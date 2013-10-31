/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "MacroAssembler-mips.h"
#include "jit/MoveEmitter.h"
#include "jit/IonFrames.h"

#include "jsscriptinlines.h"

using namespace js;
using namespace js::jit;

void
MacroAssemblerMIPS::loadConstantDouble(double d, const FloatRegister &dest)
{
    union DoublePun {
        uint64_t u;
        double d;
    } dpun;
    dpun.d = d;
    if (maybeInlineDouble(dpun.u, dest))
        return;

    if (!doubleMap_.initialized()) {
        enoughMemory_ &= doubleMap_.init();
        if (!enoughMemory_)
            return;
    }
    size_t doubleIndex;
    DoubleMap::AddPtr p = doubleMap_.lookupForAdd(d);
    if (p) {
        doubleIndex = p->value;
    } else {
        doubleIndex = doubles_.length();
        enoughMemory_ &= doubles_.append(Double(d));
        enoughMemory_ &= doubleMap_.add(p, d, doubleIndex);
        if (!enoughMemory_)
            return;
    }
    Double &dbl = doubles_[doubleIndex];
    //This is different with x86! 
    mcss.loadDouble(reinterpret_cast<void *>(dbl.uses.prev()), dest.code());
    dbl.uses.setPrev(masm.size());
}

void
MacroAssemblerMIPS::finish()
{
    if (doubles_.empty())
        return;

    masm.align(sizeof(double));
    for (size_t i = 0; i < doubles_.length(); i++) {
        CodeLabel cl(doubles_[i].uses);
        writeDoubleConstant(doubles_[i].value, cl.src());
        enoughMemory_ &= addCodeLabel(cl);
        if (!enoughMemory_)
            return;
    }
}

void
MacroAssemblerMIPS::setupABICall(uint32_t args)
{
    JS_ASSERT(!inCall_);
    inCall_ = true;

    args_ = args;
    passedArgs_ = 0;
    //This is different with x86! 
    stackForCall_ = 16;
//    subl(Imm32(16), sp);
}

void
MacroAssemblerMIPS::setupAlignedABICall(uint32_t args)
{
    setupABICall(args);
    dynamicAlignment_ = false;
}

void
MacroAssemblerMIPS::setupUnalignedABICall(uint32_t args, const Register &scratch)
{
    setupABICall(args);
    dynamicAlignment_ = true;

    movl(sp, scratch);
    andl(Imm32(~(StackAlignment - 1)), sp);
    push(scratch);
}

    //This is different with x86! 
void
MacroAssemblerMIPS::passABIArg(const MoveOperand &from)
{
    MoveOperand to;

    ++passedArgs_; 

    if(passedArgs_ <= 4){ 
        Register destReg;
        FloatRegister destFloatReg;
    
        if (from.isDouble() && GetArgFloatReg(passedArgs_, &destFloatReg)) {
            to = MoveOperand(destFloatReg);
            enoughMemory_ &= moveResolver_.addMove(from, to, Move::DOUBLE);
        }else {
            GetArgReg(passedArgs_, &destReg); 
            to = MoveOperand(destReg);
            enoughMemory_ &= moveResolver_.addMove(from, to, Move::GENERAL);
        }
    }else{
#if 1
        to = MoveOperand(StackPointer, stackForCall_);
        if (from.isDouble()) {
            stackForCall_ += sizeof(double);
            enoughMemory_ &= moveResolver_.addMove(from, to, Move::DOUBLE);
        } else {
            stackForCall_ += sizeof(int32_t);
            enoughMemory_ &= moveResolver_.addMove(from, to, Move::GENERAL);
        }
#endif
    }
}

void
MacroAssemblerMIPS::passABIArg(const Register &reg)
{
    passABIArg(MoveOperand(reg));
}

void
MacroAssemblerMIPS::passABIArg(const FloatRegister &reg)
{
    passABIArg(MoveOperand(reg));
}

void
MacroAssemblerMIPS::callWithABIPre(uint32_t *stackAdjust)
{
    JS_ASSERT(inCall_);
    JS_ASSERT(args_ == passedArgs_);

    if (dynamicAlignment_) {
        *stackAdjust = stackForCall_
                     + ComputeByteAlignment(stackForCall_ + STACK_SLOT_SIZE,
                                            StackAlignment);
    } else {
        *stackAdjust = stackForCall_
                     + ComputeByteAlignment(stackForCall_ + framePushed_,
                                            StackAlignment);
    }

    reserveStack(*stackAdjust);

    // Position all arguments.
    {
        enoughMemory_ &= moveResolver_.resolve();
        if (!enoughMemory_)
            return;

        MoveEmitter emitter(*this);
        emitter.emit(moveResolver_);
        emitter.finish();
    }

#ifdef DEBUG
    {
        // Check call alignment.
        Label good;
        /* by wangqing esp-->sp */
        testl(sp, Imm32(StackAlignment - 1));
        j(Equal, &good);
        breakpoint();
        bind(&good);
    }
#endif
}
void
MacroAssemblerMIPS::callWithABIPost(uint32_t stackAdjust, Result result)
{
    freeStack(stackAdjust);
    if (result == DOUBLE) {
        reserveStack(sizeof(double));
        fstp(Operand(sp, 0));
        movsd(Operand(sp, 0), ReturnFloatReg);
        freeStack(sizeof(double));
    }
    if (dynamicAlignment_)
        pop(sp);

    JS_ASSERT(inCall_);
    inCall_ = false;
}

//This is different with x86! 
void
MacroAssemblerMIPS::callWithABI(void *fun, Result result)
{
    uint32_t stackAdjust;
    callWithABIPre(&stackAdjust);
    call(ImmWord(fun));

    pop(ra);//fixme 1031 hwj should delete

    callWithABIPost(stackAdjust, result);
}
void
MacroAssemblerMIPS::callWithABI(const Address &fun, Result result)
{
    uint32_t stackAdjust;
    callWithABIPre(&stackAdjust);
    call(Operand(fun));
    pop(ra);
    callWithABIPost(stackAdjust, result);
}

void
MacroAssemblerMIPS::handleFailureWithHandler(void *handler)
{
    // Reserve space for exception information.
    subl(Imm32(sizeof(ResumeFromException)), sp);
    movl(sp, t6);

    // Ask for an exception handler.
    setupUnalignedABICall(1, t8);
    passABIArg(t6);
    callWithABI(handler);

    Label entryFrame;
    Label catch_;
    Label finally;
    Label return_;

    loadPtr(Address(sp, offsetof(ResumeFromException, kind)), t6);
    branch32(Assembler::Equal, t6, Imm32(ResumeFromException::RESUME_ENTRY_FRAME), &entryFrame);
    branch32(Assembler::Equal, t6, Imm32(ResumeFromException::RESUME_CATCH), &catch_);
    branch32(Assembler::Equal, t6, Imm32(ResumeFromException::RESUME_FINALLY), &finally);
    branch32(Assembler::Equal, t6, Imm32(ResumeFromException::RESUME_FORCED_RETURN), &return_);

    breakpoint(); // Invalid kind.

    // No exception handler. Load the error value, load the new stack pointer
    // and return from the entry frame.
    bind(&entryFrame);
    moveValue(MagicValue(JS_ION_ERROR), JSReturnOperand);
    movl(Operand(sp, offsetof(ResumeFromException, stackPointer)), sp);
    ret();

    // If we found a catch handler, this must be a baseline frame. Restore state
    // and jump to the catch block.
    bind(&catch_);
    movl(Operand(sp, offsetof(ResumeFromException, target)), t6);
    movl(Operand(sp, offsetof(ResumeFromException, framePointer)), fp);
    movl(Operand(sp, offsetof(ResumeFromException, stackPointer)), sp);
    jmp(Operand(t6));

    // If we found a finally block, this must be a baseline frame. Push
    // two values expected by JSOP_RETSUB: BooleanValue(true) and the
    // exception.
    bind(&finally);
    ValueOperand exception = ValueOperand(t7, t8);
    loadValue(Operand(sp, offsetof(ResumeFromException, exception)), exception);

    movl(Operand(sp, offsetof(ResumeFromException, target)), t6);
    movl(Operand(sp, offsetof(ResumeFromException, framePointer)), fp);
    movl(Operand(sp, offsetof(ResumeFromException, stackPointer)), sp);

    pushValue(BooleanValue(true));
    pushValue(exception);
    jmp(Operand(t6));

    // Only used in debug mode. Return BaselineFrame->returnValue() to the caller.
    bind(&return_);
    movl(Operand(sp, offsetof(ResumeFromException, framePointer)), fp);
    movl(Operand(sp, offsetof(ResumeFromException, stackPointer)), sp);
    loadValue(Address(fp, BaselineFrame::reverseOffsetOfReturnValue()), JSReturnOperand);
    movl(fp, sp);
    pop(fp);
    ret();
}

void
MacroAssemblerMIPS::branchTestValue(Condition cond, const ValueOperand &value, const Value &v, Label *label)
{
    jsval_layout jv = JSVAL_TO_IMPL(v);
    if (v.isMarkable())
        cmpl(value.payloadReg(), ImmGCPtr(reinterpret_cast<gc::Cell *>(v.toGCThing())));
    else
        cmpl(value.payloadReg(), Imm32(jv.s.payload.i32));

    if (cond == Equal) {
        Label done;
        j(NotEqual, &done);
        {
            cmpl(value.typeReg(), Imm32(jv.s.tag));
            j(Equal, label);
        }
        bind(&done);
    } else {
        JS_ASSERT(cond == NotEqual);
        j(NotEqual, label);

        cmpl(value.typeReg(), Imm32(jv.s.tag));
        j(NotEqual, label);
    }
}

Assembler::Condition
MacroAssemblerMIPS::testNegativeZero(const FloatRegister &reg, const Register &scratch)
{
    // Determines whether the single double contained in the XMM register reg
    // is equal to double-precision -0.

    Label nonZero;

    // Compare to zero. Lets through {0, -0}.
    xorpd(ScratchFloatReg, ScratchFloatReg);
    // If reg is non-zero, then a test of Zero is false.
    branchDouble(DoubleNotEqual, reg, ScratchFloatReg, &nonZero);

    // Input register is either zero or negative zero. Test sign bit.
    movmskpd(reg, scratch);
    // If reg is -0, then a test of Zero is true.
    cmpl(scratch, Imm32(1));

    bind(&nonZero);
    return Zero;
}
