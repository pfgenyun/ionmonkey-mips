/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "jit/BaselineJIT.h"
#include "jit/BaselineIC.h"
#include "jit/BaselineCompiler.h"
#include "jit/BaselineHelpers.h"
#include "jit/IonLinker.h"

using namespace js;
using namespace js::jit;

namespace js {
namespace jit {

bool
ICCompare_Double::Compiler::generateStubCode(MacroAssembler &masm)
{
    Label failure, notNaN;
    masm.ensureDouble(R0, FloatReg0, &failure);
    masm.ensureDouble(R1, FloatReg1, &failure);

    Register dest = R0.scratchReg();

    Label done;
    //first check NaN
    Assembler::DoubleCondition cond = JSOpToDoubleCondition(op);
    Assembler::NaNCond nanCond = Assembler::NaNCondFromDoubleCondition(cond);
    if (nanCond != Assembler::NaN_HandledByCond) {
      masm.mov(Imm32(nanCond == Assembler::NaN_IsTrue), dest);
      masm.branchDouble(Assembler::DoubleUnordered, FloatReg0, FloatReg1, &done);
    }

    //then check True or False
    /*
     * dest store result, default set it to true
     * weizhenwei, 2013.11.04
     */
    masm.addiu(dest, zero, 1);
    masm.branchDouble(cond, FloatReg0, FloatReg1, &done);
    //else false, then set dest to 0;
    masm.xorl(dest, dest);

    masm.bind(&done);

    masm.tagValue(JSVAL_TYPE_BOOLEAN, dest, R0);
    EmitReturnFromIC(masm);

    // Failure case - jump to next stub
    masm.bind(&failure);
    EmitStubGuardFailure(masm);
    return true;
}

// ICCompare_Int32
bool
ICCompare_Int32::Compiler::generateStubCode(MacroAssembler &masm)
{
    // Guard that R0 is an integer and R1 is an integer.
    Label failure;
    masm.branchTestInt32(Assembler::NotEqual, R0, &failure);
    masm.branchTestInt32(Assembler::NotEqual, R1, &failure);

    // Compare payload regs of R0 and R1.
    Assembler::Condition cond = JSOpToCondition(op, /* signed = */true);
    masm.cmpl(R0.payloadReg(), R1.payloadReg());
    masm.setCC(cond, R0.payloadReg());
    masm.movzxbl(R0.payloadReg(), R0.payloadReg());

    // Box the result and return
    masm.tagValue(JSVAL_TYPE_BOOLEAN, R0.payloadReg(), R0);
    EmitReturnFromIC(masm);

    // Failure case - jump to next stub
    masm.bind(&failure);
    EmitStubGuardFailure(masm);
    return true;
}

// ICBinaryArith_Int32

bool
ICBinaryArith_Int32::Compiler::generateStubCode(MacroAssembler &masm)
{
    // Guard that R0 is an integer and R1 is an integer.
    Label failure;
    masm.branchTestInt32(Assembler::NotEqual, R0, &failure);
    masm.branchTestInt32(Assembler::NotEqual, R1, &failure);

    // Add R0 and R1.  Don't need to explicitly unbox, just use the TailCallReg which
    // should be available.
    Register scratchReg = BaselineTailCallReg;

    Label revertRegister, maybeNegZero;
//xsb:fix me
//#if 0
//fixed by weizhenwei, 2013.11.05
    switch(op_) {
      case JSOP_ADD:
        // Add R0 and R1.  Don't need to explicitly unbox.
      
        //mov tow oprand to cmp registers to prepared for Overflow check.
        masm.cmpl(R0.payloadReg(), R1.payloadReg());
        masm.negl(cmpTemp2Register);

        //do the add
        masm.movl(R0.payloadReg(), scratchReg);
        masm.addl(R1.payloadReg(), scratchReg);


        // Just jump to failure on overflow.  R0 and R1 are preserved, so we can just jump to
        // the next stub.
        masm.j(Assembler::Overflow, &failure);

        // Just overwrite the payload, the tag is still fine.
        masm.movl(scratchReg, R0.payloadReg());
        break;
      case JSOP_SUB:
        masm.cmpl(R0.payloadReg(), R1.payloadReg());

        masm.movl(R0.payloadReg(), scratchReg);
        masm.subl(R1.payloadReg(), scratchReg);
        masm.j(Assembler::Overflow, &failure);
        masm.movl(scratchReg, R0.payloadReg());
        break;
      case JSOP_MUL:
        masm.movl(R0.payloadReg(), scratchReg);
        masm.imull(R1.payloadReg(), scratchReg);

        //original overflow check, removed by weizhenwei, 2013.11.01
        //masm.j(Assembler::Overflow, &failure);

        //test whether signed multiply overflow. by weizhenwei, 2013.11.01
        masm.mfhi(cmpTempRegister);
        masm.mflo(cmpTemp2Register);
        masm.sarl(Imm32(0x1f), cmpTemp2Register);
        masm.j(Assembler::NotEqual, &failure);

        masm.testl(scratchReg, scratchReg);
        masm.j(Assembler::Zero, &maybeNegZero);

        masm.movl(scratchReg, R0.payloadReg());
        break;
      case JSOP_DIV:
        // Prevent division by 0.
        masm.branchTest32(Assembler::Zero, R1.payloadReg(), R1.payloadReg(), &failure);

        // Prevent negative 0 and -2147483648 / -1.
        masm.branchTest32(Assembler::Zero, R0.payloadReg(), Imm32(0x7fffffff), &failure);

        // For idiv we need eax.
//        JS_ASSERT(R1.typeReg() == eax);
//        masm.movl(R0.payloadReg(), eax);
        // by weizhenwei, 2013.10.28, in mips, eax = t6 
        // see jit/mips/CodeGenerator-mips.cpp:visitDivI();
        JS_ASSERT(R1.typeReg() == s1);
        masm.movl(R0.payloadReg(), t6);

        // Preserve R0.payloadReg()/edx, eax is JSVAL_TYPE_INT32.
        masm.movl(R0.payloadReg(), scratchReg);
        // Sign extend eax into edx to make (edx:eax), since idiv is 64-bit.
        masm.cdq();
        masm.idiv(R1.payloadReg());

        // A remainder implies a double result.
        //masm.branchTest32(Assembler::NonZero, edx, edx, &revertRegister);
        //by weizhenwei, 2013.11.02
        masm.mfhi(cmpTempRegister);
        masm.movl(zero, cmpTemp2Register);
        masm.j(Assembler::NotEqual, &revertRegister);

        //masm.movl(eax, R0.payloadReg());
        //by weizhenwei, 2013.11.05
        //masm.movl(t6, R0.payloadReg());
        masm.mflo(R0.payloadReg());
        break;
      case JSOP_MOD:
      {
        // x % 0 always results in NaN.
        masm.branchTest32(Assembler::Zero, R1.payloadReg(), R1.payloadReg(), &failure);

        // Prevent negative 0 and -2147483648 % -1.
        masm.branchTest32(Assembler::Zero, R0.payloadReg(), Imm32(0x7fffffff), &failure);

        // For idiv we need eax.
//        JS_ASSERT(R1.typeReg() == eax);
//        masm.movl(R0.payloadReg(), eax);
        // by weizhenwei, 2013.10.25, in mips, eax = t6, edx = t7, ecx = t8;
        // see jit/mips/CodeGenerator-mips.cpp:visitDivI();
        JS_ASSERT(R1.typeReg() == s1);
        masm.movl(R0.payloadReg(), t6);

        // Preserve R0.payloadReg()/edx, eax is JSVAL_TYPE_INT32.
        masm.movl(R0.payloadReg(), scratchReg);
        // Sign extend eax into edx to make (edx:eax), since idiv is 64-bit.
        masm.cdq();
        masm.idiv(R1.payloadReg());

        // Fail when we would need a negative remainder.
        Label done;
        //masm.branchTest32(Assembler::NonZero, edx, edx, &done);
        masm.mfhi(cmpTempRegister);
        masm.movl(zero, cmpTemp2Register);
        masm.j(Assembler::NotEqual, &done);

        masm.branchTest32(Assembler::Signed, scratchReg, scratchReg, &revertRegister);
        masm.branchTest32(Assembler::Signed, R1.payloadReg(), R1.payloadReg(), &revertRegister);


        masm.bind(&done);
        // Result is in edx, tag in ecx remains untouched.
//        JS_ASSERT(R0.payloadReg() == edx);
//        JS_ASSERT(R0.typeReg() == ecx);
//        by weizhenwei, 201..10.25
        JS_ASSERT(R0.typeReg() == t7);
        JS_ASSERT(R0.payloadReg() == t8);

        //move reminder to R0.payloadReg, by weizhenwei, 2013.11.05
        masm.mfhi(R0.payloadReg());
        break;
      }
      case JSOP_BITOR:
        // We can overide R0, because the instruction is unfailable.
        // The R0.typeReg() is also still intact.
        masm.orl(R1.payloadReg(), R0.payloadReg());
        break;
      case JSOP_BITXOR:
        masm.xorl(R1.payloadReg(), R0.payloadReg());
        break;
      case JSOP_BITAND:
        masm.andl(R1.payloadReg(), R0.payloadReg());
        break;
      case JSOP_LSH:
        // RHS needs to be in ecx for shift operations.
//        JS_ASSERT(R0.typeReg() == ecx);
//        masm.movl(R1.payloadReg(), ecx);
//        by weizhenwei, 2013.10.25, in mips, ecx = t8
        JS_ASSERT(R0.typeReg() == t8);
        masm.movl(R0.typeReg(), scratchReg); //by weizhenwei, 2013.11.05
        masm.movl(R1.payloadReg(), t8);
        masm.shll_cl(R0.payloadReg());
        masm.movl(scratchReg, R0.typeReg()); //by weizhenwei, 2013.11.05
        // We need to tag again, because we overwrote it.
        masm.tagValue(JSVAL_TYPE_INT32, R0.payloadReg(), R0);
        break;
      case JSOP_RSH:
//        masm.movl(R1.payloadReg(), ecx);
//        by weizhenwei, 2013.10.25, in mips, ecx = t8
        JS_ASSERT(R0.typeReg() == t8);
        masm.movl(R0.typeReg(), scratchReg); //by weizhenwei, 2013.11.05
        masm.movl(R1.payloadReg(), t8);
        masm.sarl_cl(R0.payloadReg());
        masm.movl(scratchReg, R0.typeReg()); //by weizhenwei, 2013.11.05
        masm.tagValue(JSVAL_TYPE_INT32, R0.payloadReg(), R0);
        break;
      case JSOP_URSH:
        if (!allowDouble_)
            masm.movl(R0.payloadReg(), scratchReg);

//        masm.movl(R1.payloadReg(), ecx);
//        by weizhenwei, 2013.10.25, in mips, ecx = t8
        JS_ASSERT(R0.typeReg() == t8);
        masm.movl(R0.typeReg(), scratchReg); //by weizhenwei, 2013.11.05
        masm.movl(R1.payloadReg(), t8);
        masm.shrl_cl(R0.payloadReg());
        masm.movl(scratchReg, R0.typeReg()); //by weizhenwei, 2013.11.05
        masm.testl(R0.payloadReg(), R0.payloadReg());
        if (allowDouble_) {
            Label toUint;
            masm.j(Assembler::Signed, &toUint);

            // Box and return.
            masm.tagValue(JSVAL_TYPE_INT32, R0.payloadReg(), R0);
            EmitReturnFromIC(masm);

            masm.bind(&toUint);
            masm.convertUInt32ToDouble(R0.payloadReg(), ScratchFloatReg);
            masm.boxDouble(ScratchFloatReg, R0);
        } else {
            masm.j(Assembler::Signed, &revertRegister);
            masm.tagValue(JSVAL_TYPE_INT32, R0.payloadReg(), R0);
        }
        break;
      default:
       JS_NOT_REACHED("Unhandled op for BinaryArith_Int32.  ");
       return false;
    }
//#endif

    // Return.
    EmitReturnFromIC(masm);

    switch(op_) {
      case JSOP_MUL:
        masm.bind(&maybeNegZero);

        // Result is -0 if exactly one of lhs or rhs is negative.
        masm.movl(R0.payloadReg(), scratchReg);
        masm.orl(R1.payloadReg(), scratchReg);
        //add by QuQiuwen;
        masm.cmpl(scratchReg,zero);
        masm.j(Assembler::Signed, &failure);

        // Result is +0.
        masm.xorl(R0.payloadReg(), R0.payloadReg());
        EmitReturnFromIC(masm);
        break;
      case JSOP_DIV:
      case JSOP_MOD:
        masm.bind(&revertRegister);
        masm.movl(scratchReg, R0.payloadReg());
        masm.movl(ImmType(JSVAL_TYPE_INT32), R1.typeReg());
        break;
      case JSOP_URSH:
        // Revert the content of R0 in the fallible >>> case.
        if (!allowDouble_) {
            masm.bind(&revertRegister);
            masm.tagValue(JSVAL_TYPE_INT32, scratchReg, R0);
        }
        break;
      default:
        // No special failure handling required.
        // Fall through to failure.
        break;
    }

    // Failure case - jump to next stub
    masm.bind(&failure);
    EmitStubGuardFailure(masm);

    return true;
}

bool
ICUnaryArith_Int32::Compiler::generateStubCode(MacroAssembler &masm)
{
    Label failure;
    masm.branchTestInt32(Assembler::NotEqual, R0, &failure);

    switch (op) {
      case JSOP_BITNOT:
        masm.notl(R0.payloadReg());
        break;
      case JSOP_NEG:
        // Guard against 0 and MIN_INT, both result in a double.
        masm.branchTest32(Assembler::Zero, R0.payloadReg(), Imm32(0x7fffffff), &failure);
        masm.negl(R0.payloadReg());
        break;
      default:
        JS_NOT_REACHED("Unexpected op");
        return false;
    }

    EmitReturnFromIC(masm);

    masm.bind(&failure);
    EmitStubGuardFailure(masm);
    return true;
}

} // namespace jit
} // namespace js
