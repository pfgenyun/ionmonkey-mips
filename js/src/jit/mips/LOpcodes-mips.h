/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef jit_mips_opcodes_mips_h__
#define jit_mips_opcodes_mips_h__

#define LIR_CPU_OPCODE_LIST(_)  \
    _(Unbox)                    \
    _(UnboxDouble)              \
    _(Box)                      \
    _(BoxDouble)                \
    _(DivI)                     \
    _(ModI)                     \
    _(ModPowTwoI)               \
    _(PowHalfD)                 \
    _(UInt32ToDouble)           \
    _(AsmJSLoadFuncPtr)         \
    _(AsmJSDivOrMod)		\
   _(DivPowTwoI) 

#endif // jit_mips_opcodes_mips_h__


