-- File: LeanPimeval/PimevalAPI/Main.lean
-- LeanPimeval - Contract for the Pimeval API
-- Copyright (c) 2026 Ethan Ermovick
-- This file is licensed under the MIT License.
-- See the LICENSE file in the root of this repository for more details.

variable {α : Type} [Add α] [Sub α]

structure PimObj (n : Nat) where
  elems : Vector α n

def pimAdd {n} (src1 src2 : PimObj (α := α) n) : PimObj (α := α) n :=
  let elems := src1.elems.zipWith (· + ·) src2.elems
  PimObj.mk elems

def pimSub {n} (src1 src2 : PimObj (α := α) n) : PimObj (α := α) n :=
  let elems := src1.elems.zipWith (· - ·) src2.elems
  PimObj.mk elems

instance : Add String where
  add := String.append

#eval pimAdd (PimObj.mk ⟨#["d", "d", "d"], rfl⟩) (PimObj.mk ⟨#["d", "d", "d"], rfl⟩)
#eval pimSub (PimObj.mk ⟨#[10, 7, 13], rfl⟩) (PimObj.mk ⟨#[4, 5, 6], rfl⟩)
