-- File: LeanPimeval/PimevalAPI/Main.lean
-- LeanPimeval - Contract for the Pimeval API
-- Copyright (c) 2026 Ethan Ermovick
-- This file is licensed under the MIT License.
-- See the LICENSE file in the root of this repository for more details.

variable {α : Type} [Add α] [Sub α]

structure PimObj (n : Nat) where
  elems : Vector α n

-- this is a comfort thing, if you want to use the
-- above notation, that also works but I wanted to
-- get a quick version out
structure PimObj' (a' : Type) (n : Nat) where
  elems : Vector a' n

-- defines a higher order function which assumes map-based iterative
-- function application for each PIM kernel.
def PIM.Map2 {a' : Type} (f : a' -> a' -> a') :
  let PO := PimObj' a' n
  PO -> PO -> PO :=
    fun (src1 src2 : PimObj' a' n) =>
      let elems := src1.elems.zipWith f src2.elems
      PimObj'.mk elems

def PIM.Fold {a' : Type} (acc : a' -> a' -> a') :
  a' -> PimObj' a' n -> a' :=
  fun (init : a') =>
    fun (src : PimObj' a' n) =>
      Vector.foldl (acc) (init) src.elems
      
def pimAdd {n} (src1 src2 : PimObj (α := α) n) : PimObj (α := α) n :=
  let elems := src1.elems.zipWith (· + ·) src2.elems
  PimObj.mk elems

def pimAdd' [Add a'] {n}
  (src1 src2 : PimObj' a' n) : PimObj' a' n
  := PIM.Map2 (· + ·) src1 src2

def pimSub {n} (src1 src2 : PimObj (α := α) n) : PimObj (α := α) n :=
  let elems := src1.elems.zipWith (· - ·) src2.elems
  PimObj.mk elems

def pimRedSum [Zero a'] [Add a'] :
  PimObj' a' n -> a' :=
  fun (src : PimObj' a' n) =>
    PIM.Fold (fun a b => a + b) 0 src

def pimRedSub [Zero a'] [Sub a'] :
  PimObj' a' n -> a' :=
  fun (src : PimObj' a' n) =>
    PIM.Fold (fun a b => a - b) 0 src

def pimMul [Mul a'] :
  PimObj' a' n -> PimObj' a' n -> PimObj' a' n :=
  fun (src1 src2 : PimObj' a' n) => PIM.Map2 (fun a b => a * b) src1 src2

def pimMAC [Mul a'] [Zero a'] [Add a'] :
  PimObj' a' n -> PimObj' a' n -> a' :=
  fun (src1 src2 : PimObj' a' n) =>
    pimRedSum (pimMul src1 src2)

instance : Add String where
  add := String.append

#eval pimAdd (PimObj.mk ⟨#["d", "d", "d"], rfl⟩) (PimObj.mk ⟨#["d", "d", "d"], rfl⟩)
#eval pimAdd' (PimObj'.mk ⟨#["d", "d", "d"], rfl⟩) (PimObj'.mk ⟨#["d", "d", "d"], rfl⟩)
#eval pimSub (PimObj.mk ⟨#[10, 7, 13], rfl⟩) (PimObj.mk ⟨#[4, 5, 6], rfl⟩)
#eval pimRedSum (PimObj'.mk ⟨#[10, 7, 13], rfl⟩)
#eval pimRedSub (PimObj'.mk ⟨(#[10, 7, 13] : Array Int), rfl⟩)
#eval pimMul (PimObj'.mk ⟨(#[10, 7, 13] : Array Int), rfl⟩) (PimObj'.mk ⟨#[4, 5, 6], rfl⟩)
#eval pimMAC (PimObj'.mk ⟨(#[10, 7, 13] : Array Int), rfl⟩) (PimObj'.mk ⟨#[4, 5, 6], rfl⟩)
