-- File: LeanPimeval/PimevalAPI/Main.lean
-- LeanPimeval - Contract for the Pimeval API
-- Copyright (c) 2026 Ethan Ermovick, William Bradford
-- This file is licensed under the MIT License.
-- See the LICENSE file in the root of this repository for more details.

structure PimObj (α : Type) (n : Nat) where
  elems : Vector α n

-- defines a higher order function which assumes map-based iterative
-- function application for each PIM kernel.
def PIM.Map2
    {α : Type} (f : α -> α -> α)
    {n : Nat} :
    let PO := PimObj α n
    PO -> PO -> PO :=
  fun (src1 src2 : PimObj α n) =>
    let elems := src1.elems.zipWith f src2.elems
    PimObj.mk elems

def PIM.Fold
    {α : Type} (acc : α -> α -> α)
    {n : Nat} :
    α -> PimObj α n -> α :=
  fun (init : α) =>
    fun (src : PimObj α n) =>
      Vector.foldl (acc) (init) src.elems

def pimAdd
    {α : Type} [Add α]
    {n : Nat}
    (src1 src2 : PimObj α n) : PimObj α n :=
  PIM.Map2 (· + ·) src1 src2

def pimSub
    {α : Type} [Sub α]
    {n : Nat}
    (src1 src2 : PimObj (α := α) n) : PimObj (α := α) n :=
  let elems := src1.elems.zipWith (· - ·) src2.elems
  PimObj.mk elems

def pimRedSum
    {α : Type} [Zero α] [Add α]
    {n : Nat} :
    PimObj α n -> α :=
  fun (src : PimObj α n) =>
    PIM.Fold (fun a b => a + b) 0 src

def pimRedSub
    {α : Type} [Zero α] [Sub α]
    {n : Nat} :
    PimObj α n -> α :=
  fun (src : PimObj α n) =>
    PIM.Fold (fun a b => a - b) 0 src

def pimMul
    {α : Type} [Mul α]
    {n : Nat} :
    PimObj α n -> PimObj α n -> PimObj α n :=
  fun (src1 src2 : PimObj α n) =>
    PIM.Map2 (fun a b => a * b) src1 src2

def pimMAC
    {α : Type} [Mul α] [Zero α] [Add α]
    {n : Nat} :
    PimObj α n -> PimObj α n -> α :=
  fun (src1 src2 : PimObj α n) =>
    pimRedSum (pimMul src1 src2)

instance : Add String where
  add := String.append

#eval pimAdd (PimObj.mk ⟨#["d", "d", "d"], rfl⟩) (PimObj.mk ⟨#["d", "d", "d"], rfl⟩)
#eval pimSub (PimObj.mk ⟨#[10, 7, 13], rfl⟩) (PimObj.mk ⟨#[4, 5, 6], rfl⟩)
#eval pimRedSum (PimObj.mk ⟨#[10, 7, 13], rfl⟩)
#eval pimRedSub (PimObj.mk ⟨(#[10, 7, 13] : Array Int), rfl⟩)
#eval pimMul (PimObj.mk ⟨(#[10, 7, 13] : Array Int), rfl⟩) (PimObj.mk ⟨#[4, 5, 6], rfl⟩)
#eval pimMAC (PimObj.mk ⟨(#[10, 7, 13] : Array Int), rfl⟩) (PimObj.mk ⟨#[4, 5, 6], rfl⟩)
