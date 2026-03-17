-- File: LeanPimeval/CoreInverses/Defs.lean
-- LeanPimeval - Definitions of Core Location and ID
-- Copyright (c) 2026 Ethan Ermovick
-- This file is licensed under the MIT License.
-- See the LICENSE file in the root of this repository for more details.

structure BankCoreLocation where
  bankCoreIdx : Nat

structure SubarrayCoreLocation where
  bank : Nat
  subarrayCoreIdx : Nat

structure PimCoreLocation where
  rank : Nat
  chip : Nat
  loc : SubarrayCoreLocation ⊕ BankCoreLocation

structure PimCoreId where
  id : Nat

def getCoreLocation_Bank (CoreId : PimCoreId) (NumCoreInNextLevel NumChipPerRank : Nat) : PimCoreLocation :=
  let id := CoreId.id
  let coresPerChip := NumCoreInNextLevel
  let coresPerRank := coresPerChip * NumChipPerRank
  let rank := id / coresPerRank
  let rem1 := id % coresPerRank
  let chip := rem1 / coresPerChip
  let rem2 := rem1 % coresPerChip
  let bankCoreIdx := rem2
  PimCoreLocation.mk rank chip (Sum.inr (BankCoreLocation.mk bankCoreIdx))

def getCoreLocation_Subarray (CoreId : PimCoreId) (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) : PimCoreLocation :=
  let id := CoreId.id
  let coresPerBank := NumCoreInNextLevel
  let coresPerChip := coresPerBank * (NumBankPerRank / NumChipPerRank)
  let coresPerRank := coresPerChip * NumChipPerRank
  let rank := id / coresPerRank
  let rem1 := id % coresPerRank
  let chip := rem1 / coresPerChip
  let rem2 := rem1 % coresPerChip
  let bank := rem2 / coresPerBank
  let rem3 := rem2 % coresPerBank
  let subarrayCoreIdx := rem3
  PimCoreLocation.mk rank chip (Sum.inl (SubarrayCoreLocation.mk bank subarrayCoreIdx))

def getCoreLocation (CoreId : PimCoreId) (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) (IsBank : Bool) : PimCoreLocation :=
  if IsBank then
    getCoreLocation_Bank CoreId NumCoreInNextLevel NumChipPerRank
  else
    getCoreLocation_Subarray CoreId NumCoreInNextLevel NumBankPerRank NumChipPerRank

def getCoreId_Bank (rank chip bankCoreIdx NumCoreInNextLevel NumChipPerRank : Nat) : Nat :=
  let coresPerRank := NumChipPerRank * NumCoreInNextLevel
  rank * coresPerRank + chip * NumCoreInNextLevel + bankCoreIdx

def getCoreId_Subarray (rank chip bank subarrayCoreIdx NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) : Nat :=
  let numCorePerRank := NumBankPerRank * NumCoreInNextLevel
  let numCorePerChip := NumCoreInNextLevel * (NumBankPerRank / NumChipPerRank)
  let numCorePerBank := NumCoreInNextLevel
  rank * numCorePerRank + chip * numCorePerChip + bank * numCorePerBank + subarrayCoreIdx

def getCoreId (loc : PimCoreLocation) (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) : PimCoreId :=
  match loc.loc with
  | Sum.inl sub => PimCoreId.mk (getCoreId_Subarray loc.rank loc.chip sub.bank sub.subarrayCoreIdx NumCoreInNextLevel NumBankPerRank NumChipPerRank)
  | Sum.inr bn => PimCoreId.mk (getCoreId_Bank loc.rank loc.chip bn.bankCoreIdx NumCoreInNextLevel NumChipPerRank)

/-- A location validity predicate that depends on IsBank -/
def ValidLocation (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) (IsBank : Bool) (loc : PimCoreLocation) : Prop :=
  if IsBank then
    loc.chip < NumChipPerRank ∧ ∃ b, loc.loc = Sum.inr b ∧ b.bankCoreIdx < NumCoreInNextLevel
  else
    loc.chip < NumChipPerRank ∧ ∃ s, loc.loc = Sum.inl s ∧ s.bank < NumBankPerRank / NumChipPerRank ∧ s.subarrayCoreIdx < NumCoreInNextLevel
