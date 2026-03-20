-- File: LeanPimeval/CoreInverses/CoreEquiv.lean
-- LeanPimeval - Proof of Core Location and ID Equivalence
-- Copyright (c) 2026 Ethan Ermovick
-- This file is licensed under the MIT License.
-- See the LICENSE file in the root of this repository for more details.

import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.PNat.Basic
import LeanPimeval.CoreInverses.Defs
import LeanPimeval.CoreInverses.Proofs

/-- A single Equiv parametrized by IsBank -/
def coreEquiv (NumCoreInNextLevel NumBankPerRank NumChipPerRank : ℕ+) (IsBank : Bool)
    (h_divides : NumBankPerRank.val % NumChipPerRank.val = 0) :
    PimCoreId ≃ { loc : PimCoreLocation // ValidLocation NumCoreInNextLevel.val NumBankPerRank.val NumChipPerRank.val IsBank loc } where

  toFun := fun id =>
    let loc := getCoreLocation id NumCoreInNextLevel.val NumBankPerRank.val NumChipPerRank.val IsBank
    ⟨loc, coreEquiv_valid_loc id NumCoreInNextLevel.val NumBankPerRank.val NumChipPerRank.val IsBank NumCoreInNextLevel.2 NumChipPerRank.2 NumBankPerRank.2 h_divides⟩

  invFun := fun ⟨loc, _⟩ =>
    getCoreId loc NumCoreInNextLevel.val NumBankPerRank.val NumChipPerRank.val

  left_inv := fun id =>
    coreEquiv_left_inv id NumCoreInNextLevel.val NumBankPerRank.val NumChipPerRank.val IsBank h_divides

  right_inv := fun ⟨loc, h_valid⟩ =>
    Subtype.ext (coreEquiv_right_inv NumCoreInNextLevel.val NumBankPerRank.val NumChipPerRank.val IsBank loc h_valid NumCoreInNextLevel.2 NumChipPerRank.2 h_divides)
