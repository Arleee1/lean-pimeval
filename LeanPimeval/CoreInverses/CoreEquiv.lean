-- File: LeanPimeval/CoreInverses/CoreEquiv.lean
-- LeanPimeval - Proof of Core Location and ID Equivalence
-- Copyright (c) 2026 Ethan Ermovick
-- This file is licensed under the MIT License.
-- See the LICENSE file in the root of this repository for more details.

import Mathlib.Logic.Equiv.Defs
import LeanPimeval.CoreInverses.Defs
import LeanPimeval.CoreInverses.Proofs

/-- A single Equiv parametrized by IsBank -/
def coreEquiv (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) (IsBank : Bool)
  (h_NumCoreInNextLevel_pos : NumCoreInNextLevel > 0)
  (h_NumChipPerRank_pos : NumChipPerRank > 0)
  (h_NumBankPerRank_pos : NumBankPerRank > 0)
  (h_divides : NumBankPerRank % NumChipPerRank = 0) :
  PimCoreId ≃ { loc : PimCoreLocation // ValidLocation NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank loc } where

  toFun := fun id =>
    let loc := getCoreLocation id NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank
    ⟨loc, coreEquiv_valid_loc id NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank h_NumCoreInNextLevel_pos h_NumChipPerRank_pos h_NumBankPerRank_pos h_divides⟩

  invFun := fun ⟨loc, _⟩ =>
    getCoreId loc NumCoreInNextLevel NumBankPerRank NumChipPerRank

  left_inv := fun id =>
    coreEquiv_left_inv id NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank h_divides

  right_inv := fun ⟨loc, h_valid⟩ =>
    Subtype.ext (coreEquiv_right_inv NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank loc h_valid h_NumCoreInNextLevel_pos h_NumChipPerRank_pos h_divides)
