-- File: LeanPimeval/CoreInverses/Proofs.lean
-- LeanPimeval - Proof implementations for Core Location and ID Equivalence
-- Copyright (c) 2026 Ethan Ermovick
-- This file is licensed under the MIT License.
-- See the LICENSE file in the root of this repository for more details.

import LeanPimeval.CoreInverses.Defs

theorem bank_inverse (id : PimCoreId) (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) :
  getCoreId (getCoreLocation id NumCoreInNextLevel NumBankPerRank NumChipPerRank true) NumCoreInNextLevel NumBankPerRank NumChipPerRank = id := by
  cases id with
  | mk val =>
    dsimp [getCoreLocation, getCoreId, getCoreLocation_Bank, getCoreId_Bank]
    congr
    have h_comm : NumChipPerRank * NumCoreInNextLevel = NumCoreInNextLevel * NumChipPerRank := Nat.mul_comm NumChipPerRank NumCoreInNextLevel
    rw [h_comm]
    have step1 : (val % (NumCoreInNextLevel * NumChipPerRank) / NumCoreInNextLevel) * NumCoreInNextLevel + val % (NumCoreInNextLevel * NumChipPerRank) % NumCoreInNextLevel = val % (NumCoreInNextLevel * NumChipPerRank) := by
      have h := Nat.div_add_mod (val % (NumCoreInNextLevel * NumChipPerRank)) NumCoreInNextLevel
      rw [Nat.mul_comm NumCoreInNextLevel] at h
      exact h
    rw [Nat.add_assoc]
    rw [step1]
    have step2 : (val / (NumCoreInNextLevel * NumChipPerRank)) * (NumCoreInNextLevel * NumChipPerRank) + val % (NumCoreInNextLevel * NumChipPerRank) = val := by
      have h := Nat.div_add_mod val (NumCoreInNextLevel * NumChipPerRank)
      rw [Nat.mul_comm (NumCoreInNextLevel * NumChipPerRank)] at h
      exact h
    exact step2

theorem bank_inverse2 (rank chip bankCoreIdx NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat)
  (h_chip : chip < NumChipPerRank)
  (h_bank : bankCoreIdx < NumCoreInNextLevel)
  (h_NumCoreInNextLevel_pos : NumCoreInNextLevel > 0)
  (h_NumChipPerRank_pos : NumChipPerRank > 0) :
  let loc := PimCoreLocation.mk rank chip (Sum.inr (BankCoreLocation.mk bankCoreIdx))
  getCoreLocation (getCoreId loc NumCoreInNextLevel NumBankPerRank NumChipPerRank) NumCoreInNextLevel NumBankPerRank NumChipPerRank true = loc := by
  intro loc
  let n := NumCoreInNextLevel
  let c := NumChipPerRank
  let coresPerRank := n * c
  let rem := chip * n + bankCoreIdx

  have h_n_pos : 0 < n := h_NumCoreInNextLevel_pos
  have h_c_pos : 0 < c := h_NumChipPerRank_pos
  have h_coresPerRank_pos : 0 < coresPerRank := by
    dsimp [coresPerRank]
    exact Nat.mul_pos h_n_pos h_c_pos

  have h_rem_lt : rem < coresPerRank := by
    have h1 : chip * n + bankCoreIdx < chip * n + n := Nat.add_lt_add_left h_bank (chip * n)
    have h2 : chip * n + n = chip.succ * n := by
      rw [Nat.succ_mul]
    have h3 : chip.succ * n ≤ c * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h_chip)
    have h4 : c * n = coresPerRank := by
      dsimp [coresPerRank]
      rw [Nat.mul_comm]
    have h5 : rem < chip.succ * n := by
      dsimp [rem]
      simpa [h2] using h1
    exact Nat.lt_of_lt_of_le h5 (by simpa [h4] using h3)

  have h_rem_div_coresPerRank : rem / coresPerRank = 0 := Nat.div_eq_of_lt h_rem_lt
  have h_rem_mod_coresPerRank : rem % coresPerRank = rem := Nat.mod_eq_of_lt h_rem_lt

  have h_bank_div_n : bankCoreIdx / n = 0 := Nat.div_eq_of_lt h_bank
  have h_bank_mod_n : bankCoreIdx % n = bankCoreIdx := Nat.mod_eq_of_lt h_bank

  have h_chip_from_rem : rem / n = chip := by
    dsimp [rem]
    have h := Nat.add_mul_div_right bankCoreIdx chip h_n_pos
    rw [h_bank_div_n] at h
    simpa [Nat.add_comm, Nat.zero_add] using h

  have h_bank_from_rem : rem % n = bankCoreIdx := by
    calc
      rem % n = (bankCoreIdx + chip * n) % n := by
        dsimp [rem]
        rw [Nat.add_comm]
      _ = bankCoreIdx % n := Nat.add_mul_mod_self_right bankCoreIdx chip n
      _ = bankCoreIdx := h_bank_mod_n

  have h_rank_from_id : (rem + rank * coresPerRank) / coresPerRank = rank := by
    have h := Nat.add_mul_div_right rem rank h_coresPerRank_pos
    rw [h_rem_div_coresPerRank] at h
    simpa [Nat.zero_add] using h

  have h_rem_from_id : (rem + rank * coresPerRank) % coresPerRank = rem := by
    calc
      (rem + rank * coresPerRank) % coresPerRank = rem % coresPerRank :=
        Nat.add_mul_mod_self_right rem rank coresPerRank
      _ = rem := h_rem_mod_coresPerRank

  have h_id_rewrite :
      getCoreId_Bank rank chip bankCoreIdx n c = rem + rank * coresPerRank := by
    dsimp [getCoreId_Bank, rem, coresPerRank]
    rw [Nat.mul_comm c n]
    rw [Nat.add_assoc]
    rw [Nat.add_comm (rank * (n * c)) (chip * n + bankCoreIdx)]

  change getCoreLocation (PimCoreId.mk (getCoreId_Bank rank chip bankCoreIdx n c)) NumCoreInNextLevel NumBankPerRank NumChipPerRank true = loc
  rw [h_id_rewrite]
  dsimp [getCoreLocation, getCoreLocation_Bank, loc]

  have t1 : (rem + rank * coresPerRank) / (n * c) = rank := by
    simpa [coresPerRank] using h_rank_from_id
  have t2 : (rem + rank * coresPerRank) % (n * c) / n = chip := by
    calc
      (rem + rank * coresPerRank) % (n * c) / n = ((rem + rank * coresPerRank) % coresPerRank) / n := by
        rfl
      _ = rem / n := by rw [h_rem_from_id]
      _ = chip := h_chip_from_rem
  have t3 : (rem + rank * coresPerRank) % (n * c) % n = bankCoreIdx := by
    calc
      (rem + rank * coresPerRank) % (n * c) % n = ((rem + rank * coresPerRank) % coresPerRank) % n := by
        rfl
      _ = rem % n := by rw [h_rem_from_id]
      _ = bankCoreIdx := h_bank_from_rem

  rw [t1, t2, t3]

theorem subarray_inverse (id : PimCoreId) (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) (h_divides : NumBankPerRank % NumChipPerRank = 0) :
  getCoreId (getCoreLocation id NumCoreInNextLevel NumBankPerRank NumChipPerRank false) NumCoreInNextLevel NumBankPerRank NumChipPerRank = id := by
  cases id with
  | mk val =>
    dsimp [getCoreLocation, getCoreId, getCoreLocation_Subarray, getCoreId_Subarray]
    congr
    let cBank := NumCoreInNextLevel
    let cChip := NumCoreInNextLevel * (NumBankPerRank / NumChipPerRank)
    let cRank := cChip * NumChipPerRank
    have h_cRank : NumBankPerRank * NumCoreInNextLevel = cRank := by
      dsimp [cRank, cChip]
      have h1 := Nat.div_add_mod NumBankPerRank NumChipPerRank
      rw [h_divides] at h1
      rw [Nat.add_zero] at h1
      rw [Nat.mul_comm] at h1
      rw [Nat.mul_assoc]
      have comm : NumCoreInNextLevel * ((NumBankPerRank / NumChipPerRank) * NumChipPerRank) = NumCoreInNextLevel * NumBankPerRank := by rw [h1]
      rw [comm]
      exact Nat.mul_comm NumBankPerRank NumCoreInNextLevel
    rw [h_cRank]
    have step1 : (val % cRank % cChip / cBank) * cBank + (val % cRank % cChip % cBank) = val % cRank % cChip := by
      have h := Nat.div_add_mod (val % cRank % cChip) cBank
      rw [Nat.mul_comm cBank] at h
      exact h
    have add_assoc_2: (val / cRank * cRank + val % cRank / cChip * cChip + val % cRank % cChip / cBank * cBank + val % cRank % cChip % cBank) =
                      (val / cRank * cRank + val % cRank / cChip * cChip + (val % cRank % cChip / cBank * cBank + val % cRank % cChip % cBank)) := by
      rw [Nat.add_assoc (val / cRank * cRank + val % cRank / cChip * cChip)]
    rw [add_assoc_2]
    rw [step1]
    have step2 : (val % cRank / cChip) * cChip + val % cRank % cChip = val % cRank := by
      have h := Nat.div_add_mod (val % cRank) cChip
      rw [Nat.mul_comm cChip] at h
      exact h
    rw [Nat.add_assoc]
    rw [step2]
    have step3 : (val / cRank) * cRank + val % cRank = val := by
      have h := Nat.div_add_mod val cRank
      rw [Nat.mul_comm cRank] at h
      exact h
    exact step3

theorem subarray_inverse2 (rank chip bank subarrayCoreIdx NumSubarrayPerBank NumBankPerRank NumChipPerRank : Nat)
  (h_chip : chip < NumChipPerRank)
  (h_bank : bank < NumBankPerRank / NumChipPerRank)
  (h_subarray : subarrayCoreIdx < NumSubarrayPerBank)
  (h_NumSubarrayPerBank_pos : NumSubarrayPerBank > 0)
  (h_NumChipPerRank_pos : NumChipPerRank > 0)
  (h_divides : NumBankPerRank % NumChipPerRank = 0) :
  let loc := PimCoreLocation.mk rank chip (Sum.inl (SubarrayCoreLocation.mk bank subarrayCoreIdx))
  getCoreLocation (getCoreId loc NumSubarrayPerBank NumBankPerRank NumChipPerRank) NumSubarrayPerBank NumBankPerRank NumChipPerRank false = loc := by
  intro loc
  let cBank := NumSubarrayPerBank
  let bankPerChip := NumBankPerRank / NumChipPerRank
  let cChip := cBank * bankPerChip
  let cRank := cChip * NumChipPerRank
  let remBank := bank * cBank + subarrayCoreIdx
  let remRank := chip * cChip + remBank

  have h_cBank_pos : 0 < cBank := h_NumSubarrayPerBank_pos
  have h_chipPerRank_pos : 0 < NumChipPerRank := h_NumChipPerRank_pos
  have h_bankPerChip_pos : 0 < bankPerChip := Nat.lt_of_le_of_lt (Nat.zero_le bank) h_bank
  have h_cChip_pos : 0 < cChip := by
    dsimp [cChip]
    exact Nat.mul_pos h_cBank_pos h_bankPerChip_pos
  have h_cRank_pos : 0 < cRank := by
    dsimp [cRank]
    exact Nat.mul_pos h_cChip_pos h_chipPerRank_pos

  have h_remBank_lt_cChip : remBank < cChip := by
    have h1 : bank * cBank + subarrayCoreIdx < bank * cBank + cBank := Nat.add_lt_add_left h_subarray (bank * cBank)
    have h2 : bank * cBank + cBank = bank.succ * cBank := by
      rw [Nat.succ_mul]
    have h3 : bank.succ * cBank ≤ bankPerChip * cBank := Nat.mul_le_mul_right cBank (Nat.succ_le_of_lt h_bank)
    have h4 : bankPerChip * cBank = cChip := by
      dsimp [cChip]
      rw [Nat.mul_comm]
    have h5 : remBank < bank.succ * cBank := by
      dsimp [remBank]
      simpa [h2] using h1
    exact Nat.lt_of_lt_of_le h5 (by simpa [h4] using h3)

  have h_remRank_lt_cRank : remRank < cRank := by
    have h1 : chip * cChip + remBank < chip * cChip + cChip := Nat.add_lt_add_left h_remBank_lt_cChip (chip * cChip)
    have h2 : chip * cChip + cChip = chip.succ * cChip := by
      rw [Nat.succ_mul]
    have h3 : chip.succ * cChip ≤ NumChipPerRank * cChip := Nat.mul_le_mul_right cChip (Nat.succ_le_of_lt h_chip)
    have h4 : NumChipPerRank * cChip = cRank := by
      dsimp [cRank]
      rw [Nat.mul_comm]
    have h5 : remRank < chip.succ * cChip := by
      dsimp [remRank]
      simpa [h2] using h1
    exact Nat.lt_of_lt_of_le h5 (by simpa [h4] using h3)

  have h_remBank_div_cChip : remBank / cChip = 0 := Nat.div_eq_of_lt h_remBank_lt_cChip
  have h_remBank_mod_cChip : remBank % cChip = remBank := Nat.mod_eq_of_lt h_remBank_lt_cChip
  have h_remRank_div_cRank : remRank / cRank = 0 := Nat.div_eq_of_lt h_remRank_lt_cRank
  have h_remRank_mod_cRank : remRank % cRank = remRank := Nat.mod_eq_of_lt h_remRank_lt_cRank

  have h_sub_div_cBank : subarrayCoreIdx / cBank = 0 := Nat.div_eq_of_lt h_subarray
  have h_sub_mod_cBank : subarrayCoreIdx % cBank = subarrayCoreIdx := Nat.mod_eq_of_lt h_subarray

  have h_bank_from_remBank : remBank / cBank = bank := by
    dsimp [remBank]
    have h := Nat.add_mul_div_right subarrayCoreIdx bank h_cBank_pos
    rw [h_sub_div_cBank] at h
    simpa [Nat.add_comm, Nat.zero_add] using h

  have h_sub_from_remBank : remBank % cBank = subarrayCoreIdx := by
    calc
      remBank % cBank = (subarrayCoreIdx + bank * cBank) % cBank := by
        dsimp [remBank]
        rw [Nat.add_comm]
      _ = subarrayCoreIdx % cBank := Nat.add_mul_mod_self_right subarrayCoreIdx bank cBank
      _ = subarrayCoreIdx := h_sub_mod_cBank

  have h_chip_from_remRank : remRank / cChip = chip := by
    calc
      remRank / cChip = (remBank + chip * cChip) / cChip := by
        dsimp [remRank]
        rw [Nat.add_comm]
      _ = remBank / cChip + chip := Nat.add_mul_div_right remBank chip h_cChip_pos
      _ = chip := by rw [h_remBank_div_cChip, Nat.zero_add]

  have h_remBank_from_remRank : remRank % cChip = remBank := by
    calc
      remRank % cChip = (remBank + chip * cChip) % cChip := by
        dsimp [remRank]
        rw [Nat.add_comm]
      _ = remBank % cChip := Nat.add_mul_mod_self_right remBank chip cChip
      _ = remBank := h_remBank_mod_cChip

  have h_div_bankPerChip : NumChipPerRank * bankPerChip = NumBankPerRank := by
    dsimp [bankPerChip]
    have h_div := Nat.div_add_mod NumBankPerRank NumChipPerRank
    rw [h_divides, Nat.add_zero] at h_div
    exact h_div

  have h_numCorePerRank_eq_cRank : NumBankPerRank * cBank = cRank := by
    calc
      NumBankPerRank * cBank = (NumChipPerRank * bankPerChip) * cBank := by
        rw [←h_div_bankPerChip]
      _ = NumChipPerRank * (bankPerChip * cBank) := by rw [Nat.mul_assoc]
      _ = NumChipPerRank * (cBank * bankPerChip) := by rw [Nat.mul_comm bankPerChip cBank]
      _ = (cBank * bankPerChip) * NumChipPerRank := by rw [Nat.mul_comm]
      _ = cRank := by dsimp [cRank, cChip]

  have h_rank_from_id : (remRank + rank * cRank) / cRank = rank := by
    have h := Nat.add_mul_div_right remRank rank h_cRank_pos
    rw [h_remRank_div_cRank] at h
    simpa [Nat.zero_add] using h

  have h_remRank_from_id : (remRank + rank * cRank) % cRank = remRank := by
    calc
      (remRank + rank * cRank) % cRank = remRank % cRank := Nat.add_mul_mod_self_right remRank rank cRank
      _ = remRank := h_remRank_mod_cRank

  have h_id_rewrite :
      getCoreId_Subarray rank chip bank subarrayCoreIdx cBank NumBankPerRank NumChipPerRank = rank * cRank + remRank := by
    dsimp [getCoreId_Subarray, remRank, remBank, cBank, cChip]
    rw [h_numCorePerRank_eq_cRank]
    rw [Nat.add_assoc]
    rw [Nat.add_assoc]

  change getCoreLocation (PimCoreId.mk (getCoreId_Subarray rank chip bank subarrayCoreIdx cBank NumBankPerRank NumChipPerRank)) cBank NumBankPerRank NumChipPerRank false = loc
  rw [h_id_rewrite]
  dsimp [getCoreLocation, getCoreLocation_Subarray, loc, bankPerChip, cChip, cRank, remRank, remBank]

  have t1 : (rank * cRank + remRank) / cRank = rank := by
    simpa [Nat.add_comm] using h_rank_from_id
  have h_remRank_from_id' : (rank * cRank + remRank) % cRank = remRank := by
    simpa [Nat.add_comm] using h_remRank_from_id
  have t2 : (rank * cRank + remRank) % cRank / cChip = chip := by
    calc
      (rank * cRank + remRank) % cRank / cChip = remRank / cChip := by rw [h_remRank_from_id']
      _ = chip := h_chip_from_remRank
  have t3 : (rank * cRank + remRank) % cRank % cChip / cBank = bank := by
    calc
      (rank * cRank + remRank) % cRank % cChip / cBank = remBank / cBank := by
        rw [h_remRank_from_id', h_remBank_from_remRank]
      _ = bank := h_bank_from_remBank
  have t4 : (rank * cRank + remRank) % cRank % cChip % cBank = subarrayCoreIdx := by
    calc
      (rank * cRank + remRank) % cRank % cChip % cBank = remBank % cBank := by
        rw [h_remRank_from_id', h_remBank_from_remRank]
      _ = subarrayCoreIdx := h_sub_from_remBank

  rw [t1, t2, t3, t4]

theorem coreEquiv_valid_loc (id : PimCoreId) (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) (IsBank : Bool)
  (h_NumCoreInNextLevel_pos : NumCoreInNextLevel > 0)
  (h_NumChipPerRank_pos : NumChipPerRank > 0)
  (h_NumBankPerRank_pos : NumBankPerRank > 0)
  (h_divides : NumBankPerRank % NumChipPerRank = 0) :
  let loc := getCoreLocation id NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank
  ValidLocation NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank loc := by
  dsimp [ValidLocation, getCoreLocation]
  cases IsBank
  · dsimp [getCoreLocation_Subarray]
    constructor
    · have hpos : NumBankPerRank / NumChipPerRank > 0 := by
        have h1 := Nat.div_add_mod NumBankPerRank NumChipPerRank
        rw [h_divides, Nat.add_zero] at h1
        cases h2 : NumBankPerRank / NumChipPerRank
        · rw [h2] at h1
          omega
        · exact Nat.zero_lt_succ _
      have hpos2 : NumCoreInNextLevel * (NumBankPerRank / NumChipPerRank) * NumChipPerRank > 0 := by
        apply Nat.mul_pos
        · apply Nat.mul_pos h_NumCoreInNextLevel_pos hpos
        · exact h_NumChipPerRank_pos
      exact Nat.div_lt_of_lt_mul (Nat.mod_lt _ hpos2)
    · exists (SubarrayCoreLocation.mk
        (id.id % (NumCoreInNextLevel * (NumBankPerRank / NumChipPerRank) * NumChipPerRank) %
            (NumCoreInNextLevel * (NumBankPerRank / NumChipPerRank)) /
          NumCoreInNextLevel)
        (id.id % (NumCoreInNextLevel * (NumBankPerRank / NumChipPerRank) * NumChipPerRank) %
            (NumCoreInNextLevel * (NumBankPerRank / NumChipPerRank)) %
          NumCoreInNextLevel))
      refine ⟨rfl, ?_, ?_⟩
      · have hpos : NumBankPerRank / NumChipPerRank > 0 := by
          have h1 := Nat.div_add_mod NumBankPerRank NumChipPerRank
          rw [h_divides, Nat.add_zero] at h1
          cases h2 : NumBankPerRank / NumChipPerRank
          · rw [h2] at h1
            omega
          · exact Nat.zero_lt_succ _
        have hpos1 : NumCoreInNextLevel * (NumBankPerRank / NumChipPerRank) > 0 := Nat.mul_pos h_NumCoreInNextLevel_pos hpos
        have hlt1 := Nat.mod_lt
          (id.id % (NumCoreInNextLevel * (NumBankPerRank / NumChipPerRank) * NumChipPerRank)) hpos1
        have hlt2 := Nat.div_lt_of_lt_mul hlt1
        exact hlt2
      · exact Nat.mod_lt _ h_NumCoreInNextLevel_pos
  · dsimp [getCoreLocation_Bank]
    constructor
    · have hpos : NumCoreInNextLevel * NumChipPerRank > 0 := Nat.mul_pos h_NumCoreInNextLevel_pos h_NumChipPerRank_pos
      have hlt : id.id % (NumCoreInNextLevel * NumChipPerRank) < (NumCoreInNextLevel * NumChipPerRank) := Nat.mod_lt _ hpos
      exact Nat.div_lt_of_lt_mul hlt
    · exists (BankCoreLocation.mk (id.id % (NumCoreInNextLevel * NumChipPerRank) % NumCoreInNextLevel))
      exact ⟨rfl, Nat.mod_lt _ h_NumCoreInNextLevel_pos⟩

theorem coreEquiv_left_inv (id : PimCoreId) (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) (IsBank : Bool)
  (h_divides : NumBankPerRank % NumChipPerRank = 0) :
  getCoreId (getCoreLocation id NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank) NumCoreInNextLevel NumBankPerRank NumChipPerRank = id := by
  cases IsBank
  · -- Prove for IsBank = false (subarray_inverse)
    exact subarray_inverse id NumCoreInNextLevel NumBankPerRank NumChipPerRank h_divides
  · -- Prove for IsBank = true (using your bank_inverse theorem)
    exact bank_inverse id NumCoreInNextLevel NumBankPerRank NumChipPerRank

theorem coreEquiv_right_inv
  (NumCoreInNextLevel NumBankPerRank NumChipPerRank : Nat) (IsBank : Bool)
  (loc : PimCoreLocation)
  (h_valid : ValidLocation NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank loc)
  (h_NumCoreInNextLevel_pos : NumCoreInNextLevel > 0)
  (h_NumChipPerRank_pos : NumChipPerRank > 0)
  (h_divides : NumBankPerRank % NumChipPerRank = 0) :
  getCoreLocation (getCoreId loc NumCoreInNextLevel NumBankPerRank NumChipPerRank) NumCoreInNextLevel NumBankPerRank NumChipPerRank IsBank = loc := by
  cases IsBank
  · -- Prove for IsBank = false (subarray_inverse2)
    rcases loc with ⟨rank, chip, sum_loc⟩
    dsimp [ValidLocation] at h_valid
    rcases h_valid with ⟨h_chip, s, h_eq, h_bank, h_subarray⟩
    subst h_eq
    apply subarray_inverse2
    · exact h_chip
    · exact h_bank
    · exact h_subarray
    · exact h_NumCoreInNextLevel_pos
    · exact h_NumChipPerRank_pos
    · exact h_divides
  · -- Prove for IsBank = true (using your bank_inverse2 theorem)
    rcases loc with ⟨rank, chip, sum_loc⟩
    dsimp [ValidLocation] at h_valid
    rcases h_valid with ⟨h_chip, b, h_eq, h_bankCoreIdx⟩
    subst h_eq
    apply bank_inverse2
    · exact h_chip
    · exact h_bankCoreIdx
    · exact h_NumCoreInNextLevel_pos
    · exact h_NumChipPerRank_pos
