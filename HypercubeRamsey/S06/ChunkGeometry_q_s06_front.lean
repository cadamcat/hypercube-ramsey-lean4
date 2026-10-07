import HypercubeRamsey.Tools.Binomial

namespace HypercubeRamsey.Lane_q_s06_front

open scoped BigOperators

noncomputable section

private def halfMassNat (ell i : ℕ) : ℝ :=
  if hi : i < ell + 1 then halfBinomialMass ell ⟨i, hi⟩ else 0

private def prefixMass (ell j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, halfMassNat ell i

/-- Consecutive quantile labels for a binomial count. -/
def quantileLabel (ell : ℕ) (ε : ℝ) (q : ℕ) : ℕ :=
  Nat.floor (prefixMass ell (min q (ell + 1)) / ε)

private theorem prefixMass_succ (ell j : ℕ) :
    prefixMass ell (j + 1) = prefixMass ell j + halfMassNat ell j := by
  simp [prefixMass, Finset.sum_range_succ]

theorem quantileLabel_properties (ell : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hAtom : ∀ k : Fin (ell + 1), halfBinomialMass ell k ≤ ε) :
    (∀ a b, a ≤ b → quantileLabel ell ε a ≤ quantileLabel ell ε b) ∧
    (∀ a, quantileLabel ell ε (a + 1) ≤ quantileLabel ell ε a + 1) ∧
    (∀ q, quantileLabel ell ε q ≤ Nat.floor (1 / ε)) ∧
    (∀ j, (∑ q ∈ Finset.range (ell + 1),
      if quantileLabel ell ε q = j then (Nat.choose ell q : ℝ) else 0) ≤
        2 * ε * (2 : ℝ) ^ ell) ∧
    (((Finset.range (ell + 1)).image (quantileLabel ell ε)).card : ℝ) ≤ ε⁻¹ + 1 := by
  classical
  let w : Fin (ell + 1) → ℝ := halfBinomialMass ell
  have hw_nonneg (k : Fin (ell + 1)) : 0 ≤ w k := by
    dsimp [w, halfBinomialMass]
    positivity
  have hw_le (k : Fin (ell + 1)) : w k ≤ ε := by
    exact hAtom k
  let wNat : ℕ → ℝ := halfMassNat ell
  have hwNat_nonneg (i : ℕ) : 0 ≤ wNat i := by
    dsimp [wNat, halfMassNat]
    split_ifs with hi
    · exact hw_nonneg _
    · positivity
  have hwNat_le (i : ℕ) (hi : i ≤ ell) : wNat i ≤ ε := by
    have hlt : i < ell + 1 := by omega
    simpa [wNat, halfMassNat, hlt, w] using hw_le (⟨i, hlt⟩ : Fin (ell + 1))
  let cumMass : ℕ → ℝ := prefixMass ell
  have hprefix_nonneg (j : ℕ) : 0 ≤ cumMass j := by
    dsimp [cumMass, prefixMass]
    exact Finset.sum_nonneg fun i hi => hwNat_nonneg i
  have hprefix_mono : Monotone cumMass := by
    intro a b hab
    dsimp [cumMass, prefixMass]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (by
      intro i hi hnot
      exact hwNat_nonneg i)
  have hprefix_succ (j : ℕ) : cumMass (j + 1) = cumMass j + wNat j := by
    simpa [cumMass, wNat] using prefixMass_succ ell j
  have htotal : cumMass (ell + 1) = 1 := by
    dsimp [cumMass, prefixMass, halfMassNat]
    have hchoose : (∑ i ∈ Finset.range (ell + 1),
        (Nat.choose ell i : ℝ)) = (2 : ℝ) ^ ell := by
      exact_mod_cast Nat.sum_range_choose ell
    have hsum : (∑ i ∈ Finset.range (ell + 1),
        (Nat.choose ell i : ℝ) / (2 : ℝ) ^ ell) = 1 := by
      rw [← Finset.sum_div, hchoose]
      field_simp
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro i hi
    have hlt : i < ell + 1 := Finset.mem_range.mp hi
    simp [hlt, halfBinomialMass]
  have hprefix_bound (j : ℕ) (hj : j ≤ ell + 1) : cumMass j ≤ 1 := by
    calc
      cumMass j ≤ cumMass (ell + 1) := hprefix_mono hj
      _ = 1 := htotal
  have hτ_spec (j : ℕ) :
      (quantileLabel ell ε j : ℝ) ≤ cumMass (min j (ell + 1)) / ε ∧
        cumMass (min j (ell + 1)) / ε < (quantileLabel ell ε j : ℝ) + 1 := by
    have h0 : 0 ≤ cumMass (min j (ell + 1)) / ε :=
      div_nonneg (hprefix_nonneg _) hε.le
    simpa [quantileLabel, cumMass] using (Nat.floor_eq_iff h0).mp rfl
  have hτ_mono : Monotone (quantileLabel ell ε) := by
    intro a b hab
    unfold quantileLabel
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hε.le
    exact hprefix_mono (min_le_min_right _ hab)
  have hτ_step (a : ℕ) : quantileLabel ell ε (a + 1) ≤ quantileLabel ell ε a + 1 := by
    by_cases ha : a < ell + 1
    · have hminA : min a (ell + 1) = a := Nat.min_eq_left (by omega)
      have hminB : min (a + 1) (ell + 1) = a + 1 := Nat.min_eq_left (by omega)
      have hstep := hprefix_succ a
      have hatom := hwNat_le a (by omega)
      have hupper := (hτ_spec a).2
      have hupper0 : cumMass a / ε < (quantileLabel ell ε a : ℝ) + 1 := by
        simpa [hminA] using hupper
      have hupper' : cumMass (a + 1) / ε <
          (quantileLabel ell ε a : ℝ) + 2 := by
        rw [hstep]
        rw [add_div]
        have hdivide : wNat a / ε ≤ 1 := by
          apply (div_le_iff₀ hε).2
          simpa using hatom
        linarith
      have hfloor : (quantileLabel ell ε (a + 1) : ℝ) ≤ cumMass (a + 1) / ε := by
        have hnonneg : 0 ≤ cumMass (a + 1) / ε :=
          div_nonneg (hprefix_nonneg _) hε.le
        have h := Nat.floor_le hnonneg
        simpa [quantileLabel, hminB, cumMass] using h
      have hlt : (quantileLabel ell ε (a + 1) : ℝ) <
          (quantileLabel ell ε a : ℝ) + 2 := by
        exact lt_of_le_of_lt hfloor hupper'
      have hltNat : quantileLabel ell ε (a + 1) < quantileLabel ell ε a + 2 := by
        exact_mod_cast hlt
      omega
    · have hminA : min a (ell + 1) = ell + 1 := Nat.min_eq_right (by omega)
      have hminB : min (a + 1) (ell + 1) = ell + 1 := Nat.min_eq_right (by omega)
      simp [quantileLabel, hminA, hminB]
  have hfiber_mass (j : ℕ) :
      (∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
          quantileLabel ell ε k.val = j), halfBinomialMass ell k) ≤ 2 * ε := by
    let fiber : Finset (Fin (ell + 1)) :=
      Finset.univ.filter fun k => quantileLabel ell ε k.val = j
    by_cases hempty : fiber.Nonempty
    · let a := fiber.min' hempty
      let b := fiber.max' hempty
      have ha : a ∈ fiber := Finset.min'_mem _ _
      have hb : b ∈ fiber := Finset.max'_mem _ _
      have hta : quantileLabel ell ε a.val = j := (Finset.mem_filter.mp ha).2
      have htb : quantileLabel ell ε b.val = j := (Finset.mem_filter.mp hb).2
      have hab : a.val ≤ b.val := by
        exact_mod_cast Finset.min'_le fiber b hb
      have hfiber_interval (k : Fin (ell + 1)) : k ∈ fiber ↔
          a.val ≤ k.val ∧ k.val ≤ b.val := by
        constructor
        · intro hk
          exact ⟨by exact_mod_cast Finset.min'_le fiber k hk,
            by exact_mod_cast Finset.le_max' fiber k hk⟩
        · intro hk
          have hleft := hτ_mono hk.1
          have hright := hτ_mono hk.2
          rw [hta] at hleft
          rw [htb] at hright
          have htag : quantileLabel ell ε k.val = j := Nat.le_antisymm hright hleft
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htag⟩
      have hmassEq : (∑ k ∈ fiber, halfBinomialMass ell k) =
          cumMass (b.val + 1) - cumMass a.val := by
        rw [show fiber = Finset.univ.filter (fun k : Fin (ell + 1) =>
            a.val ≤ k.val ∧ k.val ≤ b.val) by
              ext k
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hfiber_interval k]
        have hbij :
            (∑ k ∈ (Finset.univ.filter (fun k : Fin (ell + 1) =>
                a.val ≤ k.val ∧ k.val ≤ b.val)), halfBinomialMass ell k) =
              ∑ i ∈ Finset.Icc a.val b.val, wNat i := by
          apply Finset.sum_bij (fun k _ => k.val)
          · intro k hk
            exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hk).2
          · intro k₁ hk₁ k₂ hk₂ heq
            exact Fin.ext heq
          · intro i hi
            let k : Fin (ell + 1) := ⟨i, by
              have := Finset.mem_Icc.mp hi
              omega⟩
            refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              Finset.mem_Icc.mp hi⟩, ?_⟩
            rfl
          · intro k hk
            dsimp [wNat, halfMassNat]
            have hlt : k.val < ell + 1 := k.isLt
            simp [hlt, halfBinomialMass]
        rw [hbij]
        have hIco : Finset.Ico a.val (b.val + 1) = Finset.Icc a.val b.val := by
          ext i
          simp [Finset.mem_Ico, Finset.mem_Icc]
        have hsumIco : (∑ i ∈ Finset.Icc a.val b.val, wNat i) =
            (∑ i ∈ Finset.range (b.val + 1), wNat i) -
              (∑ i ∈ Finset.range a.val, wNat i) := by
          rw [← hIco]
          exact Finset.sum_Ico_eq_sub _ (by omega)
        simpa [cumMass, prefixMass] using hsumIco
      have hlow := (hτ_spec a.val).1
      have hupp := (hτ_spec b.val).2
      have hlow' : (j : ℝ) * ε ≤ cumMass a.val := by
        have hmin : min a.val (ell + 1) = a.val := Nat.min_eq_left (by omega)
        rw [hta, hmin] at hlow
        exact (le_div_iff₀ hε).mp hlow
      have hupp' : cumMass b.val < ((j : ℝ) + 1) * ε := by
        have hmin : min b.val (ell + 1) = b.val := Nat.min_eq_left (by omega)
        rw [htb, hmin] at hupp
        exact (div_lt_iff₀ hε).mp hupp
      have hstep : cumMass (b.val + 1) ≤ cumMass b.val + ε := by
        rw [hprefix_succ]
        nlinarith [hwNat_le b.val (by omega)]
      rw [hmassEq]
      linarith
    · have hfiber : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      simp [fiber, hfiber]
      positivity
  have htotal_range (j : ℕ) : (∑ k ∈ Finset.range (ell + 1),
      if quantileLabel ell ε k = j then (Nat.choose ell k : ℝ) else 0) =
      (2 : ℝ) ^ ell *
        (∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
          quantileLabel ell ε k.val = j), halfBinomialMass ell k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun q : ℕ => if quantileLabel ell ε q = j then (Nat.choose ell q : ℝ) else 0)
      (ell + 1)]
    calc
      (∑ k : Fin (ell + 1),
          if quantileLabel ell ε k.val = j then (Nat.choose ell k.val : ℝ) else 0) =
          ∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
            quantileLabel ell ε k.val = j), (Nat.choose ell k.val : ℝ) := by
              rw [Finset.sum_filter]
      _ = (2 : ℝ) ^ ell *
          (∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
            quantileLabel ell ε k.val = j), halfBinomialMass ell k) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              simp only [halfBinomialMass]
              field_simp
  have hbinom : ∀ j, (∑ q ∈ Finset.range (ell + 1),
      if quantileLabel ell ε q = j then (Nat.choose ell q : ℝ) else 0) ≤
        2 * ε * (2 : ℝ) ^ ell := by
    intro j
    rw [htotal_range j]
    calc
      (2 : ℝ) ^ ell *
          (∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
            quantileLabel ell ε k.val = j), halfBinomialMass ell k) ≤
        (2 : ℝ) ^ ell * (2 * ε) :=
          mul_le_mul_of_nonneg_left (hfiber_mass j) (by positivity)
      _ = 2 * ε * (2 : ℝ) ^ ell := by ring
  have hτ_bound (k : Fin (ell + 1)) :
      quantileLabel ell ε k.val ≤ Nat.floor (1 / ε) := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hε.le
    have hmin : min k.val (ell + 1) = k.val := Nat.min_eq_left (by omega)
    rw [hmin]
    exact hprefix_bound k.val (by omega)
  have hτ_bound_all (q : ℕ) : quantileLabel ell ε q ≤ Nat.floor (1 / ε) := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hε.le
    exact hprefix_bound (min q (ell + 1)) (min_le_right _ _)
  have htags : (Finset.range (ell + 1)).image (quantileLabel ell ε) ⊆
      Finset.range (Nat.floor (1 / ε) + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hτ_bound ⟨k, Finset.mem_range.mp hk⟩)
  have hcount : ((Finset.range (ell + 1)).image (quantileLabel ell ε)).card ≤
      Nat.floor (1 / ε) + 1 := by
    calc
      ((Finset.range (ell + 1)).image (quantileLabel ell ε)).card ≤
          (Finset.range (Nat.floor (1 / ε) + 1)).card := Finset.card_le_card htags
      _ = Nat.floor (1 / ε) + 1 := by simp
  refine ⟨hτ_mono, hτ_step, hτ_bound_all, hbinom, ?_⟩
  calc
    (((Finset.range (ell + 1)).image (quantileLabel ell ε)).card : ℝ) ≤
        (Nat.floor (1 / ε) + 1 : ℝ) := by exact_mod_cast hcount
    _ = (Nat.floor (1 / ε) : ℝ) + 1 := by norm_cast
    _ ≤ ε⁻¹ + 1 := by
      have hf := Nat.floor_le (show 0 ≤ (1 : ℝ) / ε by positivity)
      simpa [one_div] using add_le_add_right hf (1 : ℝ)

end

end HypercubeRamsey.Lane_q_s06_front
