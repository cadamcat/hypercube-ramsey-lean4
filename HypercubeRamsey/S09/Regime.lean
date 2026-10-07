import HypercubeRamsey.Framework.Props

/-!
# Definition 9.1: availability exponents

`Hpow` and `Hlin` are the capped infima from the framework.  These lemmas are
the rational-parameter facts used by the two selection nodes below.
-/

namespace HypercubeRamsey

/-- D9.1(i) (09:11–20): availability is monotone in power widths and bias threshold. -/
theorem AvP.mono {T : Stage} {x y h x' y' h' : ℝ}
    (ha : AvP T x y h) (hx : x ≤ x') (hy : y ≤ y') (hh : h ≤ h') :
    AvP T x' y' h' := by
  have hdim : ∀ᶠ k in Filter.atTop, 1 ≤ T.S.n k :=
    T.S.n_tendsto.eventually (Filter.eventually_ge_atTop 1)
  change Available T (PBias (pw x) (pw y) h).toPatch at ha
  change Available T (PBias (pw x') (pw y') h').toPatch
  obtain ⟨κ, hκ, hav⟩ := (available_iff_availableAt T _).mp ha
  apply (available_iff_availableAt T _).mpr
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hav, hdim] with k hk hnk
  apply AvailableAt.mono ?_ hk
  intro AB hAB
  rcases AB with ⟨A, B⟩
  rcases hAB with ⟨μ, ν, hμ, hν, hwx, hwy, hbias⟩
  refine ⟨μ, ν, hμ, hν, ?_, ?_, ?_⟩
  · intro z
    calc
      μ.w z ≤ Real.exp ((T.S.n k : ℝ) ^ x) / T.S.N k := hwx z
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ x') / T.S.N k := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Real.exp_le_exp.mpr
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnk) hx)
  · intro z
    calc
      ν.w z ≤ Real.exp ((T.S.n k : ℝ) ^ y) / T.S.N k := hwy z
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ y') / T.S.N k := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Real.exp_le_exp.mpr
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnk) hy)
  · calc
      (T.S.n k : ℝ) ^ (-h') ≤ (T.S.n k : ℝ) ^ (-h) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnk) (by linarith)
      _ ≤ |dens (T.S.E k) true μ ν - 1 / 2| := hbias

/-- D9.1(i) (09:11–20): availability is monotone in power/linear widths and bias threshold. -/
theorem AvL.mono {T : Stage} {x α h x' α' h' : ℝ}
    (ha : AvL T x α h) (hx : x ≤ x') (hα : α ≤ α') (hh : h ≤ h') :
    AvL T x' α' h' := by
  have hdim : ∀ᶠ k in Filter.atTop, 1 ≤ T.S.n k :=
    T.S.n_tendsto.eventually (Filter.eventually_ge_atTop 1)
  change Available T (PBias (pw x) (lw α) h).toPatch at ha
  change Available T (PBias (pw x') (lw α') h').toPatch
  obtain ⟨κ, hκ, hav⟩ := (available_iff_availableAt T _).mp ha
  apply (available_iff_availableAt T _).mpr
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hav, hdim] with k hk hnk
  apply AvailableAt.mono ?_ hk
  intro AB hAB
  rcases AB with ⟨A, B⟩
  rcases hAB with ⟨μ, ν, hμ, hν, hwx, hwy, hbias⟩
  refine ⟨μ, ν, hμ, hν, ?_, ?_, ?_⟩
  · intro z
    calc
      μ.w z ≤ Real.exp ((T.S.n k : ℝ) ^ x) / T.S.N k := hwx z
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ x') / T.S.N k := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Real.exp_le_exp.mpr
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnk) hx)
  · intro z
    calc
      ν.w z ≤ Real.exp (α * T.S.n k) / T.S.N k := hwy z
      _ ≤ Real.exp (α' * T.S.n k) / T.S.N k := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _))
  · calc
      (T.S.n k : ℝ) ^ (-h') ≤ (T.S.n k : ℝ) ^ (-h) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnk) (by linarith)
      _ ≤ |dens (T.S.E k) true μ ν - 1 / 2| := hbias

/-- D9.1(ii): an exponent strictly above the capped infimum is available. -/
theorem Hpow_lt_available {T : Stage} {x y h : ℝ}
    (hh : Hpow T x y < h) (hpos : 0 < h) (hcap : h ≤ 2) : AvP T x y h := by
  unfold Hpow at hh
  let S : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvP T x y q} ∪ {2}
  have hSne : S.Nonempty := ⟨2, Or.inr rfl⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · rcases hr with ⟨q, hq, hqr, _⟩
      rw [← hqr]
      exact_mod_cast hq.le
    · have : r = 2 := Set.mem_singleton_iff.mp hr
      rw [this]
      norm_num
  have hex : ∃ r ∈ S, r < h := by
    by_contra hnone
    have hlow : h ≤ sInf S := by
      apply le_csInf hSne
      intro r hr
      exact le_of_not_gt (by
        intro hlt
        exact hnone ⟨r, hr, hlt⟩)
    exact (not_le_of_gt hh) hlow
  obtain ⟨r, hr, hrh⟩ := hex
  rcases hr with hr | hr
  · obtain ⟨q, hq, hqr, hav⟩ := hr
    have hqrh : (q : ℝ) < h := by rw [hqr]; exact hrh
    have hqh : (q : ℝ) ≤ h := hqrh.le
    exact AvP.mono hav le_rfl le_rfl hqh
  · have : r = 2 := Set.mem_singleton_iff.mp hr
    rw [this] at hrh
    linarith

/-- D9.1(ii): a positive rational exponent strictly below the capped infimum is unavailable. -/
theorem Hpow_gt_not_available {T : Stage} {x y : ℝ} {h : ℚ}
    (hpos : 0 < h) (hh : (h : ℝ) < Hpow T x y) : ¬ AvP T x y h := by
  intro hav
  unfold Hpow at hh
  let S : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvP T x y q} ∪ {2}
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · rcases hr with ⟨q, hq, hqr, _⟩
      rw [← hqr]
      exact_mod_cast hq.le
    · have : r = 2 := Set.mem_singleton_iff.mp hr
      rw [this]
      norm_num
  have hmem : (h : ℝ) ∈ S := Or.inl ⟨h, hpos, rfl, hav⟩
  have hle : sInf S ≤ (h : ℝ) := csInf_le hSbdd hmem
  exact (not_lt_of_ge hle) hh

/-- D9.1(ii): an exponent strictly above the capped linear infimum is available. -/
theorem Hlin_lt_available {T : Stage} {x α h : ℝ}
    (hh : Hlin T x α < h) (hpos : 0 < h) (hcap : h ≤ 2) : AvL T x α h := by
  unfold Hlin at hh
  let S : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvL T x α q} ∪ {2}
  have hSne : S.Nonempty := ⟨2, Or.inr rfl⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · rcases hr with ⟨q, hq, hqr, _⟩
      rw [← hqr]
      exact_mod_cast hq.le
    · have : r = 2 := Set.mem_singleton_iff.mp hr
      rw [this]
      norm_num
  have hex : ∃ r ∈ S, r < h := by
    by_contra hnone
    have hlow : h ≤ sInf S := by
      apply le_csInf hSne
      intro r hr
      exact le_of_not_gt (by
        intro hlt
        exact hnone ⟨r, hr, hlt⟩)
    exact (not_le_of_gt hh) hlow
  obtain ⟨r, hr, hrh⟩ := hex
  rcases hr with hr | hr
  · obtain ⟨q, hq, hqr, hav⟩ := hr
    have hqrh : (q : ℝ) < h := by rw [hqr]; exact hrh
    have hqh : (q : ℝ) ≤ h := hqrh.le
    exact AvL.mono hav le_rfl le_rfl hqh
  · have : r = 2 := Set.mem_singleton_iff.mp hr
    rw [this] at hrh
    linarith

/-- D9.1(ii): a positive rational exponent strictly below the capped linear infimum is unavailable. -/
theorem Hlin_gt_not_available {T : Stage} {x α : ℝ} {h : ℚ}
    (hpos : 0 < h) (hh : (h : ℝ) < Hlin T x α) : ¬ AvL T x α h := by
  intro hav
  unfold Hlin at hh
  let S : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvL T x α q} ∪ {2}
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · rcases hr with ⟨q, hq, hqr, _⟩
      rw [← hqr]
      exact_mod_cast hq.le
    · have : r = 2 := Set.mem_singleton_iff.mp hr
      rw [this]
      norm_num
  have hmem : (h : ℝ) ∈ S := Or.inl ⟨h, hpos, rfl, hav⟩
  have hle : sInf S ≤ (h : ℝ) := csInf_le hSbdd hmem
  exact (not_lt_of_ge hle) hh

/-- D9.1(ii): `Hpow` is antitone in its first width parameter. -/
theorem Hpow_antitone_x {T : Stage} {x x' y : ℝ} (hxx : x ≤ x') :
    Hpow T x' y ≤ Hpow T x y := by
  unfold Hpow
  let S : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvP T x y q} ∪ {2}
  let S' : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvP T x' y q} ∪ {2}
  have hSne : S.Nonempty := ⟨2, Or.inr rfl⟩
  have hS'bdd : BddBelow S' := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · rcases hr with ⟨q, hq, hqr, _⟩
      rw [← hqr]
      exact_mod_cast hq.le
    · have : r = 2 := Set.mem_singleton_iff.mp hr
      rw [this]
      norm_num
  apply le_csInf hSne
  intro r hr
  rcases hr with hr | hr
  · obtain ⟨q, hq, hqr, hav⟩ := hr
    have hav' : AvP T x' y q := AvP.mono hav hxx le_rfl le_rfl
    calc
      sInf S' ≤ (q : ℝ) := csInf_le hS'bdd (Or.inl ⟨q, hq, rfl, hav'⟩)
      _ = r := hqr
  · have : r = 2 := Set.mem_singleton_iff.mp hr
    subst r
    exact csInf_le hS'bdd (Or.inr rfl)

/-- D9.1(ii): `Hpow` is antitone in its second width parameter. -/
theorem Hpow_antitone_y {T : Stage} {x y y' : ℝ} (hyy : y ≤ y') :
    Hpow T x y' ≤ Hpow T x y := by
  unfold Hpow
  let S : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvP T x y q} ∪ {2}
  let S' : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvP T x y' q} ∪ {2}
  have hSne : S.Nonempty := ⟨2, Or.inr rfl⟩
  have hS'bdd : BddBelow S' := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · rcases hr with ⟨q, hq, hqr, _⟩
      rw [← hqr]
      exact_mod_cast hq.le
    · have : r = 2 := Set.mem_singleton_iff.mp hr
      rw [this]
      norm_num
  apply le_csInf hSne
  intro r hr
  rcases hr with hr | hr
  · obtain ⟨q, hq, hqr, hav⟩ := hr
    have hav' : AvP T x y' q := AvP.mono hav le_rfl hyy le_rfl
    calc
      sInf S' ≤ (q : ℝ) := csInf_le hS'bdd (Or.inl ⟨q, hq, rfl, hav'⟩)
      _ = r := hqr
  · have : r = 2 := Set.mem_singleton_iff.mp hr
    subst r
    exact csInf_le hS'bdd (Or.inr rfl)

/-- D9.1(ii): `Hlin` is antitone in its first width parameter. -/
theorem Hlin_antitone_x {T : Stage} {x x' α : ℝ} (hxx : x ≤ x') :
    Hlin T x' α ≤ Hlin T x α := by
  unfold Hlin
  let S : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvL T x α q} ∪ {2}
  let S' : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvL T x' α q} ∪ {2}
  have hSne : S.Nonempty := ⟨2, Or.inr rfl⟩
  have hS'bdd : BddBelow S' := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · rcases hr with ⟨q, hq, hqr, _⟩
      rw [← hqr]
      exact_mod_cast hq.le
    · have : r = 2 := Set.mem_singleton_iff.mp hr
      rw [this]
      norm_num
  apply le_csInf hSne
  intro r hr
  rcases hr with hr | hr
  · obtain ⟨q, hq, hqr, hav⟩ := hr
    have hav' : AvL T x' α q := AvL.mono hav hxx le_rfl le_rfl
    calc
      sInf S' ≤ (q : ℝ) := csInf_le hS'bdd (Or.inl ⟨q, hq, rfl, hav'⟩)
      _ = r := hqr
  · have : r = 2 := Set.mem_singleton_iff.mp hr
    subst r
    exact csInf_le hS'bdd (Or.inr rfl)

/-- D9.1(ii): `Hlin` is antitone in its linear width parameter. -/
theorem Hlin_antitone_α {T : Stage} {x α α' : ℝ} (hα : α ≤ α') :
    Hlin T x α' ≤ Hlin T x α := by
  unfold Hlin
  let S : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvL T x α q} ∪ {2}
  let S' : Set ℝ := {r | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = r ∧ AvL T x α' q} ∪ {2}
  have hSne : S.Nonempty := ⟨2, Or.inr rfl⟩
  have hS'bdd : BddBelow S' := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · rcases hr with ⟨q, hq, hqr, _⟩
      rw [← hqr]
      exact_mod_cast hq.le
    · have : r = 2 := Set.mem_singleton_iff.mp hr
      rw [this]
      norm_num
  apply le_csInf hSne
  intro r hr
  rcases hr with hr | hr
  · obtain ⟨q, hq, hqr, hav⟩ := hr
    have hav' : AvL T x α' q := AvL.mono hav le_rfl hα le_rfl
    calc
      sInf S' ≤ (q : ℝ) := csInf_le hS'bdd (Or.inl ⟨q, hq, rfl, hav'⟩)
      _ = r := hqr
  · have : r = 2 := Set.mem_singleton_iff.mp hr
    subst r
    exact csInf_le hS'bdd (Or.inr rfl)

/-- D9.1(iii): stabilization turns unavailable power bias into discrepancy. -/
theorem discAt_of_not_AvP {T : Stage} (hT : StabilizedOn T FamB)
    {x y h : ℚ} (hx : 0 < x) (hy : 0 < y) (hh : 0 < h)
    (hnot : ¬ AvP T x y h) :
    DiscAt T (pw x) (pw y) (fun n => (n : ℝ) ^ (-(h : ℝ))) := by
  have hFam : (PBias (pw (x : ℝ)) (pw (y : ℝ)) (h : ℝ)).toPatch ∈ FamB := by
    unfold FamB
    simp only [Set.mem_union, Set.mem_setOf_eq]
    exact Or.inl (Or.inl (Or.inr ⟨x, y, h, Or.inl rfl⟩))
  have hAbsent : EventuallyAbsent T (PBias (pw (x : ℝ)) (pw (y : ℝ)) (h : ℝ)).toPatch := by
    rcases hT _ hFam with hav | habs
    · exact False.elim (hnot hav)
    · exact habs
  apply (discAt_iff_eventually_discOne T _ _ _).2
  filter_upwards [hAbsent] with k hk
  intro μ ν hμ hν hμw hνw c
  let n : ℕ := T.S.n k
  have hTrue : |dens (T.S.E k) true μ ν - 1 / 2| < (n : ℝ) ^ (-(h : ℝ)) := by
    by_contra hnot'
    have hlarge : (n : ℝ) ^ (-(h : ℝ)) ≤
        |dens (T.S.E k) true μ ν - 1 / 2| := le_of_not_gt hnot'
    have hmem : (T.X k, T.Y k) ∈
        (PBias (pw (x : ℝ)) (pw (y : ℝ)) (h : ℝ)).toPatch
          (T.S.n k) (T.S.N k) (T.S.E k) := by
      exact ⟨μ, ν, hμ, hν, hμw, hνw, hlarge⟩
    exact hk (T.X k) (T.Y k) hmem ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩
  have hAbs : |dens (T.S.E k) c μ ν - 1 / 2| =
      |dens (T.S.E k) true μ ν - 1 / 2| := by
    cases c with
    | true => rfl
    | false =>
        rw [dens_false]
        have hneg : 1 - dens (T.S.E k) true μ ν - 1 / 2 =
            -(dens (T.S.E k) true μ ν - 1 / 2) := by ring
        rw [hneg, abs_neg]
  change |dens (T.S.E k) c μ ν - 1 / 2| ≤ (n : ℝ) ^ (-(h : ℝ))
  rw [hAbs]
  exact le_of_lt hTrue

/-- D9.1(iii): stabilization turns unavailable linear bias into discrepancy. -/
theorem discAt_of_not_AvL {T : Stage} (hT : StabilizedOn T FamB)
    {x α h : ℚ} (hx : 0 < x) (hα : 0 < α) (hh : 0 < h)
    (hnot : ¬ AvL T x α h) :
    DiscAt T (pw x) (lw α) (fun n => (n : ℝ) ^ (-(h : ℝ))) := by
  have hFam : (PBias (pw (x : ℝ)) (lw (α : ℝ)) (h : ℝ)).toPatch ∈ FamB := by
    unfold FamB
    simp only [Set.mem_union, Set.mem_setOf_eq]
    exact Or.inl (Or.inr ⟨x, α, h, Or.inl rfl⟩)
  have hAbsent : EventuallyAbsent T (PBias (pw (x : ℝ)) (lw (α : ℝ)) (h : ℝ)).toPatch := by
    rcases hT _ hFam with hav | habs
    · exact False.elim (hnot hav)
    · exact habs
  apply (discAt_iff_eventually_discOne T _ _ _).2
  filter_upwards [hAbsent] with k hk
  intro μ ν hμ hν hμw hνw c
  let n : ℕ := T.S.n k
  have hTrue : |dens (T.S.E k) true μ ν - 1 / 2| < (n : ℝ) ^ (-(h : ℝ)) := by
    by_contra hnot'
    have hlarge : (n : ℝ) ^ (-(h : ℝ)) ≤
        |dens (T.S.E k) true μ ν - 1 / 2| := le_of_not_gt hnot'
    have hmem : (T.X k, T.Y k) ∈
        (PBias (pw (x : ℝ)) (lw (α : ℝ)) (h : ℝ)).toPatch
          (T.S.n k) (T.S.N k) (T.S.E k) := by
      exact ⟨μ, ν, hμ, hν, hμw, hνw, hlarge⟩
    exact hk (T.X k) (T.Y k) hmem ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩
  have hAbs : |dens (T.S.E k) c μ ν - 1 / 2| =
      |dens (T.S.E k) true μ ν - 1 / 2| := by
    cases c with
    | true => rfl
    | false =>
        rw [dens_false]
        have hneg : 1 - dens (T.S.E k) true μ ν - 1 / 2 =
            -(dens (T.S.E k) true μ ν - 1 / 2) := by ring
        rw [hneg, abs_neg]
  change |dens (T.S.E k) c μ ν - 1 / 2| ≤ (n : ℝ) ^ (-(h : ℝ))
  rw [hAbs]
  exact le_of_lt hTrue

/-- D9.1(iv): stronger discrepancy excludes availability at a smaller exponent. -/
theorem not_AvP_of_discAt {T : Stage} {x y h h₀ : ℚ}
    (hxy : 0 < x ∧ 0 < y) (hh : 0 < h) (h₀h : h < h₀)
    (hd : DiscAt T (pw x) (pw y) (fun n => (n : ℝ) ^ (-(h₀ : ℝ)))) :
    ¬ AvP T x y h := by
  intro hav
  change Available T (PBias (pw (x : ℝ)) (pw (y : ℝ)) (h : ℝ)).toPatch at hav
  obtain ⟨κ, hκ, havail⟩ := (available_iff_availableAt T _).mp hav
  have hn : ∀ᶠ k in Filter.atTop, 2 ≤ T.S.n k :=
    T.S.n_tendsto.eventually (Filter.eventually_ge_atTop 2)
  have hdisc : ∀ᶠ k in Filter.atTop,
      DiscOne (T.S.E k) (T.X k) (T.Y k)
        ((T.S.n k : ℝ) ^ (x : ℝ)) ((T.S.n k : ℝ) ^ (y : ℝ))
        ((T.S.n k : ℝ) ^ (-(h₀ : ℝ))) :=
    (discAt_iff_eventually_discOne T _ _ _).mp hd
  have hfalse : ∀ᶠ k : ℕ in Filter.atTop, False := by
    filter_upwards [havail, hdisc, hn] with k hk hdK hnk
    have hempty : ((∅ : Finset (Fin (T.S.N k))).card : ℝ) ≤ κ * T.S.N k := by
      simp
      positivity
    obtain ⟨A, B, hAB, hA, hB⟩ := hk ∅ ∅ hempty hempty
    have hAsub : A ⊆ T.X k := fun z hz => (Finset.mem_sdiff.mp (hA hz)).1
    have hBsub : B ⊆ T.Y k := fun z hz => (Finset.mem_sdiff.mp (hB hz)).1
    rcases hAB with ⟨μ, ν, hμA, hνB, hμw, hνw, hbias⟩
    have hμX : μ.SupportedIn (T.X k) := by
      intro z hz
      exact hμA z (fun hza => hz (hAsub hza))
    have hνY : ν.SupportedIn (T.Y k) := by
      intro z hz
      exact hνB z (fun hzb => hz (hBsub hzb))
    have hdiscTrue := hdK μ ν hμX hνY hμw hνw true
    have hnR : 1 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 1 < T.S.n k)
    have hpow : (T.S.n k : ℝ) ^ (-(h₀ : ℝ)) < (T.S.n k : ℝ) ^ (-(h : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt hnR (by exact_mod_cast (neg_lt_neg h₀h))
    exact (not_le_of_gt hpow) (le_trans hbias hdiscTrue)
  obtain ⟨k, hk⟩ := hfalse.exists
  exact hk.elim

/-- D9.1(iv): stronger linear discrepancy excludes availability at a smaller exponent. -/
theorem not_AvL_of_discAt {T : Stage} {x α h h₀ : ℚ}
    (hxα : 0 < x ∧ 0 < α) (hh : 0 < h) (h₀h : h < h₀)
    (hd : DiscAt T (pw x) (lw α) (fun n => (n : ℝ) ^ (-(h₀ : ℝ)))) :
    ¬ AvL T x α h := by
  intro hav
  change Available T (PBias (pw (x : ℝ)) (lw (α : ℝ)) (h : ℝ)).toPatch at hav
  obtain ⟨κ, hκ, havail⟩ := (available_iff_availableAt T _).mp hav
  have hn : ∀ᶠ k in Filter.atTop, 2 ≤ T.S.n k :=
    T.S.n_tendsto.eventually (Filter.eventually_ge_atTop 2)
  have hdisc : ∀ᶠ k in Filter.atTop,
      DiscOne (T.S.E k) (T.X k) (T.Y k)
        ((T.S.n k : ℝ) ^ (x : ℝ)) ((α : ℝ) * T.S.n k)
        ((T.S.n k : ℝ) ^ (-(h₀ : ℝ))) :=
    (discAt_iff_eventually_discOne T _ _ _).mp hd
  have hfalse : ∀ᶠ k : ℕ in Filter.atTop, False := by
    filter_upwards [havail, hdisc, hn] with k hk hdK hnk
    have hempty : ((∅ : Finset (Fin (T.S.N k))).card : ℝ) ≤ κ * T.S.N k := by
      simp
      positivity
    obtain ⟨A, B, hAB, hA, hB⟩ := hk ∅ ∅ hempty hempty
    have hAsub : A ⊆ T.X k := fun z hz => (Finset.mem_sdiff.mp (hA hz)).1
    have hBsub : B ⊆ T.Y k := fun z hz => (Finset.mem_sdiff.mp (hB hz)).1
    rcases hAB with ⟨μ, ν, hμA, hνB, hμw, hνw, hbias⟩
    have hμX : μ.SupportedIn (T.X k) := by
      intro z hz
      exact hμA z (fun hza => hz (hAsub hza))
    have hνY : ν.SupportedIn (T.Y k) := by
      intro z hz
      exact hνB z (fun hzb => hz (hBsub hzb))
    have hdiscTrue := hdK μ ν hμX hνY hμw hνw true
    have hnR : 1 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 1 < T.S.n k)
    have hpow : (T.S.n k : ℝ) ^ (-(h₀ : ℝ)) < (T.S.n k : ℝ) ^ (-(h : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt hnR (by exact_mod_cast (neg_lt_neg h₀h))
    exact (not_le_of_gt hpow) (le_trans hbias hdiscTrue)
  obtain ⟨k, hk⟩ := hfalse.exists
  exact hk.elim

end HypercubeRamsey
