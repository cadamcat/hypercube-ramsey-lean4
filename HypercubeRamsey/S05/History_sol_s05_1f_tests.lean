import HypercubeRamsey.S05.History_sol_s05_1f_feasible

namespace HypercubeRamsey.Lane_sol_s05_1f
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

private theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (h : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · simp only [if_pos ha, if_pos (h ω ha)]; exact le_rfl
  · simp only [if_neg ha]; split_ifs <;> simp [P.nonneg ω]

/-- The fixed uniform smoothing component costs at most log 2 per coordinate. -/
theorem smooth_positive_log_le (P Q : Law N) (y : Fin N) (hQ : 0 < Q.w y) :
    max 0 (Real.log (P.w y / (X.smooth Q).w y)) ≤
      max 0 (Real.log (P.w y / Q.w y)) + Real.log 2 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hp : P.w y = 0
  · simp only [hp, zero_div, Real.log_zero, max_self, zero_add]
    exact hlog2
  · have hpp : 0 < P.w y := lt_of_le_of_ne (P.nonneg y) (Ne.symm hp)
    have hsm := smooth_weight_pos X Q y
    have hqle : Q.w y / 2 ≤ (X.smooth Q).w y := by
      change Q.w y / 2 ≤ (Q.w y + (N : ℝ)⁻¹) / 2
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))) (by norm_num)
    have hrat : P.w y / (X.smooth Q).w y ≤ (P.w y / Q.w y) * 2 := by
      calc
        _ ≤ P.w y / (Q.w y / 2) := div_le_div_of_nonneg_left hpp.le
          (div_pos hQ (by norm_num)) hqle
        _ = _ := by ring
    have hlog : Real.log (P.w y / (X.smooth Q).w y) ≤
        Real.log (P.w y / Q.w y) + Real.log 2 := by
      have hh := Real.log_le_log (div_pos hpp hsm) hrat
      rwa [Real.log_mul (div_pos hpp hQ).ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    apply max_le
    · exact add_nonneg (le_max_left _ _) hlog2
    · exact hlog.trans (add_le_add (le_max_right 0 (Real.log (P.w y / Q.w y))) le_rfl)

/-- A fixed price direction has its predictable clipped-cost tail under the
original posterior law, before any selection of a successful path. -/
theorem clipped_direction_tail {s : ℕ} {I : Type*} [Fintype I]
    (P : FinProb (Fin s → Fin N)) (Q : I → FinProb (Fin s → Fin N))
    (price : I → ℝ) (b C L ε : ℝ) (hs : 0 < s)
    (hp : ∀ i, 0 ≤ price i) (hpsum : ∑ i, price i = 1)
    (hL : 0 < L) (hε : 0 < ε)
    (hdom : ∀ i θ, P.w θ ≤ Real.exp (b * s) * (Q i).w θ) :
    P.pr (fun θ =>
      (∑ h, (X.condCoord P.w θ h).expect (fun y => min L (∑ i, price i *
        max 0 (Real.log ((X.condCoord P.w θ h).w y /
          (X.smooth (X.condCoord (Q i).w θ h)).w y))))) >
      (b + C + Real.log 2 + ε) * s) ≤
        (Fintype.card I : ℝ) * Real.exp ((s : ℝ) * Real.log 2 - C * s / 2) +
          Real.exp (-2 * (ε * s) ^ 2 / ((s : ℝ) * (2 * L) ^ 2)) := by
  let f := fun θ h y => min L (∑ i, price i *
    max 0 (Real.log ((X.condCoord P.w θ h).w y /
      (X.smooth (X.condCoord (Q i).w θ h)).w y)))
  let bad := fun i θ => (b * s + C * s) <
    ∑ h, max 0 (Real.log ((X.condCoord P.w θ h).w (θ h) /
      (X.condCoord (Q i).w θ h).w (θ h)))
  have hbad (i) : P.pr (bad i) ≤ Real.exp ((s : ℝ) * Real.log 2 - C * s / 2) := by
    have he : -((C / 2 - Real.log 2) * (s : ℝ)) = (s : ℝ) * Real.log 2 - C * s / 2 := by ring
    simpa only [bad, he] using condCoord_positive_log_tail X P (Q i) (b * s) C (hdom i)
  have hf (θ h y) : 0 ≤ f θ h y ∧ f θ h y ≤ L := by
    exact ⟨le_min hL.le (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (le_max_left _ _)), min_le_left _ _⟩
  have hpre (θ ϑ : Fin s → Fin N) (h : Fin s)
      (he : ∀ i, i < h → θ i = ϑ i) : f θ h = f ϑ h := by
    funext y
    dsimp only [f]
    simp_rw [condCoord_prefix_congr X P.w θ ϑ h he]
    congr 3
    funext i
    rw [condCoord_prefix_congr X (Q i).w θ ϑ h he]
  have haz := condCoord_predictable_concentration X P f L ε hs hL hε hf hpre
  let mart := fun θ =>
    (∑ h, (X.condCoord P.w θ h).expect (f θ h)) > (∑ h, f θ h (θ h)) + ε * s
  have hactual (θ : Fin s → Fin N) (hθ : P.w θ ≠ 0) (hno : ¬ ∃ i, bad i θ) :
      (∑ h, f θ h (θ h)) ≤ (b + C + Real.log 2) * s := by
    have hPpos : 0 < P.w θ := lt_of_le_of_ne (P.nonneg θ) (Ne.symm hθ)
    have hQpos (i) : 0 < (Q i).w θ := by
      by_contra h
      have hqz : (Q i).w θ = 0 := le_antisymm (le_of_not_gt h) ((Q i).nonneg θ)
      have hh := hdom i θ
      rw [hqz, mul_zero] at hh
      exact (not_le_of_gt hPpos) hh
    have hbound (i) : ∑ h, max 0 (Real.log ((X.condCoord P.w θ h).w (θ h) /
        (X.smooth (X.condCoord (Q i).w θ h)).w (θ h))) ≤
        (b + C + Real.log 2) * s := by
      calc
        _ ≤ ∑ h, (max 0 (Real.log ((X.condCoord P.w θ h).w (θ h) /
            (X.condCoord (Q i).w θ h).w (θ h))) + Real.log 2) :=
          Finset.sum_le_sum fun h _ => smooth_positive_log_le X _ _ _
            (condCoord_path_pos X (Q i) θ (hQpos i) h)
        _ = (∑ h, max 0 (Real.log ((X.condCoord P.w θ h).w (θ h) /
            (X.condCoord (Q i).w θ h).w (θ h)))) + (s : ℝ) * Real.log 2 := by
          rw [Finset.sum_add_distrib]; simp
        _ ≤ _ := by
          have hn : ¬ bad i θ := fun h => hno ⟨i, h⟩
          have hh : (∑ h, max 0 (Real.log ((X.condCoord P.w θ h).w (θ h) /
              (X.condCoord (Q i).w θ h).w (θ h)))) ≤ b * s + C * s := le_of_not_gt hn
          nlinarith
    calc
      _ ≤ ∑ h, ∑ i, price i * max 0 (Real.log ((X.condCoord P.w θ h).w (θ h) /
          (X.smooth (X.condCoord (Q i).w θ h)).w (θ h))) :=
        Finset.sum_le_sum fun h _ => min_le_right _ _
      _ = ∑ i, price i * (∑ h, max 0 (Real.log ((X.condCoord P.w θ h).w (θ h) /
          (X.smooth (X.condCoord (Q i).w θ h)).w (θ h)))) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      _ ≤ ∑ i, price i * ((b + C + Real.log 2) * s) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbound i) (hp i)
      _ = _ := by rw [← Finset.sum_mul, hpsum, one_mul]
  have himp (θ) (ht : P.w θ ≠ 0) (hfail :
      (∑ h, (X.condCoord P.w θ h).expect (f θ h)) > (b + C + Real.log 2 + ε) * s) :
      (∃ i, bad i θ) ∨ mart θ := by
    by_cases hbad : ∃ i, bad i θ
    · exact Or.inl hbad
    · have ha := hactual θ ht hbad
      right
      dsimp [mart]
      nlinarith
  calc
    _ ≤ P.pr (fun θ => (∃ i, bad i θ) ∨ mart θ) := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro θ _
      by_cases ht : P.w θ = 0
      · simp [ht]
      · by_cases hfail : (∑ h, (X.condCoord P.w θ h).expect (f θ h)) >
            (b + C + Real.log 2 + ε) * s
        · have ho := himp θ ht hfail
          simp only [f] at hfail
          simp only [if_pos hfail, if_pos ho]; exact le_rfl
        · simp only [f] at hfail
          simp only [if_neg hfail]; split_ifs <;> simp [P.nonneg θ]
    _ ≤ P.pr (fun θ => ∃ i, bad i θ) + P.pr mart := P.pr_union _ _
    _ ≤ (∑ i, P.pr (bad i)) + P.pr mart := add_le_add (FinProb.pr_exists_le_sum5 P bad) le_rfl
    _ ≤ (∑ _i : I, Real.exp ((s : ℝ) * Real.log 2 - C * s / 2)) +
        Real.exp (-2 * (ε * s) ^ 2 / ((s : ℝ) * (2 * L) ^ 2)) :=
      add_le_add (Finset.sum_le_sum fun i _ => hbad i) haz
    _ = _ := by simp


private theorem pi_pr_rectangle {s : ℕ} (P : Fin s → Law N) (A : Fin s → Fin N → Prop) :
    (FinProb.pi P).pr (fun θ => ∀ i, A i (θ i)) = ∏ i, (P i).pr (A i) := by
  unfold FinProb.pr
  simp only [FinProb.pi]
  calc
    _ = ∑ θ : Fin s → Fin N, ∏ i, if A i (θ i) then (P i).w (θ i) else 0 := by
      apply Finset.sum_congr rfl
      intro θ _
      by_cases ha : ∀ i, A i (θ i)
      · simp only [if_pos ha, Fintype.prod_ite_zero, if_pos ha]
      · simp only [if_neg ha, Fintype.prod_ite_zero, if_neg ha]
    _ = _ := (Fintype.prod_sum (fun i y => if A i y then (P i).w y else 0)).symm

/-- The next-coordinate conditional of a product law is its corresponding factor. -/
theorem condCoord_pi {s : ℕ} (P : Fin s → Law N) (θ : Fin s → Fin N)
    (hθ : (FinProb.pi P).w θ ≠ 0) (h : Fin s) (y : Fin N) :
    (X.condCoord (FinProb.pi P).w θ h).w y = (P h).w y := by
  let A := fun z : Fin s → Fin N => ∀ i, i < h → z i = θ i
  let F := fun i : Fin s => if i < h then (P i).w (θ i) else 1
  have hprefix : (FinProb.pi P).pr A = ∏ i, F i := by
    change (FinProb.pi P).pr (fun z => ∀ i, i < h → z i = θ i) = _
    rw [pi_pr_rectangle P (fun i z => i < h → z = θ i)]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i < h <;> simp [FinProb.pr, F, hi, (P i).sum_eq_one]
  have hnum : (FinProb.pi P).pr (fun z => A z ∧ z h = y) =
      (FinProb.pi P).pr A * (P h).w y := by
    have he : (fun z => A z ∧ z h = y) =
        (fun z => ∀ i, (i < h → z i = θ i) ∧ (i = h → z i = y)) := by
      funext z
      apply propext
      constructor
      · rintro ⟨hp, hy⟩ i
        exact ⟨hp i, by intro he; subst i; exact hy⟩
      · intro hh
        exact ⟨fun i hi => (hh i).1 hi, (hh h).2 rfl⟩
    rw [he, pi_pr_rectangle P (fun i z => (i < h → z = θ i) ∧ (i = h → z = y)), hprefix]
    have hsingle (i) : (P i).pr (fun z => (i < h → z = θ i) ∧ (i = h → z = y)) =
        F i * (if i = h then (P i).w y else 1) := by
      by_cases hie : i = h
      · subst i; simp [F, FinProb.pr]
      · by_cases hi : i < h <;> simp [F, FinProb.pr, hie, hi, (P i).sum_eq_one]
    simp_rw [hsingle]
    rw [Finset.prod_mul_distrib]
    simp
  have hp := condCoord_prefix_pos (FinProb.pi P) θ h
    (lt_of_le_of_ne ((FinProb.pi P).nonneg θ) (Ne.symm hθ))
  have hc := condCoord_expect X (FinProb.pi P) θ h (fun z => if z = y then 1 else 0) hp
  have hnumeq : (∑ z : Fin s → Fin N, if A z then
      (FinProb.pi P).w z * (if z h = y then 1 else 0) else 0) =
      (FinProb.pi P).pr (fun z => A z ∧ z h = y) := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro z _
    by_cases ha : A z <;> by_cases hy : z h = y <;> simp [ha, hy]
  have hcleft : (X.condCoord (FinProb.pi P).w θ h).expect (fun z => if z = y then 1 else 0) =
      (X.condCoord (FinProb.pi P).w θ h).w y := by simp [FinProb.expect]
  rw [hcleft] at hc
  change _ = (∑ z, if A z then _ else 0) / (FinProb.pi P).pr A at hc
  rw [hnumeq, hnum, mul_div_cancel_left₀ _ hp.ne'] at hc
  exact hc

/-- Uniform coordinate reference for the joint posterior atom bound. -/
def uniformLabels : Law N := FinProb.uniform Finset.univ ⟨X.y₀, Finset.mem_univ _⟩

theorem uniformLabels_weight (y : Fin N) : (uniformLabels X).w y = (N : ℝ)⁻¹ := by
  simp [uniformLabels, FinProb.uniform]

theorem uniform_condCoord {s : ℕ} (θ : Fin s → Fin N) (h : Fin s) (y : Fin N) :
    (X.condCoord (FinProb.pi fun _ : Fin s => uniformLabels X).w θ h).w y = (N : ℝ)⁻¹ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos X.y₀
  have hθ : (FinProb.pi fun _ : Fin s => uniformLabels X).w θ ≠ 0 := by
    simp only [FinProb.pi, uniformLabels_weight, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (pow_pos (inv_pos.mpr hN) _).ne'
  rw [condCoord_pi X (fun _ => uniformLabels X) θ hθ h y, uniformLabels_weight]

theorem uniform_joint_domination {s : ℕ} (P : FinProb (Fin s → Fin N)) (B : ℝ)
    (hcap : ∀ θ, (N : ℝ) ^ s * P.w θ ≤ Real.exp B) :
    ∀ θ, P.w θ ≤ Real.exp B * (FinProb.pi fun _ : Fin s => uniformLabels X).w θ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos X.y₀
  intro θ
  simp only [FinProb.pi, uniformLabels_weight, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    inv_pow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hN _)).mpr
  simpa [mul_comm] using hcap θ


/-- Conditional density-bad mass is controlled by the clipped log-density cost. -/
theorem coordinate_density_le (X : Setup5 γ K' χ n N E G) {s : ℕ} (P : Fin s → Law N) (hs : 0 < s)
    (D : ℝ) (hD : 0 < D) :
    (coordinatePair P hs).pr (fun hy => Real.exp D / ((s : ℝ) * N) <
      (coordinatePair P hs).w hy) ≤
      (∑ h, (P h).expect (fun y => min D (max 0 (Real.log ((N : ℝ) * (P h).w y))))) /
        ((s : ℝ) * D) := by
  let ν := coordinatePair P hs
  let f := fun hy : Fin s × Fin N => min D (max 0 (Real.log ((N : ℝ) * (P hy.1).w hy.2)))
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos X.y₀
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsub (hy) (hb : Real.exp D / ((s : ℝ) * N) < ν.w hy) : D ≤ f hy := by
    have hratio : Real.exp D / (N : ℝ) < (P hy.1).w hy.2 := by
      have hh := hb
      change Real.exp D / ((s : ℝ) * N) < (P hy.1).w hy.2 / (s : ℝ) at hh
      rw [mul_comm (s : ℝ) (N : ℝ), ← div_div] at hh
      exact (div_lt_div_iff_of_pos_right hsR).mp hh
    have hlog : D < Real.log ((N : ℝ) * (P hy.1).w hy.2) := by
      have hh := Real.log_lt_log (Real.exp_pos D) ((div_lt_iff₀ hN).mp hratio)
      simpa [mul_comm] using hh
    exact le_min le_rfl ((le_max_right _ _).trans' hlog.le)
  have hpr := pr_mono ν _ _ hsub
  have hm := ν.markov f D (fun hy => le_min hD.le (le_max_left _ _)) hD
  apply (hpr.trans hm).trans_eq
  rw [coordinatePair_expect]
  dsimp only [f]
  rw [div_div]

/-- At a joint atom cap, the density-good mass test also has a fixed-data
conditional path bound. -/
theorem density_path_tail {s : ℕ} (P : FinProb (Fin s → Fin N))
    (b C D ε η : ℝ) (hs : 0 < s) (hD : 0 < D) (hε : 0 < ε)
    (hbudget : b + C + Real.log 2 + ε ≤ η * D)
    (hcap : ∀ θ, (N : ℝ) ^ s * P.w θ ≤ Real.exp (b * s)) :
    P.pr (fun θ =>
      (coordinatePair (fun h => X.condCoord P.w θ h) hs).pr (fun hy =>
        Real.exp D / ((s : ℝ) * N) <
          (coordinatePair (fun h => X.condCoord P.w θ h) hs).w hy) > η) ≤
      Real.exp ((s : ℝ) * Real.log 2 - C * s / 2) +
        Real.exp (-2 * (ε * s) ^ 2 / ((s : ℝ) * (2 * D) ^ 2)) := by
  let Q := FinProb.pi fun _ : Fin s => uniformLabels X
  have hdom := uniform_joint_domination X P (b * s) hcap
  have htail := clipped_direction_tail X (I := Unit) P (fun _ => Q) (fun _ => 1)
    b C D ε hs (fun _ => by norm_num) (by simp) hD hε (fun _ => hdom)
  have hq (θ : Fin s → Fin N) (h : Fin s) (y : Fin N) :
      (X.smooth (X.condCoord Q.w θ h)).w y = (N : ℝ)⁻¹ := by
    change (_ + (N : ℝ)⁻¹) / 2 = _
    rw [uniform_condCoord X θ h y]
    ring
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, Fintype.card_unique,
    Nat.cast_one] at htail
  have hlog (θ : Fin s → Fin N) (h : Fin s) (y : Fin N) :
      Real.log ((X.condCoord P.w θ h).w y / (N : ℝ)⁻¹) =
        Real.log ((N : ℝ) * (X.condCoord P.w θ h).w y) := by
    rw [div_inv_eq_mul, mul_comm]
  simp_rw [hq, hlog] at htail
  apply (pr_mono P _ _ ?_).trans (by simpa only [one_mul] using htail)
  intro θ hbad
  have hh := coordinate_density_le X (fun h => X.condCoord P.w θ h) hs D hD
  have hpos : (0 : ℝ) < (s : ℝ) * D := mul_pos (by exact_mod_cast hs) hD
  have hsum := (lt_div_iff₀ hpos).mp (hbad.trans_le hh)
  have hmul := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg s)
  nlinarith


/-- Union all finite box directions at fixed data; each direction is tested
under the entering posterior, before restricting to any successful path. -/
theorem clipped_grid_tail {s : ℕ} {I : Type*} [Fintype I]
    (P : FinProb (Fin s → Fin N)) (Q : I → FinProb (Fin s → Fin N))
    (b C L ε εg B : ℝ) (hs : 0 < s) (hL : 0 < L) (hε : 0 < ε)
    (hbudget : b + C + Real.log 2 + ε ≤ B)
    (hdom : ∀ i θ, P.w θ ≤ Real.exp (b * s) * (Q i).w θ) :
    P.pr (fun θ => ∃ a : I → Fin (⌈(1 + εg⁻¹) * Fintype.card I⌉₊ + 1),
      0 < ∑ i, (a i).val ∧
      (coordinatePair (fun h => X.condCoord P.w θ h) hs).expect (fun hy => min L (∑ i,
        ((a i).val : ℝ) / (∑ j, (a j).val : ℕ) *
          max 0 (Real.log ((X.condCoord P.w θ hy.1).w hy.2 /
            (X.smooth (X.condCoord (Q i).w θ hy.1)).w hy.2)))) > B) ≤
      ((⌈(1 + εg⁻¹) * Fintype.card I⌉₊ + 1) ^ Fintype.card I : ℕ) *
        ((Fintype.card I : ℝ) * Real.exp ((s : ℝ) * Real.log 2 - C * s / 2) +
          Real.exp (-2 * (ε * s) ^ 2 / ((s : ℝ) * (2 * L) ^ 2))) := by
  let bad := fun (a : I → Fin (⌈(1 + εg⁻¹) * Fintype.card I⌉₊ + 1)) θ =>
    0 < ∑ i, (a i).val ∧
    (coordinatePair (fun h => X.condCoord P.w θ h) hs).expect (fun hy => min L (∑ i,
      ((a i).val : ℝ) / (∑ j, (a j).val : ℕ) *
        max 0 (Real.log ((X.condCoord P.w θ hy.1).w hy.2 /
          (X.smooth (X.condCoord (Q i).w θ hy.1)).w hy.2)))) > B
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hb (a) : P.pr (bad a) ≤
      (Fintype.card I : ℝ) * Real.exp ((s : ℝ) * Real.log 2 - C * s / 2) +
        Real.exp (-2 * (ε * s) ^ 2 / ((s : ℝ) * (2 * L) ^ 2)) := by
    by_cases ha : 0 < ∑ i, (a i).val
    · let price := fun i : I => ((a i).val : ℝ) / (∑ j, (a j).val : ℕ)
      have hp (i) : 0 ≤ price i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hpsum : ∑ i, price i = 1 := by
        dsimp [price]
        rw [← Finset.sum_div, ← Nat.cast_sum]
        exact div_self (by exact_mod_cast ha.ne')
      apply (pr_mono P _ _ ?_).trans (clipped_direction_tail X P Q price b C L ε hs hp hpsum hL hε hdom)
      intro θ hbad
      have hh := hbad.2
      rw [coordinatePair_expect] at hh
      have hsum := (lt_div_iff₀ hsR).mp hh
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbudget hsR.le) hsum
    · have hz : P.pr (bad a) = 0 := by simp [FinProb.pr, bad, ha]
      rw [hz]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le
  calc
    _ ≤ ∑ a, P.pr (bad a) := FinProb.pr_exists_le_sum5 P bad
    _ ≤ ∑ _a : I → Fin (⌈(1 + εg⁻¹) * Fintype.card I⌉₊ + 1),
        ((Fintype.card I : ℝ) * Real.exp ((s : ℝ) * Real.log 2 - C * s / 2) +
          Real.exp (-2 * (ε * s) ^ 2 / ((s : ℝ) * (2 * L) ^ 2))) :=
      Finset.sum_le_sum fun a _ => hb a
    _ = _ := by simp [Fintype.card_fun]; ring

end
end HypercubeRamsey.Lane_sol_s05_1f
