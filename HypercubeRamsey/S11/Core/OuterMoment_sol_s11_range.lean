import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer

namespace HypercubeRamsey.S11.Core.OuterMoment_sol_s11_range

open HypercubeRamsey OAI.HypercubeRamsey
open Classical Filter
open scoped BigOperators

theorem env_nonneg {N u : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Fin N → ℝ) (x : Fin u → Fin N) : 0 ≤ env E G π x := by
  unfold env
  exact (Finset.le_sup' (fun J : Finset (Fin u) =>
    if 2 ≤ J.card then |inter E G π J x| else 0) (Finset.mem_univ ∅)).trans'
      (by simp)

theorem inter_le_env {N u : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Fin N → ℝ) (x : Fin u → Fin N) (J : Finset (Fin u)) (hJ : 2 ≤ J.card) :
    |inter E G π J x| ≤ env E G π x := by
  unfold env
  simpa [hJ] using Finset.le_sup' (fun J : Finset (Fin u) =>
    if 2 ≤ J.card then |inter E G π J x| else 0) (Finset.mem_univ J)

theorem inter_singleton {N u : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Fin N → ℝ) (hπ : ∑ y, π y = 1) (x : Fin u → Fin N) (j : Fin u)
    (hd : deg E G π (x j) ≠ 0) : inter E G π {j} x = 0 := by
  simp only [inter, Finset.prod_singleton, aF, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, hπ]
  have heq : (∑ y, π y * (hit E G (x j) y / deg E G π (x j))) = 1 := by
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    exact div_self hd
  rw [heq, sub_self]

theorem kernel_expansion {N u : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Fin N → ℝ) (x : Fin u → Fin N) (I : Finset (Fin u)) :
    (∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)) =
      ∑ J ∈ I.powerset, inter E G π J x := by
  simp only [inter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.mul_sum]
  congr 1
  simpa only [add_comm] using Finset.prod_one_add (f := fun j => aF E G π (x j) y) I

theorem kernel_abs_le {N u : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Fin N → ℝ) (hπ : ∑ y, π y = 1) (x : Fin u → Fin N)
    (hd : ∀ j, deg E G π (x j) ≠ 0) (I : Finset (Fin u)) :
    |∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)| ≤
      1 + (2 : ℝ) ^ u * env E G π x := by
  let A := I.powerset.erase ∅
  have hempty : inter E G π ∅ x = 1 := by simp [inter, hπ]
  have hsplit : (∑ J ∈ I.powerset, inter E G π J x) =
      1 + ∑ J ∈ A, inter E G π J x := by
    rw [← Finset.add_sum_erase I.powerset (fun J => inter E G π J x)
      (Finset.empty_mem_powerset I), hempty]
  have hpoint (J : Finset (Fin u)) (hJ : J ∈ A) :
      |inter E G π J x| ≤ env E G π x := by
    by_cases hc : 2 ≤ J.card
    · exact inter_le_env E G π x J hc
    · have hne : J ≠ ∅ := (Finset.mem_erase.mp hJ).1
      have hc1 : J.card = 1 := by
        have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
        omega
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hc1
      rw [inter_singleton E G π hπ x j (hd j), abs_zero]
      exact env_nonneg E G π x
  have hcard : (A.card : ℝ) ≤ (2 : ℝ) ^ u := by
    have h : A.card ≤ Fintype.card (Finset (Fin u)) := Finset.card_le_univ A
    simpa [Fintype.card_finset] using (show (A.card : ℝ) ≤
      (Fintype.card (Finset (Fin u)) : ℝ) by exact_mod_cast h)
  rw [kernel_expansion, hsplit]
  calc
    |1 + ∑ J ∈ A, inter E G π J x| ≤ |(1 : ℝ)| + |∑ J ∈ A, inter E G π J x| := abs_add_le _ _
    _ ≤ 1 + ∑ J ∈ A, |inter E G π J x| := by
      exact add_le_add (by norm_num : |(1 : ℝ)| ≤ 1) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ _J ∈ A, env E G π x := by
      exact add_le_add (le_refl 1) (Finset.sum_le_sum hpoint)
    _ = 1 + (A.card : ℝ) * env E G π x := by simp
    _ ≤ 1 + (2 : ℝ) ^ u * env E G π x := by
      exact add_le_add (le_refl 1) (mul_le_mul_of_nonneg_right hcard (env_nonneg E G π x))

theorem phi_abs_le_exp {N u d n : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Fin N → ℝ) (hπ : ∑ y, π y = 1) (x : Fin u → Fin N)
    (hd : ∀ j, deg E G π (x j) ≠ 0) (hdn : d ≤ n) :
    |phiU E G π d u x| ≤ (2 : ℝ) ^ u * Real.exp ((2 : ℝ) ^ u * n * env E G π x) := by
  have hw := env_nonneg E G π x
  have hA : 0 ≤ (2 : ℝ) ^ u * env E G π x := mul_nonneg (by positivity) hw
  have hp (I : Finset (Fin u)) :
      |(-1 : ℝ) ^ (u - I.card) *
        (∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)) ^ d| ≤
        Real.exp ((2 : ℝ) ^ u * n * env E G π x) := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow]
    calc
      |∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)| ^ d ≤
          (1 + (2 : ℝ) ^ u * env E G π x) ^ d :=
        pow_le_pow_left₀ (abs_nonneg _) (kernel_abs_le E G π hπ x hd I) d
      _ ≤ (Real.exp ((2 : ℝ) ^ u * env E G π x)) ^ d :=
        pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp ((2 : ℝ)^u*env E G π x)) d
      _ = Real.exp ((2 : ℝ) ^ u * env E G π x * d) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp ((2 : ℝ) ^ u * n * env E G π x) := by
        apply Real.exp_le_exp.mpr
        have hh : (d : ℝ) ≤ n := by exact_mod_cast hdn
        nlinarith
  unfold phiU
  calc
    |∑ I : Finset (Fin u), _| ≤ ∑ I : Finset (Fin u), |(-1 : ℝ) ^ (u - I.card) *
      (∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)) ^ d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _I : Finset (Fin u), Real.exp ((2 : ℝ) ^ u * n * env E G π x) :=
      Finset.sum_le_sum (fun I _ => hp I)
    _ = _ := by simp [Fintype.card_finset]

theorem extension_union_card {N u : ℕ} (S : Finset (Fin N)) (cap B : ℝ)
    (M : Finset (Fin u) → (Fin u → Fin N) → ℝ)
    (hC : ∀ (J : Finset (Fin u)) (j : Fin u), j ∈ J →
      ∀ base : Fin u → Fin N, (∀ l, base l ∈ S) →
      ((S.filter fun z => cap < |M J (Function.update base j z)|).card : ℝ) ≤ B)
    (base : Fin u → Fin N) (hbase : ∀ l, base l ∈ S) (R : Finset (Fin u)) (i : Fin u) :
    ((S.filter fun z => ∃ J ∈ R.powerset,
      cap < |M (insert i J) (Function.update base i z)|).card : ℝ) ≤ (2 : ℝ) ^ u * B := by
  let T (J : Finset (Fin u)) := S.filter fun z => cap < |M (insert i J) (Function.update base i z)|
  have hB : 0 ≤ B := (Nat.cast_nonneg (T ∅).card).trans (hC _ i (Finset.mem_insert_self _ _) base hbase)
  have heq : (S.filter fun z => ∃ J ∈ R.powerset,
      cap < |M (insert i J) (Function.update base i z)|) = R.powerset.biUnion T := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_biUnion, T]
    aesop
  rw [heq]
  calc
    ((R.powerset.biUnion T).card : ℝ) ≤ ∑ J ∈ R.powerset, ((T J).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _J ∈ R.powerset, B := Finset.sum_le_sum (fun J _ => hC _ i (Finset.mem_insert_self _ _) base hbase)
    _ = (2 : ℝ) ^ R.card * B := by simp
    _ ≤ (2 : ℝ) ^ u * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact pow_le_pow_right₀ (by norm_num) (by simpa using Finset.card_le_univ R)

/- The alternating coefficient of a list depends only on its union. -/
theorem alternating_coefficient (u : ℕ) (U : Finset (Fin u)) :
    (∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
      (if U ⊆ I then 1 else 0)) = if U = Finset.univ then 1 else 0 := by
  let g : Fin u → ℝ := fun j => if j ∈ U then 0 else -1
  have hterm (I : Finset (Fin u)) :
      (∏ j ∈ I, (1 : ℝ)) * (∏ j ∈ Iᶜ, g j) =
      (-1 : ℝ) ^ (u - I.card) * (if U ⊆ I then 1 else 0) := by
    simp only [Finset.prod_const_one, one_mul]
    by_cases hUI : U ⊆ I
    · rw [if_pos hUI, mul_one]
      calc
        (∏ j ∈ Iᶜ, g j) = ∏ _j ∈ Iᶜ, (-1 : ℝ) := by
          apply Finset.prod_congr rfl
          intro j hj
          have hjI : j ∉ I := Finset.mem_compl.mp hj
          have hjU : j ∉ U := fun h => hjI (hUI h)
          simp [g, hjU]
        _ = _ := by simp [Finset.card_compl]
    · rw [if_neg hUI, mul_zero]
      obtain ⟨j, hjU, hjI⟩ := Finset.not_subset.mp hUI
      exact Finset.prod_eq_zero (Finset.mem_compl.mpr hjI) (by simp [g, hjU])
  calc
    _ = ∑ I : Finset (Fin u), (∏ j ∈ I, (1 : ℝ)) * ∏ j ∈ Iᶜ, g j := by
      apply Finset.sum_congr rfl
      intro I _
      exact (hterm I).symm
    _ = ∏ j : Fin u, (1 + g j) := (Fintype.prod_add (fun _ : Fin u => (1 : ℝ)) g).symm
    _ = _ := by
      by_cases hU : U = Finset.univ
      · subst U
        simp [g]
      · rw [if_neg hU]
        have hnot : ¬ Finset.univ ⊆ U := by
          intro h
          exact hU (Finset.Subset.antisymm (Finset.subset_univ U) h)
        obtain ⟨j, _, hj⟩ := Finset.not_subset.mp hnot
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [g, hj])

def polyPhi (u d : ℕ) (M : Finset (Fin u) → ℝ) : ℝ :=
  ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) * (∑ J ∈ I.powerset, M J) ^ d

theorem polyPhi_covered (u d : ℕ) (M : Finset (Fin u) → ℝ) :
    polyPhi u d M = ∑ f : Fin d → Finset (Fin u),
      if Finset.univ.biUnion f = Finset.univ then ∏ l, M (f l) else 0 := by
  have hexpand (I : Finset (Fin u)) :
      (∑ J ∈ I.powerset, M J) ^ d =
      ∑ f : Fin d → Finset (Fin u),
        (if Finset.univ.biUnion f ⊆ I then ∏ l, M (f l) else 0) := by
    have hsum : (∑ J ∈ I.powerset, M J) =
        ∑ J : Finset (Fin u), if J ⊆ I then M J else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext J
      simp
    rw [hsum, Fintype.sum_pow]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hsub : Finset.univ.biUnion f ⊆ I
    · rw [if_pos hsub]
      apply Finset.prod_congr rfl
      intro l _
      rw [if_pos]
      exact fun j hj => hsub (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hj⟩)
    · rw [if_neg hsub]
      obtain ⟨j, hj, hjI⟩ := Finset.not_subset.mp hsub
      obtain ⟨l, _, hjl⟩ := Finset.mem_biUnion.mp hj
      apply Finset.prod_eq_zero (Finset.mem_univ l)
      exact if_neg (fun h => hjI (h hjl))
  unfold polyPhi
  simp_rw [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  have h : (∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
      (if Finset.univ.biUnion f ⊆ I then ∏ l, M (f l) else 0)) =
      (∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
        (if Finset.univ.biUnion f ⊆ I then 1 else 0)) * ∏ l, M (f l) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro I _
    split_ifs <;> ring
  rw [h, alternating_coefficient]
  split_ifs <;> simp

theorem abs_pow_sub_le (a b c : ℝ) (hc : 1 ≤ c) (ha : |a| ≤ c) (hb : |b| ≤ c)
    (d : ℕ) : |a ^ d - b ^ d| ≤ (d : ℝ) * c ^ d * |a - b| := by
  have hc0 : 0 ≤ c := by linarith
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep : a ^ (d + 1) - b ^ (d + 1) = a * (a ^ d - b ^ d) + b ^ d * (a - b) := by ring
    rw [hstep]
    calc
      |a * (a ^ d - b ^ d) + b ^ d * (a - b)| ≤
          |a| * |a ^ d - b ^ d| + |b| ^ d * |a - b| := by
        simpa only [abs_mul, abs_pow] using abs_add_le (a * (a ^ d - b ^ d)) (b ^ d * (a - b))
      _ ≤ c * ((d : ℝ) * c ^ d * |a - b|) + c ^ d * |a - b| := by
        exact add_le_add (mul_le_mul ha ih (abs_nonneg _) hc0)
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg b) hb d) (abs_nonneg _))
      _ ≤ ((d + 1 : ℕ) : ℝ) * c ^ (d + 1) * |a - b| := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith [mul_nonneg (pow_nonneg hc0 d) (abs_nonneg (a-b))]

theorem powerset_abs_sum_le {u : ℕ} (M : Finset (Fin u) → ℝ) (I : Finset (Fin u)) :
    (∑ J ∈ I.powerset, |M J|) ≤ ∑ J : Finset (Fin u), |M J| := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)

theorem polyPhi_lipschitz (u d : ℕ) (M M' : Finset (Fin u) → ℝ) (c : ℝ)
    (hc : 1 ≤ c) (hM : (∑ J, |M J|) ≤ c) (hM' : (∑ J, |M' J|) ≤ c) :
    |polyPhi u d M - polyPhi u d M'| ≤
      (2 : ℝ) ^ u * d * c ^ d * ∑ J : Finset (Fin u), |M J - M' J| := by
  have hpoint (I : Finset (Fin u)) :
      |(-1 : ℝ) ^ (u - I.card) * (∑ J ∈ I.powerset, M J) ^ d -
        (-1 : ℝ) ^ (u - I.card) * (∑ J ∈ I.powerset, M' J) ^ d| ≤
      (d : ℝ) * c ^ d * ∑ J : Finset (Fin u), |M J - M' J| := by
    rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have ha : |∑ J ∈ I.powerset, M J| ≤ c :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((powerset_abs_sum_le M I).trans hM)
    have hb : |∑ J ∈ I.powerset, M' J| ≤ c :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((powerset_abs_sum_le M' I).trans hM')
    apply (abs_pow_sub_le _ _ c hc ha hb d).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg (by linarith) d))
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (powerset_abs_sum_le (fun J => M J-M' J) I)
  unfold polyPhi
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ I : Finset (Fin u), |(-1 : ℝ) ^ (u - I.card) * (∑ J ∈ I.powerset, M J) ^ d -
        (-1 : ℝ) ^ (u - I.card) * (∑ J ∈ I.powerset, M' J) ^ d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _I : Finset (Fin u), (d : ℝ) * c ^ d * ∑ J : Finset (Fin u), |M J - M' J| :=
      Finset.sum_le_sum (fun I _ => hpoint I)
    _ = _ := by simp [Fintype.card_finset]; ring

/-- Every surviving list covers all `u` coordinates. Multiplying an interaction by
`lam ^ J.card` therefore multiplies each surviving list by at least `lam ^ u`. -/
theorem polyPhi_weighted (u d : ℕ) (M : Finset (Fin u) → ℝ) (lam : ℝ) (hlam : 1 ≤ lam) :
    |polyPhi u d M| ≤ (∑ J : Finset (Fin u), lam ^ J.card * |M J|) ^ d / lam ^ u := by
  have hlam0 : 0 < lam := by linarith
  have hpoint (f : Fin d → Finset (Fin u)) :
      lam ^ u * |if Finset.univ.biUnion f = Finset.univ then ∏ l, M (f l) else 0| ≤
      ∏ l, lam ^ (f l).card * |M (f l)| := by
    by_cases hcover : Finset.univ.biUnion f = Finset.univ
    · rw [if_pos hcover, Finset.abs_prod, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
      apply pow_le_pow_right₀ hlam
      have hh := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin d))) (t := f)
      simpa [hcover] using hh
    · rw [if_neg hcover, abs_zero, mul_zero]
      exact Finset.prod_nonneg (fun l _ => mul_nonneg (pow_nonneg hlam0.le _) (abs_nonneg _))
  apply (le_div_iff₀ (pow_pos hlam0 u)).mpr
  rw [mul_comm, polyPhi_covered]
  calc
    lam ^ u * |∑ f : Fin d → Finset (Fin u), _| ≤
        lam ^ u * ∑ f : Fin d → Finset (Fin u),
          |if Finset.univ.biUnion f = Finset.univ then ∏ l, M (f l) else 0| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hlam0.le u)
    _ = ∑ f : Fin d → Finset (Fin u), lam ^ u *
        |if Finset.univ.biUnion f = Finset.univ then ∏ l, M (f l) else 0| := Finset.mul_sum _ _ _
    _ ≤ ∑ f : Fin d → Finset (Fin u), ∏ l, lam ^ (f l).card * |M (f l)| :=
      Finset.sum_le_sum (fun f _ => hpoint f)
    _ = _ := (Fintype.sum_pow (fun J : Finset (Fin u) => lam ^ J.card * |M J|) d).symm

theorem abs_sum_le_one_add {u : ℕ} (M : Finset (Fin u) → ℝ) (h0 : M ∅ = 1)
    (t : ℝ) (ht : 0 ≤ t) (hM : ∀ J, J ≠ ∅ → |M J| ≤ t) :
    (∑ J : Finset (Fin u), |M J|) ≤ 1 + (2 : ℝ) ^ u * t := by
  have he : (∅ : Finset (Fin u)) ∈ (Finset.univ : Finset (Finset (Fin u))) := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ (fun J => |M J|) he, h0, abs_one]
  calc
    _ ≤ 1 + ∑ _J ∈ Finset.univ.erase (∅ : Finset (Fin u)), t := by
      apply add_le_add (le_refl 1)
      exact Finset.sum_le_sum (fun J hJ => hM J (Finset.mem_erase.mp hJ).1)
    _ = 1 + ((Finset.univ.erase (∅ : Finset (Fin u))).card : ℝ) * t := by simp
    _ ≤ _ := by
      apply add_le_add (le_refl 1)
      apply mul_le_mul_of_nonneg_right _ ht
      exact_mod_cast (show (Finset.univ.erase (∅ : Finset (Fin u))).card ≤ 2 ^ u by
        simpa [Fintype.card_finset] using Finset.card_le_univ (Finset.univ.erase (∅ : Finset (Fin u))))

/-- Truncate interactions at cardinality `r`. The covered generating function bounds
 the truncated polynomial; a power Lipschitz estimate charges its difference to
 the sum of the interactions of cardinality at least `r`. -/
theorem polyPhi_low_bound (u d n r : ℕ) (M : Finset (Fin u) → ℝ)
    (t lam : ℝ) (ht : 0 ≤ t) (hlam : 1 ≤ lam) (hr : 0 < r) (hdn : d ≤ n)
    (h0 : M ∅ = 1) (hM : ∀ J, J ≠ ∅ → |M J| ≤ t)
    (hscale : (n : ℝ) * lam ^ r * t ≤ 1) :
    |polyPhi u d M| ≤ Real.exp ((2 : ℝ) ^ u) / lam ^ u +
      (2 : ℝ) ^ u * n * Real.exp ((2 : ℝ) ^ u) *
        ∑ J : Finset (Fin u), if r ≤ J.card then |M J| else 0 := by
  let M' : Finset (Fin u) → ℝ := fun J => if J.card < r then M J else 0
  let A : ℝ := (2 : ℝ) ^ u
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlam0 : 0 < lam := by linarith
  have hlamr : 1 ≤ lam ^ r := one_le_pow₀ hlam
  have hnt : (n : ℝ) * t ≤ 1 := by nlinarith [show 0 ≤ (n : ℝ) * t from mul_nonneg (Nat.cast_nonneg n) ht]
  have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hM'0 : M' ∅ = 1 := by simp [M', hr, h0]
  have hM' (J : Finset (Fin u)) (hJ : J ≠ ∅) : |M' J| ≤ t := by
    dsimp [M']; split_ifs <;> simp_all
  have hweighted : (∑ J : Finset (Fin u), lam ^ J.card * |M' J|) ≤ 1 + A * (lam ^ r * t) := by
    have heq : (∑ J : Finset (Fin u), |lam ^ J.card * (|M' J|)|) =
        ∑ J : Finset (Fin u), lam ^ J.card * |M' J| := by
      apply Finset.sum_congr rfl
      intro J _
      exact abs_of_nonneg (mul_nonneg (pow_nonneg hlam0.le _) (abs_nonneg _))
    rw [← heq]
    apply abs_sum_le_one_add (fun J => lam ^ J.card * |M' J|)
      (by simp [hM'0]) (lam ^ r * t) (mul_nonneg (pow_nonneg hlam0.le _) ht)
    intro J hJ
    rw [abs_mul, abs_of_nonneg (pow_nonneg hlam0.le _), abs_abs]
    by_cases hc : J.card < r
    · have hpow : lam ^ J.card ≤ lam ^ r := pow_le_pow_right₀ hlam (by omega)
      exact mul_le_mul hpow (hM' J hJ) (abs_nonneg _) (pow_nonneg hlam0.le _)
    · simp [M', hc, mul_nonneg (pow_nonneg hlam0.le _) ht]
  have hexp (v : ℝ) (hv : 0 ≤ v) (hnv : (n : ℝ) * v ≤ 1) :
      (1 + A * v) ^ d ≤ Real.exp A := by
    calc
      _ ≤ (Real.exp (A * v)) ^ d := pow_le_pow_left₀ (by positivity)
        (by simpa [add_comm] using Real.add_one_le_exp (A*v)) d
      _ = Real.exp (A * v * d) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp A := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hA hv]
  have hsmall : |polyPhi u d M'| ≤ Real.exp A / lam ^ u := by
    apply (polyPhi_weighted u d M' lam hlam).trans
    apply div_le_div_of_nonneg_right _ (pow_nonneg hlam0.le _)
    exact (pow_le_pow_left₀ (Finset.sum_nonneg (fun J _ => mul_nonneg
      (pow_nonneg hlam0.le _) (abs_nonneg _))) hweighted d).trans
      (hexp (lam ^ r * t) (mul_nonneg (pow_nonneg hlam0.le _) ht) (by simpa [mul_assoc] using hscale))
  have hdiff : |polyPhi u d M - polyPhi u d M'| ≤
      A * n * Real.exp A * ∑ J : Finset (Fin u), if r ≤ J.card then |M J| else 0 := by
    have hh := polyPhi_lipschitz u d M M' (1+A*t) (by linarith [mul_nonneg hA ht])
      (abs_sum_le_one_add M h0 t ht hM) (abs_sum_le_one_add M' hM'0 t ht hM')
    have hsum : (∑ J : Finset (Fin u), |M J-M' J|) =
        ∑ J : Finset (Fin u), if r ≤ J.card then |M J| else 0 := by
      apply Finset.sum_congr rfl
      intro J _
      by_cases hc : J.card < r
      · simp [M', hc, Nat.not_le.mpr hc]
      · simp [M', hc, Nat.le_of_not_gt hc]
    rw [hsum] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun J _ => by split_ifs <;> positivity))
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hdn' hA
    · exact hexp t ht hnt
    · positivity
    · positivity
  calc
    |polyPhi u d M| ≤ |polyPhi u d M'| + |polyPhi u d M-polyPhi u d M'| := by
      have hh := abs_add_le (polyPhi u d M') (polyPhi u d M-polyPhi u d M')
      convert hh using 1 <;> ring
    _ ≤ _ := add_le_add hsmall hdiff

theorem sMean_eq_two_deg_sub_one {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Fin N → ℝ) (hπ : ∑ y, π y = 1) (x : Fin N) :
    sMean E G π x = 2 * deg E G π x - 1 := by
  unfold sMean deg fv
  calc
    (∑ y, π y * (2 * hit E G x y - 1)) = ∑ y, (2 * (π y * hit E G x y) - π y) := by
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = (∑ y, 2 * (π y * hit E G x y)) - ∑ y, π y := by rw [Finset.sum_sub_distrib]
    _ = _ := by rw [← Finset.mul_sum, hπ]

theorem tuple_weight_sum {N u : ℕ} (σ : Fin N → ℝ) (hσ : ∑ x, σ x = 1) :
    (∑ f : Fin u → Fin N, tupWt σ f) = 1 := by
  unfold tupWt
  rw [← Fintype.prod_sum]
  simp [hσ]

theorem maximal_retained {u : ℕ} (M : Finset (Fin u) → ℝ) (cap : ℝ)
    (hlarge : ∃ J : Finset (Fin u), 2 ≤ J.card ∧ cap < |M J|) :
    ∃ R : Finset (Fin u), R ≠ Finset.univ ∧
      (∀ J ⊆ R, 2 ≤ J.card → |M J| ≤ cap) ∧
      ∀ i : Fin u, i ∉ R → ∃ J ∈ R.powerset, cap < |M (insert i J)| := by
  let good (R : Finset (Fin u)) := ∀ J ⊆ R, 2 ≤ J.card → |M J| ≤ cap
  let A : Finset (Finset (Fin u)) := Finset.univ.filter good
  have hA : A.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro J hJ hc
    have hJe : J = ∅ := Finset.subset_empty.mp hJ
    simp [hJe] at hc
  obtain ⟨R, hR, hmax⟩ := A.exists_max_image Finset.card hA
  have hgood : good R := (Finset.mem_filter.mp hR).2
  have hproper : R ≠ Finset.univ := by
    intro heq
    obtain ⟨J, hc, hv⟩ := hlarge
    exact (not_lt_of_ge (hgood J (by simpa [heq] using Finset.subset_univ J) hc)) hv
  refine ⟨R, hproper, hgood, ?_⟩
  intro i hi
  have hnotgood : ¬ good (insert i R) := by
    intro hg
    have hh := hmax (insert i R) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
    rw [Finset.card_insert_of_notMem hi] at hh
    omega
  simp only [good, not_forall, not_imp, not_le] at hnotgood
  obtain ⟨J, hJ, hc, hv⟩ := hnotgood
  have hiJ : i ∈ J := by
    by_contra h
    have hsub : J ⊆ R := by
      intro j hj
      obtain heq | hjR := Finset.mem_insert.mp (hJ hj)
      · exact False.elim (h (heq ▸ hj))
      · exact hjR
    exact (not_lt_of_ge (hgood J hsub hc)) hv
  refine ⟨J.erase i, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro j hj
    obtain ⟨hne, hjJ⟩ := Finset.mem_erase.mp hj
    exact (Finset.mem_insert.mp (hJ hjJ)).resolve_left hne
  · simpa [Finset.insert_erase hiJ] using hv

theorem inverse_degree_le {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π : Fin N → ℝ) (hπ : ∑ y, π y = 1) (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1/8)
    (x : Fin N) (hm : |sMean E G π x| ≤ 4*b) :
    0 < deg E G π x ∧ (deg E G π x)⁻¹ ≤ 2 * Real.exp (8*b) := by
  have heq := sMean_eq_two_deg_sub_one E G π hπ x
  have hmlo := (abs_le.mp hm).1
  have hD : (1-4*b)/2 ≤ deg E G π x := by linarith
  have hdpos : 0 < deg E G π x := by linarith
  refine ⟨hdpos, (inv_le_iff_one_le_mul₀ hdpos).mpr ?_⟩
  have he : 1+8*b ≤ Real.exp (8*b) := by simpa [add_comm] using Real.add_one_le_exp (8*b)
  have hp : 1 ≤ (1-4*b)*(1+8*b) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left he hdpos.le
  nlinarith

theorem split_weight_integral {u N : ℕ} (σ : Fin N → ℝ) (R : Finset (Fin u))
    (H : (R → Fin N) → ℝ)
    (B : (R → Fin N) → {j : Fin u // j ∉ R} → Fin N → ℝ) :
    (∑ f : Fin u → Fin N, tupWt σ f * H (fun j => f j) *
      ∏ j : {j : Fin u // j ∉ R}, B (fun j => f j) j (f j)) =
    ∑ z : R → Fin N, (∏ j, σ (z j)) * H z *
      ∏ j : {j : Fin u // j ∉ R}, ∑ y, σ y * B z j y := by
  let e := (Equiv.piEquivPiSubtypeProd (fun j : Fin u => j ∈ R) (fun _ => Fin N)).symm
  have hret (z : R → Fin N) (v : {j : Fin u // j ∉ R} → Fin N) :
      (fun j : R => e (z,v) j) = z := by
    funext j
    simp [e, Equiv.piEquivPiSubtypeProd, j.property]
  have hout (z : R → Fin N) (v : {j : Fin u // j ∉ R} → Fin N)
      (j : {j : Fin u // j ∉ R}) : e (z,v) j = v j := by
    simp [e, Equiv.piEquivPiSubtypeProd, j.property]
  have hw (z : R → Fin N) (v : {j : Fin u // j ∉ R} → Fin N) :
      tupWt σ (e (z,v)) = (∏ j : R, σ (z j)) * ∏ j : {j : Fin u // j ∉ R}, σ (v j) := by
    unfold tupWt
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : Fin u => j ∈ R)]
    apply congrArg₂ (fun a b : ℝ => a*b)
    · apply Finset.prod_congr (by ext j; simp)
      intro j _
      exact congrArg σ (congrFun (hret z v) j)
    · apply Finset.prod_congr rfl
      intro j _
      rw [hout]
  have hreindex :
      (∑ f : Fin u → Fin N, tupWt σ f * H (fun j => f j) *
        ∏ j : {j : Fin u // j ∉ R}, B (fun j => f j) j (f j)) =
      ∑ q : (R → Fin N) × ({j : Fin u // j ∉ R} → Fin N),
        tupWt σ (e q) * H (fun j => e q j) *
          ∏ j : {j : Fin u // j ∉ R}, B (fun j => e q j) j (e q j) := by
    symm
    apply Fintype.sum_equiv e
    intro q
    rfl
  rw [hreindex, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [hw, hret, hout]
  calc
    _ = (∏ j : R, σ (z j)) * H z *
        ∑ v : {j : Fin u // j ∉ R} → Fin N, ∏ j, σ (v j) * B z j (v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      exact (Fintype.prod_sum (fun (j : {j : Fin u // j ∉ R}) (y : Fin N) => σ y * B z j y)).symm

noncomputable def retainedTuple {u N : ℕ} (R : Finset (Fin u)) (f : R → Fin N) : Fin R.card → Fin N :=
  fun j => f (R.equivFin.symm j)

noncomputable def liftedSet {u : ℕ} (R : Finset (Fin u)) (J : Finset (Fin R.card)) : Finset (Fin u) :=
  J.map (R.equivFin.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩)

theorem liftedSet_subset {u : ℕ} (R : Finset (Fin u)) (J : Finset (Fin R.card)) :
    liftedSet R J ⊆ R := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  exact (R.equivFin.symm j).property

theorem inter_liftedSet {u N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (R : Finset (Fin u)) (f : Fin u → Fin N) (J : Finset (Fin R.card)) :
    inter E G π (liftedSet R J) f = inter E G π J (retainedTuple R (fun j => f j)) := by
  simp [inter, liftedSet, retainedTuple, Finset.prod_map]

theorem env_retained_le {u N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (R : Finset (Fin u)) (f : Fin u → Fin N) (cap : ℝ) (hc : 0 ≤ cap)
    (hgood : ∀ J ⊆ R, 2 ≤ J.card → |inter E G π J f| ≤ cap) :
    env E G π (retainedTuple R (fun j => f j)) ≤ cap := by
  unfold env
  apply Finset.sup'_le
  intro J _
  split_ifs with hJ
  · rw [← inter_liftedSet]
    apply hgood _ (liftedSet_subset R J)
    simpa [liftedSet] using hJ
  · exact hc

theorem inner_card_eq (n : ℕ) (hn : 1 ≤ n) : Fintype.card (InnerCoord n) = hIn n := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : (n : ℝ) ^ ((1 : ℝ)/10) ≤ n := by
    calc
      _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = _ := Real.rpow_one _
  have hh : hIn n ≤ n := by
    exact_mod_cast (OuterMoment_q_s11_outer.hIn_real_le_pow n).trans hp
  let e : InnerCoord n ≃ Fin (hIn n) :=
    { toFun := fun j => ⟨j.1.val, j.2⟩
      invFun := fun j => ⟨⟨j.val, lt_of_lt_of_le j.isLt hh⟩, j.isLt⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
  simpa using Fintype.card_congr e

theorem eventually_extension_charge (M P : ℝ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * Real.exp (-gS n * Fintype.card (InnerCoord n)/2 + 8*(n : ℝ)*bS n +
        (n : ℝ) ^ ((3 : ℝ)/100)) ≤ (n : ℝ) ^ (-P) := by
  have hp := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ)/10)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hgap1 := OuterMoment_q_s11_outer.eventually_pow_gap ((1 : ℝ)/20) ((9 : ℝ)/100)
    128 (by norm_num) (by norm_num)
  have hgap2 := OuterMoment_q_s11_outer.eventually_pow_gap ((3 : ℝ)/100) ((9 : ℝ)/100)
    16 (by norm_num) (by norm_num)
  have hgap3 := OuterMoment_q_s11_outer.eventually_pow_gap ((1 : ℝ)/100) ((9 : ℝ)/100)
    (8*(100*|P| + |Real.log M| + 1)) (by norm_num) (by positivity)
  filter_upwards [hp, hgap1, hgap2, hgap3,
    (eventually_atTop.mpr ⟨2, fun n hn => hn⟩ : ∀ᶠ n : ℕ in atTop, 2 ≤ n)] with n hp hg1 hg2 hg3 hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  change 2 ≤ (n : ℝ)^((1 : ℝ)/10) at hp
  have hcard : (n : ℝ) ^ ((1 : ℝ)/10)/2 ≤ (Fintype.card (InnerCoord n) : ℝ) := by
    rw [inner_card_eq n (by omega)]
    have hh := Nat.lt_floor_add_one ((n : ℝ)^((1 : ℝ)/10))
    change (n : ℝ) ^ ((1 : ℝ)/10)/2 ≤ (Nat.floor ((n : ℝ)^((1 : ℝ)/10)) : ℝ)
    linarith
  have hgh : (n : ℝ) ^ ((9 : ℝ)/100)/2 ≤ gS n * Fintype.card (InnerCoord n) := by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left hcard (by unfold gS; positivity))
    dsimp [gS]
    rw [← mul_div_assoc, ← Real.rpow_add hnpos]
    norm_num
  have hnb : (n : ℝ)*bS n = (n : ℝ)^((1 : ℝ)/20) := by
    unfold bS
    calc
      _ = (n : ℝ)^(1 : ℝ) * (n : ℝ)^(-(19 : ℝ)/20) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hnpos]; norm_num
  have hlog : Real.log (n : ℝ) ≤ 100*(n : ℝ)^((1 : ℝ)/100) := by
    calc
      _ ≤ (n : ℝ)^((1 : ℝ)/100)/((1 : ℝ)/100) :=
        Real.log_natCast_le_rpow_div n (by norm_num)
      _ = _ := by ring
  have hp1 : 1 ≤ (n : ℝ)^((1 : ℝ)/100) := Real.one_le_rpow hn1 (by norm_num)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlogM : Real.log M ≤ |Real.log M| := le_abs_self _
  have hP : P ≤ |P| := le_abs_self _
  have hlogProd : P*Real.log (n : ℝ) + Real.log M ≤
      (100*|P|+|Real.log M|+1)*(n : ℝ)^((1 : ℝ)/100) := by
    nlinarith [mul_le_mul_of_nonneg_right hP hlog0,
      mul_le_mul_of_nonneg_left hlog (abs_nonneg P),
      mul_le_mul_of_nonneg_left hp1 (abs_nonneg (Real.log M))]
  have hexponent : Real.log M + (-gS n * Fintype.card (InnerCoord n)/2 +
      8*(n : ℝ)*bS n + (n : ℝ)^((3 : ℝ)/100)) ≤ -P * Real.log (n : ℝ) := by
    rw [mul_assoc 8 (n : ℝ) (bS n), hnb]
    linarith
  calc
    _ = Real.exp (Real.log M + (-gS n * Fintype.card (InnerCoord n)/2 +
      8*(n : ℝ)*bS n + (n : ℝ)^((3 : ℝ)/100))) := by
      rw [Real.exp_add (Real.log M) (-gS n * Fintype.card (InnerCoord n)/2 +
        8*(n : ℝ)*bS n + (n : ℝ)^((3 : ℝ)/100)), Real.exp_log hM]
    _ ≤ Real.exp (-P * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [Real.rpow_def_of_pos hnpos]; congr 1; ring

theorem inter_congr {u N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (J : Finset (Fin u)) (f f' : Fin u → Fin N) (h : ∀ j ∈ J, f j = f' j) :
    inter E G π J f = inter E G π J f' := by
  unfold inter
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [h j hj]

noncomputable def kernel {u N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (I : Finset (Fin u)) (f : Fin u → Fin N) : ℝ :=
  ∑ y, π y * ∏ j ∈ I, (1+aF E G π (f j) y)

theorem factor_nonneg_le {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (x y : Fin N) (hd : 0 < deg E G π x) :
    0 ≤ 1+aF E G π x y ∧ 1+aF E G π x y ≤ (deg E G π x)⁻¹ := by
  have he : 1+aF E G π x y = hit E G x y / deg E G π x := by unfold aF; ring
  rw [he]
  have hh : 0 ≤ hit E G x y ∧ hit E G x y ≤ 1 := by unfold hit; split_ifs <;> norm_num
  exact ⟨div_nonneg hh.1 hd.le, by simpa using div_le_div_of_nonneg_right hh.2 hd.le⟩

theorem kernel_nonneg {u N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (hp : ∀ y, 0 ≤ π y) (I : Finset (Fin u)) (f : Fin u → Fin N)
    (hd : ∀ j, 0 < deg E G π (f j)) : 0 ≤ kernel E G π I f := by
  exact Finset.sum_nonneg (fun y _ => mul_nonneg (hp y)
    (Finset.prod_nonneg (fun j _ => (factor_nonneg_le E G π (f j) y (hd j)).1)))

theorem deg_le_one {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (hp : ∀ y, 0 ≤ π y) (hs : ∑ y, π y = 1) (x : Fin N) : deg E G π x ≤ 1 := by
  calc
    _ ≤ ∑ y, π y := Finset.sum_le_sum (fun y _ => by
      have hh : hit E G x y ≤ 1 := by unfold hit; split_ifs <;> norm_num
      simpa using mul_le_mul_of_nonneg_left hh (hp y))
    _ = _ := hs

theorem kernel_omit_le {u N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (hp : ∀ y, 0 ≤ π y) (hs : ∑ y, π y = 1) (I R : Finset (Fin u)) (f : Fin u → Fin N)
    (hd : ∀ j, 0 < deg E G π (f j)) :
    kernel E G π I f ≤ kernel E G π (I ∩ R) f * ∏ j ∈ Rᶜ, (deg E G π (f j))⁻¹ := by
  have hprod (y : Fin N) : (∏ j ∈ I, (1+aF E G π (f j) y)) ≤
      (∏ j ∈ I∩R, (1+aF E G π (f j) y)) * ∏ j ∈ Rᶜ, (deg E G π (f j))⁻¹ := by
    rw [← Finset.prod_inter_mul_prod_sdiff I R]
    apply mul_le_mul_of_nonneg_left _
      (Finset.prod_nonneg (fun j _ => (factor_nonneg_le E G π (f j) y (hd j)).1))
    apply (Finset.prod_le_prod₀ (fun j _ => (factor_nonneg_le E G π (f j) y (hd j)).1)
      (fun j _ => (factor_nonneg_le E G π (f j) y (hd j)).2)).trans
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro j hj
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hj).2
    · intro j _
      exact inv_nonneg.mpr (hd j).le
    · intro j _ _
      exact (one_le_inv₀ (hd j)).mpr (deg_le_one E G π hp hs (f j))
  unfold kernel
  calc
    _ ≤ ∑ y, π y * ((∏ j ∈ I∩R, (1+aF E G π (f j) y)) *
        ∏ j ∈ Rᶜ, (deg E G π (f j))⁻¹) :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hprod y) (hp y))
    _ = _ := by simp_rw [← mul_assoc]; rw [Finset.sum_mul]

noncomputable def retainedSet {u : ℕ} (R I : Finset (Fin u)) : Finset (Fin R.card) :=
  Finset.univ.filter fun j => (R.equivFin.symm j).val ∈ I

theorem lifted_retainedSet {u : ℕ} (R I : Finset (Fin u)) : liftedSet R (retainedSet R I) = I∩R := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hj).2, (R.equivFin.symm j).property⟩
  · intro hi
    obtain ⟨hiI, hiR⟩ := Finset.mem_inter.mp hi
    apply Finset.mem_map.mpr
    refine ⟨R.equivFin ⟨i, hiR⟩, ?_, ?_⟩
    · simp [retainedSet, hiI]
    · simp

theorem kernel_retainedSet {u N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (R I : Finset (Fin u)) (f : Fin u → Fin N) :
    kernel E G π (I∩R) f = kernel E G π (retainedSet R I) (retainedTuple R (fun j => f j)) := by
  rw [← lifted_retainedSet R I]
  simp [kernel, liftedSet, retainedTuple, Finset.prod_map]

theorem kernel_pow_le_exp {u d n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (hs : ∑ y, π y = 1) (I : Finset (Fin u)) (f : Fin u → Fin N)
    (hd : ∀ j, deg E G π (f j) ≠ 0) (hdn : d ≤ n) :
    |kernel E G π I f| ^ d ≤ Real.exp ((2 : ℝ)^u*n*env E G π f) := by
  have hw := env_nonneg E G π f
  have hA : 0 ≤ (2 : ℝ)^u*env E G π f := mul_nonneg (by positivity) hw
  calc
    _ ≤ (1+(2 : ℝ)^u*env E G π f)^d := pow_le_pow_left₀ (abs_nonneg _)
      (kernel_abs_le E G π hs f hd I) d
    _ ≤ (Real.exp ((2 : ℝ)^u*env E G π f))^d := pow_le_pow_left₀ (by linarith)
      (by simpa [add_comm] using Real.add_one_le_exp ((2 : ℝ)^u*env E G π f)) d
    _ = Real.exp ((2 : ℝ)^u*env E G π f*d) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh : (d : ℝ) ≤ n := by exact_mod_cast hdn
      nlinarith

theorem phi_retained_le {u d n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π : Fin N → ℝ)
    (hp : ∀ y, 0 ≤ π y) (hs : ∑ y, π y = 1) (R : Finset (Fin u)) (f : Fin u → Fin N)
    (hd : ∀ j, 0 < deg E G π (f j)) (hdn : d ≤ n) :
    |phiU E G π d u f| ≤ (2 : ℝ)^u *
      Real.exp ((2 : ℝ)^R.card*n*env E G π (retainedTuple R (fun j => f j))) *
      ∏ j ∈ Rᶜ, ((deg E G π (f j))⁻¹)^d := by
  let z := retainedTuple R (fun j => f j)
  have hdz (j : Fin R.card) : 0 < deg E G π (z j) := hd (R.equivFin.symm j).val
  have hpoint (I : Finset (Fin u)) :
      |(-1 : ℝ)^(u-I.card) * (kernel E G π I f)^d| ≤
      Real.exp ((2 : ℝ)^R.card*n*env E G π z) * ∏ j ∈ Rᶜ, ((deg E G π (f j))⁻¹)^d := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
      abs_of_nonneg (kernel_nonneg E G π hp I f hd)]
    have hkp := kernel_pow_le_exp E G π hs (retainedSet R I) z (fun j => (hdz j).ne') hdn
    rw [abs_of_nonneg (kernel_nonneg E G π hp (retainedSet R I) z hdz)] at hkp
    calc
      _ ≤ (kernel E G π (I∩R) f * ∏ j ∈ Rᶜ, (deg E G π (f j))⁻¹)^d :=
        pow_le_pow_left₀ (kernel_nonneg E G π hp I f hd) (kernel_omit_le E G π hp hs I R f hd) d
      _ = (kernel E G π (I∩R) f)^d * ∏ j ∈ Rᶜ, ((deg E G π (f j))⁻¹)^d := by rw [mul_pow, Finset.prod_pow]
      _ ≤ _ := by
        rw [kernel_retainedSet]
        exact mul_le_mul_of_nonneg_right hkp (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hd j).le) d))
  unfold phiU
  change |∑ I : Finset (Fin u), (-1 : ℝ)^(u-I.card) * (kernel E G π I f)^d| ≤ _
  calc
    _ ≤ ∑ I : Finset (Fin u), |(-1 : ℝ)^(u-I.card) * (kernel E G π I f)^d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _I : Finset (Fin u), Real.exp ((2 : ℝ)^R.card*n*env E G π z) *
        ∏ j ∈ Rᶜ, ((deg E G π (f j))⁻¹)^d := Finset.sum_le_sum (fun I _ => hpoint I)
    _ = _ := by simp [Fintype.card_finset, z, mul_assoc]

theorem retained_sum_eq {u N : ℕ} (σ : Fin N → ℝ) (R : Finset (Fin u))
    (H : (Fin R.card → Fin N) → ℝ) :
    (∑ z : R → Fin N, (∏ j, σ (z j)) * H (retainedTuple R z)) =
    ∑ f : Fin R.card → Fin N, tupWt σ f * H f := by
  let e : (R → Fin N) ≃ (Fin R.card → Fin N) := Equiv.arrowCongr R.equivFin (Equiv.refl (Fin N))
  apply Fintype.sum_equiv e
  intro z
  have he : e z = retainedTuple R z := rfl
  rw [he]
  congr 1
  unfold tupWt
  apply Fintype.prod_equiv R.equivFin
  intro j
  simp [retainedTuple]

theorem inner_outer_sum (n : ℕ) : Fintype.card (InnerCoord n) + Fintype.card (OuterCoord n) = n := by
  have hc := Fintype.card_subtype_compl (α := Fin n) (fun j => j.val < hIn n)
  have ho : Fintype.card (OuterCoord n) = n-Fintype.card (InnerCoord n) := by
    simpa [OuterCoord, InnerCoord, Nat.not_lt] using hc
  have hi : Fintype.card (InnerCoord n) ≤ n := by
    simpa using Fintype.card_le_of_injective (fun j : InnerCoord n => j.1) Subtype.val_injective
  omega

theorem sigma_charged_atom {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (π σ : Fin N → ℝ) (hπ : ∑ y, π y = 1) (hσ : ∀ x, 0 ≤ σ x)
    (host : 2^n ≤ N) (hb : bS n ≤ 1/8)
    (cap : ∀ x, (N : ℝ)*σ x ≤ Real.exp ((Real.log 2-gS n/2)*Fintype.card (InnerCoord n)))
    (x : Fin N) (hm : |sMean E G π x| ≤ 4*bS n) :
    σ x * ((deg E G π x)⁻¹)^Fintype.card (OuterCoord n) ≤
      Real.exp (-gS n*Fintype.card (InnerCoord n)/2 + 8*(n : ℝ)*bS n) := by
  let d := Fintype.card (OuterCoord n)
  let h := Fintype.card (InnerCoord n)
  have hdim : h+d=n := inner_outer_sum n
  have hdn : (d : ℝ) ≤ n := by exact_mod_cast (by omega : d ≤ n)
  have hb0 : 0 ≤ bS n := by unfold bS; positivity
  have hd := inverse_degree_le E G π hπ (bS n) hb0 hb x hm
  have hdpow : ((deg E G π x)⁻¹)^d ≤ (2 : ℝ)^d * Real.exp (8*(n : ℝ)*bS n) := by
    calc
      _ ≤ (2*Real.exp (8*bS n))^d := pow_le_pow_left₀ (inv_nonneg.mpr hd.1.le) hd.2 d
      _ = (2 : ℝ)^d*Real.exp (8*bS n*d) := by rw [mul_pow, ← Real.exp_nat_mul]; congr 1; congr 1; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith
  have hcap : Real.exp ((Real.log 2-gS n/2)*h) =
      (2 : ℝ)^h * Real.exp (-gS n*h/2) := by
    rw [show (Real.log 2-gS n/2)*(h : ℝ) = Real.log 2*h + (-gS n*h/2) by ring,
      Real.exp_add]
    congr 1
    rw [mul_comm (Real.log 2), Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ)<2)]
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (Nat.two_pow_pos n) host)
  have hhost : (2 : ℝ)^n ≤ N := by exact_mod_cast host
  apply (mul_le_mul_iff_right₀ hN0).mp
  calc
    (N : ℝ)*(σ x*((deg E G π x)⁻¹)^d) = ((N : ℝ)*σ x)*((deg E G π x)⁻¹)^d := by ring
    _ ≤ Real.exp ((Real.log 2-gS n/2)*h) * ((2 : ℝ)^d*Real.exp (8*(n : ℝ)*bS n)) :=
      mul_le_mul (cap x) hdpow (pow_nonneg (inv_nonneg.mpr hd.1.le) _) (Real.exp_nonneg _)
    _ = (2 : ℝ)^n * Real.exp (-gS n*h/2 + 8*(n : ℝ)*bS n) := by
      rw [hcap, Real.exp_add]
      have hpow : (2 : ℝ)^h*(2 : ℝ)^d = (2 : ℝ)^n := by rw [← pow_add, hdim]
      calc
        _ = ((2 : ℝ)^h*(2 : ℝ)^d) * (Real.exp (-gS n*h/2)*Real.exp (8*(n : ℝ)*bS n)) := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_right hhost (Real.exp_nonneg _)

end HypercubeRamsey.S11.Core.OuterMoment_sol_s11_range
