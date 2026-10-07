import HypercubeRamsey.S12.Defs

namespace HypercubeRamsey.S12.Exceptional_q_s12_exc

open HypercubeRamsey
open Classical
open scoped BigOperators

theorem sum_subset_le {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hst : s ⊆ t) (hf : ∀ x ∈ t, 0 ≤ f x) :
    ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun x hx _ => hf x hx)

theorem sum_union_le {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have hdis : Disjoint (s \ t) t := by
    rw [Finset.disjoint_left]
    intro x hx ht
    exact (Finset.mem_sdiff.mp hx).2 ht
  have hunion : (s \ t) ∪ t = s ∪ t := by
    ext x
    simp [Finset.mem_sdiff, Finset.mem_union]
  rw [← hunion, Finset.sum_union hdis]
  have hsub : s \ t ⊆ s := Finset.sdiff_subset
  have hs : ∑ x ∈ s \ t, f x ≤ ∑ x ∈ s, f x :=
    sum_subset_le (s \ t) s f hsub (fun x hx => hf x)
  linarith

theorem dens_eq_rowDegree_sum {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) :
    dens E c μ ν = ∑ x, μ.w x * deg E c ν.w x := by
  classical
  unfold dens deg
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [hit]
  ring

theorem dens_eq_colDegree_sum {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) :
    dens E c μ ν = ∑ y, ν.w y * (∑ x, μ.w x * hit E c x y) := by
  classical
  unfold dens
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [hit]
  ring

lemma law_N_pos {N : ℕ} (μ : Law N) : (0 : ℝ) < N := by
  have hN0 : (N : ℝ) ≠ 0 := by
    intro hzero
    have hNat : N = 0 := Nat.cast_eq_zero.mp hzero
    subst N
    have hsum := μ.sum_eq_one
    simp at hsum
  exact lt_of_le_of_ne (Nat.cast_nonneg N) (Ne.symm hN0)

theorem width_mono {N : ℕ} {μ : Law N} {s t : ℝ}
    (hμ : μ.WidthLE s) (hst : s ≤ t) : μ.WidthLE t := by
  intro x
  exact le_trans (hμ x) (div_le_div_of_nonneg_right
    (Real.exp_le_exp.mpr hst) (by positivity))

theorem width_restrict {N : ℕ} (μ : Law N) (S : Finset (Fin N)) {s : ℝ}
    (hm : 0 < ∑ x ∈ S, μ.w x) (hμ : μ.WidthLE s) :
    (μ.restrict S hm).WidthLE (s - Real.log (∑ x ∈ S, μ.w x)) := by
  have hN : 0 < (N : ℝ) := law_N_pos μ
  intro x
  by_cases hx : x ∈ S
  · change (if x ∈ S then μ.w x / (∑ y ∈ S, μ.w y) else 0) ≤ _
    rw [if_pos hx]
    calc
      μ.w x / (∑ y ∈ S, μ.w y) ≤ (Real.exp s / N) / (∑ y ∈ S, μ.w y) :=
        div_le_div_of_nonneg_right (hμ x) (le_of_lt hm)
      _ = Real.exp (s - Real.log (∑ y ∈ S, μ.w y)) / N := by
        rw [Real.exp_sub, Real.exp_log hm]
        field_simp [ne_of_gt hN, ne_of_gt hm]
  · change (if x ∈ S then μ.w x / (∑ y ∈ S, μ.w y) else 0) ≤ _
    rw [if_neg hx]
    positivity

theorem cond_widthLE {N : ℕ} (μ : Law N) (S : Finset (Fin N))
    (hm : 0 < ∑ x ∈ S, μ.w x) {s : ℝ} (hμ : μ.WidthLE s) :
    (μ.cond S hm).WidthLE (s + Real.log (1 / ∑ x ∈ S, μ.w x)) := by
  change (μ.restrict S hm).WidthLE _
  rw [one_div, Real.log_inv]
  convert width_restrict μ S hm hμ using 1 <;> ring

noncomputable def tiltMass {N : ℕ} (π : Law N) (f : Fin N → ℝ) : ℝ :=
  ∑ y, π.w y * (f y + 2)

theorem tiltMass_bounds {N : ℕ} (π : Law N) (f : Fin N → ℝ)
    (hf : ∀ y, |f y| ≤ 1) :
    1 ≤ tiltMass π f ∧ tiltMass π f ≤ 3 := by
  constructor
  · unfold tiltMass
    calc
      1 = ∑ y, π.w y := π.sum_eq_one.symm
      _ ≤ ∑ y, π.w y * (f y + 2) := by
        apply Finset.sum_le_sum
        intro y hy
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ f y + 2 by rcases abs_le.mp (hf y) with ⟨hlo, hhi⟩; linarith)
          (π.nonneg y)
  · unfold tiltMass
    calc
      ∑ y, π.w y * (f y + 2) ≤ ∑ y, π.w y * 3 := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left
          (show f y + 2 ≤ 3 by rcases abs_le.mp (hf y) with ⟨hlo, hhi⟩; linarith)
          (π.nonneg y)
      _ = 3 := by rw [← Finset.sum_mul, π.sum_eq_one]; ring

noncomputable def tiltLaw {N : ℕ} (π : Law N) (f : Fin N → ℝ)
    (hf : ∀ y, |f y| ≤ 1) : Law N where
  w y := π.w y * (f y + 2) / tiltMass π f
  nonneg y := by
    apply div_nonneg
    · exact mul_nonneg (π.nonneg y)
        (show (0 : ℝ) ≤ f y + 2 by rcases abs_le.mp (hf y) with ⟨hlo, hhi⟩; linarith)
    · exact le_of_lt (lt_of_lt_of_le zero_lt_one (tiltMass_bounds π f hf).1)
  sum_eq_one := by
    have hZ : 0 < tiltMass π f := lt_of_lt_of_le zero_lt_one (tiltMass_bounds π f hf).1
    rw [← Finset.sum_div]
    change tiltMass π f / tiltMass π f = 1
    exact div_self hZ.ne'

theorem tiltLaw_supported {N : ℕ} (π : Law N) (f : Fin N → ℝ)
    (hf : ∀ y, |f y| ≤ 1) (Y : Finset (Fin N))
    (hπ : π.SupportedIn Y) : (tiltLaw π f hf).SupportedIn Y := by
  intro y hy
  simp [tiltLaw, hπ y hy]

theorem tiltLaw_width {N : ℕ} (π : Law N) (f : Fin N → ℝ)
    (hf : ∀ y, |f y| ≤ 1) {w₁ : ℝ}
    (hπw : π.WidthLE (w₁ - Real.log 3)) :
    (tiltLaw π f hf).WidthLE w₁ := by
  have hZ := tiltMass_bounds π f hf
  have hZpos : 0 < tiltMass π f := lt_of_lt_of_le zero_lt_one hZ.1
  have hN : 0 < (N : ℝ) := law_N_pos π
  have hEq : 3 * (Real.exp (w₁ - Real.log 3) / N) = Real.exp w₁ / N := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    field_simp [ne_of_gt hN]
  intro y
  change π.w y * (f y + 2) / tiltMass π f ≤ Real.exp w₁ / N
  have hnum : π.w y * (f y + 2) ≤ 3 * π.w y := by
    calc
      π.w y * (f y + 2) ≤ π.w y * 3 := mul_le_mul_of_nonneg_left
        (show f y + 2 ≤ 3 by rcases abs_le.mp (hf y) with ⟨hlo, hhi⟩; linarith)
        (π.nonneg y)
      _ = 3 * π.w y := by ring
  have hquot : π.w y * (f y + 2) / tiltMass π f ≤ 3 * π.w y := by
    apply (div_le_iff₀ hZpos).2
    calc
      π.w y * (f y + 2) ≤ 3 * π.w y := hnum
      _ = (3 * π.w y) * 1 := by ring
      _ ≤ (3 * π.w y) * tiltMass π f :=
        mul_le_mul_of_nonneg_left hZ.1 (mul_nonneg (by norm_num) (π.nonneg y))
  calc
    π.w y * (f y + 2) / tiltMass π f ≤ 3 * π.w y := hquot
    _ ≤ 3 * (Real.exp (w₁ - Real.log 3) / N) :=
      mul_le_mul_of_nonneg_left (hπw y) (by norm_num)
    _ = Real.exp w₁ / N := hEq

theorem tilt_expect_identity {N : ℕ} (π : Law N) (f : Fin N → ℝ)
    (hf : ∀ y, |f y| ≤ 1) (g : Fin N → ℝ) :
    tiltMass π f *
        ((∑ y, (tiltLaw π f hf).w y * g y) - ∑ y, π.w y * g y) =
      ∑ y, π.w y * f y * (g y - ∑ z, π.w z * g z) := by
  let Z := tiltMass π f
  let D := ∑ y, π.w y * g y
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one (tiltMass_bounds π f hf).1
  have hZne : tiltMass π f ≠ 0 := by
    exact ne_of_gt (by simpa [Z] using hZpos)
  have htilt : Z * (∑ y, (tiltLaw π f hf).w y * g y) =
      ∑ y, π.w y * (f y + 2) * g y := by
    unfold tiltLaw
    dsimp [Z]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    field_simp [hZne]
  have hcancel : ∑ y, π.w y * (g y - D) = 0 := by
    calc
      ∑ y, π.w y * (g y - D) = ∑ y, (π.w y * g y - π.w y * D) := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (∑ y, π.w y * g y) - ∑ y, π.w y * D := by
        simpa using (Finset.sum_sub_distrib (s := Finset.univ)
          (f := fun y => π.w y * g y) (g := fun y => π.w y * D))
      _ = D - D := by
        rw [← Finset.sum_mul, π.sum_eq_one]
        dsimp [D]
        ring
      _ = 0 := sub_self _
  have hsplit :
      ∑ y, π.w y * (f y + 2) * (g y - D) =
        ∑ y, π.w y * f y * (g y - D) := by
    calc
      ∑ y, π.w y * (f y + 2) * (g y - D) =
          (∑ y, π.w y * f y * (g y - D)) +
            2 * ∑ y, π.w y * (g y - D) := by
          calc
            ∑ y, π.w y * (f y + 2) * (g y - D) =
                ∑ y, (π.w y * f y * (g y - D) +
                  2 * (π.w y * (g y - D))) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
            _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [hcancel]; ring
  calc
    Z * ((∑ y, (tiltLaw π f hf).w y * g y) - ∑ y, π.w y * g y) =
        Z * (∑ y, (tiltLaw π f hf).w y * g y) - Z * D := by
          dsimp [D]
          ring
    _ = (∑ y, π.w y * (f y + 2) * g y) -
        (∑ y, π.w y * (f y + 2)) * D := by
          rw [htilt]
          dsimp [Z, tiltMass]
    _ = ∑ y, π.w y * (f y + 2) * (g y - D) := by
          calc
            _ = (∑ y, π.w y * (f y + 2) * g y) -
                ∑ y, π.w y * (f y + 2) * D := by rw [Finset.sum_mul]
            _ = ∑ y, (π.w y * (f y + 2) * g y -
                π.w y * (f y + 2) * D) := by
                  symm
                  simpa using (Finset.sum_sub_distrib (s := Finset.univ)
                    (f := fun y => π.w y * (f y + 2) * g y)
                    (g := fun y => π.w y * (f y + 2) * D))
            _ = _ := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  ring
    _ = ∑ y, π.w y * f y * (g y - D) := hsplit
    _ = ∑ y, π.w y * f y * (g y - ∑ z, π.w z * g z) := by rfl

theorem tilt_degree_identity {N : ℕ} (π : Law N) (f : Fin N → ℝ)
    (hf : ∀ y, |f y| ≤ 1) (E : Fin N → Fin N → Prop) (c : Colour)
    (x : Fin N) :
    tiltMass π f * (deg E c (tiltLaw π f hf).w x - deg E c π.w x) =
      ∑ y, π.w y * f y * (hit E c x y - deg E c π.w x) := by
  simpa [deg] using tilt_expect_identity π f hf (fun y => hit E c x y)

theorem tilt_colDegree_identity {N : ℕ} (π : Law N) (f : Fin N → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (E : Fin N → Fin N → Prop) (c : Colour)
    (y : Fin N) :
    tiltMass π f *
        ((∑ x, (tiltLaw π f hf).w x * hit E c x y) -
          ∑ x, π.w x * hit E c x y) =
      ∑ x, π.w x * f x * (hit E c x y - ∑ z, π.w z * hit E c z y) := by
  simpa using tilt_expect_identity π f hf (fun x => hit E c x y)

end HypercubeRamsey.S12.Exceptional_q_s12_exc
