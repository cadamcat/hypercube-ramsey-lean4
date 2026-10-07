import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.S07.GeometryNodes
import HypercubeRamsey.S03.Height.Scale
import HypercubeRamsey.Tools.Binomial
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
Lane-local finite-cube lemmas used by the L8.1 grid proofs.
-/

namespace HypercubeRamsey.S08

open OAI.HypercubeRamsey

theorem hammingBall_card_le_sum_choose {d R : ℕ} (v : CubeVertex d) :
    (hammingBall v R).card ≤ ∑ j ∈ Finset.range (R + 1), Nat.choose d j := by
  classical
  let support : CubeVertex d → Finset (Fin d) := fun u =>
    Finset.univ.filter (fun i => u i ≠ v i)
  let B := hammingBall v R
  let Q := (Finset.univ : Finset (Fin d)).powerset.filter (fun s => s.card ≤ R)
  have hsupportDist (u : CubeVertex d) : (support u).card = hammingDist v u := by
    simp [support, hammingDist, ne_comm]
  have hinj : Set.InjOn support (B : Set (CubeVertex d)) := by
    intro x hx y hy hxy
    funext i
    have hiff : x i ≠ v i ↔ y i ≠ v i := by
      have h := congrArg (fun s : Finset (Fin d) => i ∈ s) hxy
      simpa [support] using h
    cases hv : v i <;> cases hxv : x i <;> cases hyv : y i <;> simp_all
  have hsubset : B.image support ⊆ Q := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    have hu' : u ∈ hammingBall v R := by simpa [B] using hu
    have hdistle : hammingDist v u ≤ R := (Finset.mem_filter.mp hu').2
    rw [hsupportDist]
    exact hdistle
  have hcard : B.card ≤ Q.card := by
    calc
      B.card = (B.image support).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsubset
  have hQsum : Q.card =
      ∑ k ∈ Finset.range (d + 1), if k ≤ R then Nat.choose d k else 0 := by
    calc
      Q.card = ∑ s ∈ (Finset.univ : Finset (Fin d)).powerset,
          if s.card ≤ R then 1 else 0 := by
        simpa [Q] using
          (Finset.natCast_card_filter (R := ℕ)
            (p := fun s : Finset (Fin d) => s.card ≤ R)
            (s := (Finset.univ : Finset (Fin d)).powerset))
      _ = ∑ k ∈ Finset.range (d + 1),
          Nat.choose d k * (if k ≤ R then 1 else 0) := by
        simpa [Fintype.card_fin, nsmul_eq_mul] using
          (Finset.sum_powerset_apply_card
            (f := fun k : ℕ => if k ≤ R then (1 : ℕ) else 0)
            (x := (Finset.univ : Finset (Fin d))))
      _ = _ := by simp
  let S := (Finset.range (d + 1)).filter (fun j => j ≤ R)
  have hQtoS : Q.card = ∑ j ∈ S, Nat.choose d j := by
    rw [hQsum]
    simp [S, Finset.sum_filter]
  have hSsub : S ⊆ Finset.range (R + 1) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj')
  have hsum : (∑ j ∈ S, Nat.choose d j) ≤
      ∑ j ∈ Finset.range (R + 1), Nat.choose d j :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub (by intros; exact Nat.zero_le _)
  calc
    (hammingBall v R).card = B.card := rfl
    _ ≤ Q.card := hcard
    _ = ∑ j ∈ S, Nat.choose d j := hQtoS
    _ ≤ ∑ j ∈ Finset.range (R + 1), Nat.choose d j := hsum

theorem cubeVertex_eq_of_prefix_suffix {n m : ℕ} (hmn : m ≤ n)
    {v w : CubeVertex n}
    (hprefix : ∀ i : Fin m, v (Fin.castLE hmn i) = w (Fin.castLE hmn i))
    (hsuffix : ∀ j : Fin (n - m),
      v ⟨m + j.val, by have hj := j.isLt; omega⟩ =
        w ⟨m + j.val, by have hj := j.isLt; omega⟩) :
    v = w := by
  funext i
  by_cases hi : i.val < m
  · let j : Fin m := ⟨i.val, hi⟩
    have hj := hprefix j
    have hji : Fin.castLE hmn j = i := by
      apply Fin.ext
      rfl
    simpa only [hji] using hj
  · let j : Fin (n - m) := ⟨i.val - m, by omega⟩
    have hj := hsuffix j
    have hji : (⟨m + j.val, by have hj' := j.isLt; omega⟩ : Fin n) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [hji] using hj

theorem natDist_sum_one_decomp {s : ℕ} (g u : Fin s → ℕ)
    (h : (∑ r : Fin s, Nat.dist (g r) (u r)) = 1) :
    ∃ r : Fin s, Nat.dist (g r) (u r) = 1 ∧ ∀ q, q ≠ r → g q = u q := by
  classical
  have hne : (∑ r : Fin s, Nat.dist (g r) (u r)) ≠ 0 := by rw [h]; decide
  obtain ⟨r, hrmem, hrne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hrpos : 0 < Nat.dist (g r) (u r) := Nat.pos_of_ne_zero hrne
  have hrle : Nat.dist (g r) (u r) ≤ 1 := by
    let term : Fin s → ℕ := fun q => Nat.dist (g q) (u q)
    calc
      Nat.dist (g r) (u r) ≤ ∑ q : Fin s, Nat.dist (g q) (u q) :=
        Finset.single_le_sum (s := Finset.univ) (f := term)
          (fun q hq => Nat.zero_le (term q)) hrmem
      _ = 1 := h
  have hrone : Nat.dist (g r) (u r) = 1 := by omega
  refine ⟨r, hrone, ?_⟩
  intro q hqr
  have hqzero : Nat.dist (g q) (u q) = 0 := by
    by_contra hqne
    have hqpos : 0 < Nat.dist (g q) (u q) := Nat.pos_of_ne_zero hqne
    have hpair : (∑ x ∈ ({r, q} : Finset (Fin s)), Nat.dist (g x) (u x)) ≤ 1 := by
      calc
        (∑ x ∈ ({r, q} : Finset (Fin s)), Nat.dist (g x) (u x)) ≤
            ∑ x : Fin s, Nat.dist (g x) (u x) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
        _ = 1 := h
    have hpairEq :
        (∑ x ∈ ({r, q} : Finset (Fin s)), Nat.dist (g x) (u x)) =
          Nat.dist (g r) (u r) + Nat.dist (g q) (u q) := by
      rw [Finset.sum_pair hqr.symm]
    rw [hpairEq, hrone] at hpair
    omega
  exact Nat.eq_of_dist_eq_zero hqzero

theorem keyDistOne_card_bound {s q : ℕ} (g : Fin s → Fin q) :
    (Finset.univ.filter (fun u : Fin s → Fin q =>
      (∑ r : Fin s, Nat.dist (g r).val (u r).val) = 1)).card ≤ 2 * s := by
  classical
  let P := Finset.univ.filter (fun u : Fin s → Fin q =>
    (∑ r : Fin s, Nat.dist (g r).val (u r).val) = 1)
  letI : Fintype {u : Fin s → Fin q // u ∈ P} := Fintype.subtype P (by intro u; simp)
  have hsum (u : {u : Fin s → Fin q // u ∈ P}) :
      (∑ r : Fin s, Nat.dist (g r).val (u.1 r).val) = 1 := by
    simpa [P] using (Finset.mem_filter.mp u.2).2
  let coord (u : {u : Fin s → Fin q // u ∈ P}) : Fin s :=
    Classical.choose (natDist_sum_one_decomp (fun r => (g r).val) (fun r => (u.1 r).val) (hsum u))
  have hcoord (u : {u : Fin s → Fin q // u ∈ P}) :
      Nat.dist (g (coord u)).val (u.1 (coord u)).val = 1 ∧
        ∀ r, r ≠ coord u → (g r).val = (u.1 r).val :=
    Classical.choose_spec
      (natDist_sum_one_decomp (fun r => (g r).val) (fun r => (u.1 r).val) (hsum u))
  let code (u : {u : Fin s → Fin q // u ∈ P}) : Fin s × Bool :=
    (coord u, decide ((g (coord u)).val < (u.1 (coord u)).val))
  have hcode : Function.Injective code := by
    intro u v huv
    apply Subtype.ext
    have hcoordEq : coord u = coord v := congrArg Prod.fst huv
    have hdirBool : decide ((g (coord u)).val < (u.1 (coord u)).val) =
        decide ((g (coord u)).val < (v.1 (coord u)).val) := by
      have h := congrArg Prod.snd huv
      change decide ((g (coord u)).val < (u.1 (coord u)).val) =
        decide ((g (coord v)).val < (v.1 (coord v)).val) at h
      rw [← hcoordEq] at h
      exact h
    funext r
    by_cases hqr : r = coord u
    · subst r
      have hdistU : Nat.dist (g (coord u)).val (u.1 (coord u)).val = 1 := (hcoord u).1
      have hdistV : Nat.dist (g (coord u)).val (v.1 (coord u)).val = 1 := by
        simpa [hcoordEq] using (hcoord v).1
      by_cases hltU : (g (coord u)).val < (u.1 (coord u)).val
      · have hltV : (g (coord u)).val < (v.1 (coord u)).val := by
          have hdecU : decide ((g (coord u)).val < (u.1 (coord u)).val) = true := by simp [hltU]
          have hdecV : decide ((g (coord u)).val < (v.1 (coord u)).val) = true := by
            rw [← hdirBool]
            exact hdecU
          exact of_decide_eq_true hdecV
        apply Fin.ext
        unfold Nat.dist at hdistU hdistV
        omega
      · have hltV : ¬ (g (coord u)).val < (v.1 (coord u)).val := by
          intro hltV
          have hdecU : decide ((g (coord u)).val < (u.1 (coord u)).val) = false := by simp [hltU]
          have hdecV : decide ((g (coord u)).val < (v.1 (coord u)).val) = true := by simp [hltV]
          rw [hdirBool] at hdecU
          rw [hdecV] at hdecU
          contradiction
        apply Fin.ext
        unfold Nat.dist at hdistU hdistV
        omega
    · have hqU : r ≠ coord u := hqr
      have hqV : r ≠ coord v := by
        intro h
        exact hqr (h.trans hcoordEq.symm)
      have huq := (hcoord u).2 r hqU
      have hvq := (hcoord v).2 r hqV
      apply Fin.ext
      calc
        (u.1 r).val = (g r).val := huq.symm
        _ = (v.1 r).val := hvq
  have hsource : Fintype.card {u : Fin s → Fin q // u ∈ P} = P.card :=
    Fintype.card_of_subtype P (by intro u; simp)
  have htarget : Fintype.card (Fin s × Bool) = s * 2 := by simp
  calc
    P.card = Fintype.card {u : Fin s → Fin q // u ∈ P} := hsource.symm
    _ ≤ Fintype.card (Fin s × Bool) := Fintype.card_le_of_injective code hcode
    _ = s * 2 := htarget
    _ = 2 * s := by omega

theorem scaleIndex_exists_grid (M R target : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R) :
    ∃ i : ℕ, target ≤ M ^ i * R := by
  have hM0 : M ≠ 0 := by omega
  induction target with
  | zero => exact ⟨0, by simp⟩
  | succ target ih =>
      obtain ⟨i, hi⟩ := ih
      let x := M ^ i * R
      have hx0 : x ≠ 0 := by
        dsimp [x]
        exact Nat.mul_ne_zero (pow_ne_zero _ hM0) (by omega)
      have hx : 1 ≤ x := by omega
      have hstep : x + 1 ≤ 2 * x := by omega
      have hmult : 2 * x ≤ M * x := Nat.mul_le_mul_right x hM
      refine ⟨i + 1, ?_⟩
      calc
        target + 1 ≤ x + 1 := Nat.succ_le_succ hi
        _ ≤ 2 * x := hstep
        _ ≤ M * x := hmult
        _ = M ^ (i + 1) * R := by dsimp [x]; rw [pow_succ]; ring

theorem findScale_le_mul_target (M R target : ℕ)
    (hP : ∃ i : ℕ, target ≤ M ^ i * R) (hM : 2 ≤ M) (hR : 1 ≤ R)
    (hRT : R ≤ target) : M ^ Nat.find hP * R ≤ M * target := by
  have hspec : target ≤ M ^ Nat.find hP * R := Nat.find_spec hP
  by_cases hi : Nat.find hP = 0
  · have hEq : R = target := by
      have hle : target ≤ R := by simpa [hi] using hspec
      exact Nat.le_antisymm hRT hle
    rw [hi, hEq, pow_zero, one_mul]
    calc
      target = 1 * target := by simp
      _ ≤ M * target := Nat.mul_le_mul_right target (by omega)
  · have hpos : 1 ≤ Nat.find hP := by omega
    have hpowEq : M ^ Nat.find hP = M ^ (Nat.find hP - 1 + 1) := by
      rw [Nat.sub_add_cancel hpos]
    have hprev : ¬ target ≤ M ^ (Nat.find hP - 1) * R :=
      Nat.find_min hP (by omega)
    have hlt : M ^ (Nat.find hP - 1) * R < target := Nat.lt_of_not_ge hprev
    have hpow : M ^ Nat.find hP * R = M * (M ^ (Nat.find hP - 1) * R) := by
      calc
        M ^ Nat.find hP * R = M ^ ((Nat.find hP - 1) + 1) * R := by rw [hpowEq]
        _ = (M ^ (Nat.find hP - 1) * M) * R := by rw [pow_succ]
        _ = M * (M ^ (Nat.find hP - 1) * R) := by ring
    rw [hpow]
    exact Nat.mul_le_mul_left M hlt.le

theorem topScale_eq_grid_formula (n : ℕ) (σ ζ : ℝ) :
    topScale n σ ζ =
      (max 2 ⌈(n : ℝ) ^ σ⌉₊) ^ Nat.find
        (scaleIndex_exists_grid (max 2 ⌈(n : ℝ) ^ σ⌉₊)
          (max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊) ⌈(n : ℝ) ^ (1 - ζ)⌉₊
          (by omega) (by omega)) * max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ := by
  unfold topScale
  congr 1

theorem topScale_le_mul_target (n : ℕ) (σ ζ : ℝ)
    (hR0 : max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ ⌈(n : ℝ) ^ (1 - ζ)⌉₊) :
    topScale n σ ζ ≤ (max 2 ⌈(n : ℝ) ^ σ⌉₊) * ⌈(n : ℝ) ^ (1 - ζ)⌉₊ := by
  let R₀ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hM : 2 ≤ M := by simp [M]
  have hR : 1 ≤ R₀ := by simp [R₀]
  rw [topScale_eq_grid_formula]
  exact findScale_le_mul_target M R₀ target
    (scaleIndex_exists_grid M R₀ target hM hR) hM hR (by simpa [R₀, target] using hR0)

namespace Lane_q_s08_grid

theorem choose_range_entropy_quarter {d R : ℕ}
    (hR : (R : ℝ) ≤ (d : ℝ) / 4) :
    (∑ j ∈ Finset.range (R + 1), (Nat.choose d j : ℝ)) ≤
      Real.exp (Real.binEntropy (1 / 4 : ℝ) * d) := by
  classical
  have hRle : R ≤ d := by
    have hR' : (R : ℝ) ≤ (d : ℝ) := by nlinarith [hR]
    exact_mod_cast hR'
  let T : Finset ℕ :=
    (Finset.range (d + 1)).filter (fun j => (j : ℝ) ≤ (1 / 4 : ℝ) * d)
  have hsub : Finset.range (R + 1) ⊆ T := by
    intro j hj
    have hjR : j ≤ R := by simpa using (Finset.mem_range.mp hj)
    have hjd : j ≤ d := le_trans hjR hRle
    have hjBound : (j : ℝ) ≤ (1 / 4 : ℝ) * d := by
      have hjCast : (j : ℝ) ≤ R := by exact_mod_cast hjR
      have hRCast : (R : ℝ) ≤ (1 / 4 : ℝ) * d := by
        nlinarith [hR]
      exact hjCast.trans hRCast
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjBound⟩
  have hsum :
      (∑ j ∈ Finset.range (R + 1), (Nat.choose d j : ℝ)) ≤
        ∑ j ∈ T, (Nat.choose d j : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro j hj hjT; positivity)
  have hT :
      (∑ j ∈ T, (Nat.choose d j : ℝ)) =
        ∑ k ∈ Finset.univ.filter
          (fun k : Fin (d + 1) => (k.val : ℝ) ≤ (1 / 4 : ℝ) * d),
            (Nat.choose d k.val : ℝ) := by
    let f : ℕ → ℝ := fun j =>
      if (j : ℝ) ≤ (1 / 4 : ℝ) * d then (Nat.choose d j : ℝ) else 0
    let g : Fin (d + 1) → ℝ := fun k =>
      if (k.val : ℝ) ≤ (1 / 4 : ℝ) * d then (Nat.choose d k.val : ℝ) else 0
    calc
      (∑ j ∈ T, (Nat.choose d j : ℝ)) = ∑ j ∈ Finset.range (d + 1), f j := by
        simp [T, f, Finset.sum_filter]
      _ = ∑ k : Fin (d + 1), g k := by
        rw [← Fin.sum_univ_eq_sum_range f (d + 1)]
      _ = ∑ k ∈ Finset.univ.filter
          (fun k : Fin (d + 1) => (k.val : ℝ) ≤ (1 / 4 : ℝ) * d),
            (Nat.choose d k.val : ℝ) := by
        simp [g, Finset.sum_filter]
  have hEntropy := _root_.HypercubeRamsey.binomialEntropyBound d (1 / 4 : ℝ)
    (by norm_num) (by norm_num)
  rw [← hT] at hEntropy
  exact hsum.trans hEntropy

theorem binEntropy_quarter_gap :
    Real.binEntropy (1 / 4 : ℝ) ≤ Real.log 2 - 1 / 20 := by
  have hlog43 : Real.log ((4 : ℝ) / 3) ≤ 1 / 3 := by
    have h := Real.log_le_sub_one_of_pos (x := (4 : ℝ) / 3) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log (2 * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 := by rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 2 := by ring
  have hform : Real.binEntropy (1 / 4 : ℝ) =
      (1 / 2 : ℝ) * Real.log 2 + (3 / 4 : ℝ) * Real.log ((4 : ℝ) / 3) := by
    rw [Real.binEntropy, show (1 / 4 : ℝ)⁻¹ = 4 by norm_num,
      show 1 - (1 / 4 : ℝ) = 3 / 4 by norm_num,
      show (3 / 4 : ℝ)⁻¹ = (4 : ℝ) / 3 by norm_num, hlog4]
    ring
  rw [hform]
  have hlog2 : (3 / 5 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  nlinarith

end Lane_q_s08_grid

end HypercubeRamsey.S08
