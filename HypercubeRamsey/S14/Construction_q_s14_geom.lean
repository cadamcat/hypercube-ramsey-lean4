import HypercubeRamsey.PartC.SliceSolver
import HypercubeRamsey.S10.Projection
import HypercubeRamsey.S15.Defs
import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.S10.FixedList

namespace HypercubeRamsey.S14.Geometry_q_s14_geom

open Classical

/-- Binary coordinates identify a dyadic finite index set with the cube of
syndrome bits. -/
noncomputable def coordEquiv {h m : ℕ} (hh : h = 2 ^ m) :
    Fin h ≃ (Fin m → ZMod 2) where
  toFun l j := if l.val.testBit j.val then 1 else 0
  invFun g := Fin.cast hh.symm (Fin.ofBits fun j : Fin m => decide (g j = 1))
  left_inv l := by
    subst h
    apply Fin.ext
    simp only [Fin.cast_eq_self, Fin.val_ofBits]
    have hbits : (fun j : Fin m =>
        decide ((if l.val.testBit j.val then 1 else 0 : ZMod 2) = 1)) =
        fun j => l.val.testBit j.val := by
      funext j
      simp
    rw [hbits, Nat.ofBits_testBit]
    exact Nat.mod_eq_of_lt (by simpa using l.isLt)
  right_inv g := by
    subst h
    funext j
    apply ZMod.val_injective 2
    have hj : j.val < m := j.isLt
    have hval : (g j).val < 2 := (g j).val_lt
    have hcase : (g j).val = 0 ∨ (g j).val = 1 := by omega
    rcases hcase with hzero | hone
    · have hg : g j = 0 := ZMod.val_injective 2 (by simp [hzero])
      rw [hg]
      simp [Nat.testBit_ofBits_lt, hj, hg]
    · have hg : g j = 1 := ZMod.val_injective 2 (by
        rw [ZMod.val_one_eq_one_mod]
        norm_num [hone])
      rw [hg]
      simp [Nat.testBit_ofBits_lt, hj, hg]

noncomputable def coordWord {h m : ℕ} (hh : h = 2 ^ m) (z : Fin h → Bool) :
    (Fin m → ZMod 2) → Bool := fun g => z ((coordEquiv hh).symm g)

noncomputable def wordEquiv {h m : ℕ} (hh : h = 2 ^ m) :
    (Fin h → Bool) ≃ ((Fin m → ZMod 2) → Bool) where
  toFun := coordWord hh
  invFun w l := w (coordEquiv hh l)
  left_inv z := by
    funext l
    simp [coordWord]
  right_inv w := by
    funext g
    simp [coordWord]

theorem coordWord_flip {h m : ℕ} (hh : h = 2 ^ m)
    (z : Fin h → Bool) (l : Fin h) :
    coordWord hh (flipPos z l) =
      HypercubeRamsey.S10.flipChunkBit (coordWord hh z) (coordEquiv hh l) := by
  funext g
  by_cases hg : g = coordEquiv hh l
  · have hsymm : (coordEquiv hh).symm g = l := by rw [hg]; simp
    simp [coordWord, HypercubeRamsey.S10.flipChunkBit, flipPos, hg]
  · have hsymm : (coordEquiv hh).symm g ≠ l := by
      intro h
      apply hg
      calc
        g = coordEquiv hh ((coordEquiv hh).symm g) := (coordEquiv hh).apply_symm_apply g |>.symm
        _ = coordEquiv hh l := congrArg (coordEquiv hh) h
    simp [coordWord, HypercubeRamsey.S10.flipChunkBit, flipPos, hg, hsymm]

theorem chunkSyndrome_flipChunkBit {G : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] (h₂ : ∀ g : G, g + g = 0) (s : G → Bool) (g : G) :
    HypercubeRamsey.S10.chunkSyndrome (HypercubeRamsey.S10.flipChunkBit s g) =
      HypercubeRamsey.S10.chunkSyndrome s + g := by
  unfold HypercubeRamsey.S10.chunkSyndrome
  calc
    (∑ x : G, if HypercubeRamsey.S10.flipChunkBit s g x then x else 0) =
        ∑ x : G, ((if s x then x else 0) + (if x = g then g else 0)) := by
      apply Fintype.sum_congr
      intro x
      by_cases hx : x = g
      · subst x
        by_cases hs : s g <;> simp [HypercubeRamsey.S10.flipChunkBit, hs, h₂]
      · simp [HypercubeRamsey.S10.flipChunkBit, hx]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem wordSyndrome_eq_chunk {h m : ℕ} (hh : h = 2 ^ m)
    (z : Fin h → Bool) (j : Fin m) :
    wordSyndrome z j.val =
      (HypercubeRamsey.S10.chunkSyndrome (coordWord hh z)) j := by
  let e := coordEquiv hh
  have hsum :
      (∑ l : Fin h, if z l = true ∧ l.val.testBit j.val = true then
          (1 : ZMod 2) else 0) =
        ∑ g : Fin m → ZMod 2, if coordWord hh z g = true then g j else 0 := by
    apply Fintype.sum_equiv e
    intro l
    change (if z l = true ∧ l.val.testBit j.val = true then (1 : ZMod 2) else 0) =
      (if z (e.symm (e l)) = true then (e l) j else 0)
    rw [e.symm_apply_apply]
    change (if z l = true ∧ l.val.testBit j.val = true then (1 : ZMod 2) else 0) =
      (if z l = true then (if l.val.testBit j.val then 1 else 0) else 0)
    by_cases hz : z l = true <;> by_cases hb : l.val.testBit j.val = true <;>
      simp [hz, hb]
  have hsumEval :
      (∑ c : Fin m → ZMod 2, if coordWord hh z c = true then c j else 0) =
        ∑ c : Fin m → ZMod 2, (if coordWord hh z c = true then c else 0) j := by
    apply Finset.sum_congr rfl
    intro c hc
    by_cases h : coordWord hh z c = true <;> simp [h]
  calc
    wordSyndrome z j.val =
        ∑ l : Fin h, if z l = true ∧ l.val.testBit j.val = true then
          (1 : ZMod 2) else 0 := rfl
    _ = ∑ g : Fin m → ZMod 2, if coordWord hh z g = true then g j else 0 := hsum
    _ = (HypercubeRamsey.S10.chunkSyndrome (coordWord hh z)) j := by
      unfold HypercubeRamsey.S10.chunkSyndrome
      exact hsumEval.trans (Fintype.sum_apply j
        (fun c : Fin m → ZMod 2 => if coordWord hh z c = true then c else 0)).symm

theorem wordSyndrome_eq_zero_of_ge {h m : ℕ} (hh : h = 2 ^ m)
    (z : Fin h → Bool) {j : ℕ} (hj : m ≤ j) : wordSyndrome z j = 0 := by
  unfold wordSyndrome
  apply Finset.sum_eq_zero
  intro l hl
  have hlt : l.val < 2 ^ j := by
    apply lt_of_lt_of_le l.isLt
    rw [hh]
    exact Nat.pow_le_pow_right (by omega) hj
  have hbit := Nat.testBit_eq_false_of_lt hlt
  simp [hbit]

theorem chunk_zero_iff_word_zero {h m : ℕ} (hh : h = 2 ^ m)
    (z : Fin h → Bool) :
    HypercubeRamsey.S10.chunkSyndrome (coordWord hh z) = 0 ↔ wordSyndrome z = 0 := by
  constructor
  · intro hzero
    funext j
    by_cases hj : j < m
    · let j' : Fin m := ⟨j, hj⟩
      have hcoord := wordSyndrome_eq_chunk hh z j'
      have hzero' := congrFun hzero j'
      exact hcoord.trans hzero'
    · exact wordSyndrome_eq_zero_of_ge hh z (Nat.le_of_not_gt hj)
  · intro hzero
    funext j
    have hcoord := wordSyndrome_eq_chunk hh z j
    exact hcoord.symm.trans (congrFun hzero j.val)

noncomputable def syndromeIndex {h m : ℕ} (hh : h = 2 ^ m)
    (z : Fin h → Bool) : Fin h :=
  (coordEquiv hh).symm (HypercubeRamsey.S10.chunkSyndrome (coordWord hh z))

theorem syndromeIndex_spec {h m : ℕ} (hh : h = 2 ^ m)
    (z : Fin h → Bool) (j : ℕ) :
    ((syndromeIndex hh z).val.testBit j = true ↔ wordSyndrome z j = 1) := by
  by_cases hj : j < m
  · let j' : Fin m := ⟨j, hj⟩
    have hcoord := congrFun
      ((coordEquiv hh).apply_symm_apply
        (HypercubeRamsey.S10.chunkSyndrome (coordWord hh z))) j'
    change (if (syndromeIndex hh z).val.testBit j then (1 : ZMod 2) else 0) =
      (HypercubeRamsey.S10.chunkSyndrome (coordWord hh z)) j' at hcoord
    have hword := wordSyndrome_eq_chunk hh z j'
    constructor
    · intro hbit
      rw [hword]
      rw [← hcoord]
      simp [hbit]
    · intro hval
      have hbitval :
          (if (syndromeIndex hh z).val.testBit j then (1 : ZMod 2) else 0) = 1 := by
        rw [hcoord, ← hword]
        exact hval
      by_cases hbit : (syndromeIndex hh z).val.testBit j = true
      · exact hbit
      · simp [hbit] at hbitval
  · have hlt : (syndromeIndex hh z).val < 2 ^ j := by
      apply lt_of_lt_of_le (syndromeIndex hh z).isLt
      rw [hh]
      exact Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hj)
    have hbit := Nat.testBit_eq_false_of_lt hlt
    have hword := wordSyndrome_eq_zero_of_ge hh z (Nat.le_of_not_gt hj)
    constructor
    · intro h
      simp [hbit] at h
    · intro h
      rw [hword] at h
      simp at h

theorem hammingDist_flipPos {h : ℕ} (z : Fin h → Bool) (l : Fin h) :
    hammingDist z (flipPos z l) = 1 := by
  classical
  have hset : (Finset.univ.filter fun j : Fin h => z j ≠ flipPos z l j) = {l} := by
    ext j
    by_cases hj : j = l
    · subst j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [show flipPos z l l = !z l by simp [flipPos, Function.update_self]]
      cases hz : z l <;> simp [hz]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [show flipPos z l j = z j by
        change Function.update z l (!z l) j = z j
        exact Function.update_of_ne hj (!z l) z]
      simp [hj]
  unfold hammingDist
  rw [hset]
  simp


open scoped BigOperators
open Classical

/-- Integrate a pointwise bound on one coordinate of a finite product law. -/
theorem FinProb.pr_piSplitAt_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (A : (∀ j, Ω j) → Prop) (p : ℝ)
    (hp : 0 ≤ p)
    (hbound : ∀ rest : (∀ j : {j // j ≠ i}, Ω j.1),
      (∑ x, if A ((Equiv.piSplitAt i Ω).symm (x, rest)) then (P i).w x else 0) ≤ p) :
    (FinProb.pi P).pr A ≤ p := by
  classical
  let R : FinProb (∀ j : {j // j ≠ i}, Ω j.1) := FinProb.pi (fun j => P j.1)
  have hprod (x : Ω i) (rest : ∀ j : {j // j ≠ i}, Ω j.1) :
      (∏ j, (P j).w (((Equiv.piSplitAt i Ω).symm (x, rest)) j)) =
        (P i).w x * R.w rest := by
    let f : ι → ℝ := fun j => (P j).w (((Equiv.piSplitAt i Ω).symm (x, rest)) j)
    have hi : (Equiv.piSplitAt i Ω).symm (x, rest) i = x := by
      simp [Equiv.piSplitAt]
    have hrest : (∏ j ∈ Finset.univ.erase i, f j) = R.w rest := by
      have hset : Finset.univ.erase i = Finset.univ.filter (fun j : ι => j ≠ i) := by
        ext j
        simp
      rw [hset]
      rw [← Finset.prod_subtype_eq_prod_filter
        (s := Finset.univ) (p := fun j : ι => j ≠ i)]
      dsimp [R, FinProb.pi]
      have hsub :
          Finset.univ.subtype (fun j : ι => j ≠ i) =
            (Finset.univ : Finset {j // j ≠ i}) := by
        ext j
        simp
      rw [hsub]
      change (∏ j : {j // j ≠ i}, f j.1) = ∏ j : {j // j ≠ i}, (P j.1).w (rest j)
      apply Finset.prod_congr rfl
      intro j hj
      simp [f, Equiv.piSplitAt, j.2]
    calc
      ∏ j, f j = (∏ j ∈ Finset.univ.erase i, f j) * f i := by
        simpa [f] using (Finset.prod_erase_mul Finset.univ f (Finset.mem_univ i)).symm
      _ = (P i).w x * R.w rest := by
        rw [hrest]
        change R.w rest * (P i).w ((Equiv.piSplitAt i Ω).symm (x, rest) i) = _
        rw [hi]
        ring
  change (∑ ω, if A ω then ∏ j, (P j).w (ω j) else 0) ≤ p
  let e := Equiv.piSplitAt i Ω
  have hEquivSum :
      (∑ ω, if A ω then ∏ j, (P j).w (ω j) else 0) =
        ∑ z : Ω i × (∀ j : {j // j ≠ i}, Ω j.1),
          if A (e.symm z) then ∏ j, (P j).w ((e.symm z) j) else 0 := by
    exact Fintype.sum_equiv e _ _ (by intro ω; simp only [Equiv.symm_apply_apply])
  rw [hEquivSum]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hrewrite :
      (∑ rest, ∑ x, if A (e.symm (x, rest)) then
          (∏ j, (P j).w ((e.symm (x, rest)) j)) else 0) =
        ∑ rest, R.w rest *
          (∑ x, if A (e.symm (x, rest)) then (P i).w x else 0) := by
    apply Finset.sum_congr rfl
    intro rest hrest
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hprod]
    by_cases hA : A (e.symm (x, rest)) <;> simp [hA, mul_comm]
  rw [hrewrite]
  calc
    (∑ rest, R.w rest *
        (∑ x, if A (e.symm (x, rest)) then (P i).w x else 0)) ≤
        ∑ rest, R.w rest * p := by
      apply Finset.sum_le_sum
      intro rest hrest
      exact mul_le_mul_of_nonneg_left (hbound rest) (R.nonneg rest)
    _ = p := by
      rw [← Finset.sum_mul]
      rw [R.sum_eq_one]
      ring

/-- The expectation of a function under a finite product, split at one coordinate. -/
theorem FinProb.expect_piSplitAt_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (X : (∀ j, Ω j) → ℝ) :
    (FinProb.pi P).expect X =
      ∑ rest : (∀ j : {j // j ≠ i}, Ω j.1),
        (FinProb.pi (fun j => P j.1)).w rest *
          (∑ x, (P i).w x * X ((Equiv.piSplitAt i Ω).symm (x, rest))) := by
  classical
  let R : FinProb (∀ j : {j // j ≠ i}, Ω j.1) := FinProb.pi (fun j => P j.1)
  have hprod (x : Ω i) (rest : ∀ j : {j // j ≠ i}, Ω j.1) :
      (∏ j, (P j).w (((Equiv.piSplitAt i Ω).symm (x, rest)) j)) =
        (P i).w x * R.w rest := by
    let f : ι → ℝ := fun j => (P j).w (((Equiv.piSplitAt i Ω).symm (x, rest)) j)
    have hi : (Equiv.piSplitAt i Ω).symm (x, rest) i = x := by
      simp [Equiv.piSplitAt]
    have hrest : (∏ j ∈ Finset.univ.erase i, f j) = R.w rest := by
      have hset : Finset.univ.erase i = Finset.univ.filter (fun j : ι => j ≠ i) := by
        ext j
        simp
      rw [hset]
      rw [← Finset.prod_subtype_eq_prod_filter
        (s := Finset.univ) (p := fun j : ι => j ≠ i)]
      dsimp [R, FinProb.pi]
      have hsub :
          Finset.univ.subtype (fun j : ι => j ≠ i) =
            (Finset.univ : Finset {j // j ≠ i}) := by
        ext j
        simp
      rw [hsub]
      change (∏ j : {j // j ≠ i}, f j.1) = ∏ j : {j // j ≠ i}, (P j.1).w (rest j)
      apply Finset.prod_congr rfl
      intro j hj
      simp [f, Equiv.piSplitAt, j.2]
    calc
      ∏ j, f j = (∏ j ∈ Finset.univ.erase i, f j) * f i := by
        simpa [f] using (Finset.prod_erase_mul Finset.univ f (Finset.mem_univ i)).symm
      _ = (P i).w x * R.w rest := by
        rw [hrest]
        change R.w rest * (P i).w ((Equiv.piSplitAt i Ω).symm (x, rest) i) = _
        rw [hi]
        ring
  change (∑ ω, (∏ j, (P j).w (ω j)) * X ω) = _
  let e := Equiv.piSplitAt i Ω
  have hEquivSum :
      (∑ ω, (∏ j, (P j).w (ω j)) * X ω) =
        ∑ z : Ω i × (∀ j : {j // j ≠ i}, Ω j.1),
          (∏ j, (P j).w ((e.symm z) j)) * X (e.symm z) := by
    exact Fintype.sum_equiv e _ _ (by intro ω; simp only [Equiv.symm_apply_apply])
  rw [hEquivSum, Fintype.sum_prod_type, Finset.sum_comm]
  have hrewrite :
      (∑ rest, ∑ x,
        (∏ j, (P j).w ((e.symm (x, rest)) j)) * X (e.symm (x, rest))) =
        ∑ rest, R.w rest *
          (∑ x, (P i).w x * X (e.symm (x, rest))) := by
    apply Finset.sum_congr rfl
    intro rest hrest
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hprod]
    ring
  rw [hrewrite]

/-- The squared likelihood tilt of a finite law. -/
noncomputable def FinProb.squareTilt
    {ι : Type*} [Fintype ι] (P : FinProb ι) (m : ι → ℝ)
    (hpos : 0 < ∑ i, P.w i * (m i) ^ 2) : FinProb ι where
  w i := P.w i * (m i) ^ 2 / ∑ j, P.w j * (m j) ^ 2
  nonneg i := div_nonneg (mul_nonneg (P.nonneg i) (sq_nonneg _)) hpos.le
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)

namespace Law

/-- Condition a finite law on a set when it has positive mass, and leave it unchanged on a null set. -/
noncomputable def restrictOrSelf {N : ℕ} (μ : Law N) (A : Finset (Fin N)) : Law N :=
  if h : 0 < ∑ x ∈ A, μ.w x then Law.restrict μ A h else μ

end Law

/-- Jensen's square inequality for a finite law. -/
theorem FinProb.expect_sq_ge_sq_expect {ι : Type*} [Fintype ι]
    (P : FinProb ι) (f : ι → ℝ) :
    (P.expect f) ^ 2 ≤ P.expect (fun i => (f i) ^ 2) := by
  classical
  let m := P.expect f
  have hvar : 0 ≤ P.expect (fun i => (f i - m) ^ 2) := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (P.nonneg i) (sq_nonneg _)
  have hcalc :
      P.expect (fun i => (f i - m) ^ 2) =
        P.expect (fun i => (f i) ^ 2) - m ^ 2 := by
    unfold FinProb.expect at *
    calc
      (∑ i, P.w i * (f i - m) ^ 2) =
          ∑ i, (P.w i * (f i) ^ 2 - 2 * m * (P.w i * f i) + m ^ 2 * P.w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, P.w i * (f i) ^ 2) -
          2 * m * (∑ i, P.w i * f i) + m ^ 2 * (∑ i, P.w i) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [Finset.mul_sum, Finset.mul_sum] <;> ring
      _ = (∑ i, P.w i * (f i) ^ 2) - m ^ 2 := by
        simp [m, FinProb.expect, P.sum_eq_one] <;> ring
  have hvar' : 0 ≤ P.expect (fun i => (f i) ^ 2) - (P.expect f) ^ 2 := by
    simpa [m] using hvar.trans_eq hcalc
  linarith

/-- Expanding a squared degree gives the expected common-neighbor codegree. -/
theorem FinProb.expect_rowDeg_sq_eq_codeg {N : ℕ}
    (μ π : Law N) (E : Fin N → Fin N → Prop) (G : Colour) :
    μ.expect (fun x => (rowDeg E G x π) ^ 2) =
      ∑ y, ∑ y', π.w y * π.w y' * codeg E G μ y y' := by
  classical
  unfold FinProb.expect rowDeg codeg
  have hinner (x : Fin N) :
      (∑ y, π.w y * (if Hits E G x y then (1 : ℝ) else 0)) ^ 2 =
        ∑ y, ∑ y', π.w y * π.w y' *
          (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0) := by
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro y' hy'
    by_cases hxy : Hits E G x y <;> by_cases hxy' : Hits E G x y' <;>
      simp [hxy, hxy'] <;> ring
  calc
    (∑ x, μ.w x *
        (∑ y, π.w y * (if Hits E G x y then (1 : ℝ) else 0)) ^ 2) =
      ∑ x, μ.w x *
        (∑ y, ∑ y', π.w y * π.w y' *
          (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hinner]
    _ = ∑ x, ∑ y, ∑ y', μ.w x * (π.w y * π.w y' *
          (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
    _ = ∑ y, ∑ y', ∑ x, μ.w x * (π.w y * π.w y' *
          (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ y, ∑ y', π.w y * π.w y' *
          (∑ x, μ.w x *
            (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro y' hy'
      calc
        (∑ x, μ.w x * (π.w y * π.w y' *
            (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0))) =
            ∑ x, (π.w y * π.w y') * (μ.w x *
              (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = π.w y * π.w y' *
            (∑ x, μ.w x *
              (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
          rw [Finset.mul_sum]
    _ = ∑ y, ∑ y', π.w y * π.w y' *
          ∑ x, μ.w x *
            (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0) := rfl

/-- A finite union bound for events in a finite probability space. -/
theorem FinProb.pr_iUnion_le
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FinProb Ω) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  calc
    P.pr (fun ω => ∃ i, A i ω) =
        ∑ ω, if ∃ i, A i ω then P.w ω else 0 := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ∃ i, A i ω <;> simp [h]
    _ ≤ ∑ ω, ∑ i, if A i ω then P.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hA : ∃ i, A i ω
      · obtain ⟨i, hi⟩ := hA
        have hExist : ∃ i, A i ω := ⟨i, hi⟩
        have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
            0 ≤ if A j ω then P.w ω else 0 := by
          intro j hj
          split_ifs <;> simp [P.nonneg ω]
        have hsingle : P.w ω ≤ ∑ j, if A j ω then P.w ω else 0 := by
          calc
            P.w ω = if A i ω then P.w ω else 0 := by simp [hi]
            _ ≤ ∑ j, if A j ω then P.w ω else 0 :=
              Finset.single_le_sum hnonneg (Finset.mem_univ i)
        simpa [hExist] using hsingle
      · have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
            0 ≤ if A j ω then P.w ω else 0 := by
          intro j hj
          split_ifs <;> simp [P.nonneg ω]
        simp [hA]
        exact Finset.sum_nonneg hnonneg
    _ = ∑ i, P.pr (A i) := by
      rw [Finset.sum_comm]
      rfl

/-- The chord of `log` between `θ` and `1` lies below `log`, including after clipping at `θ`. -/
theorem real_log_max_ge_chord {θ x : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (max θ x) ≥ Real.log θ * (1 - x) / (1 - θ) := by
  let z : ℝ := max θ x
  let lam : ℝ := (z - θ) / (1 - θ)
  have hz0 : 0 < z := lt_of_lt_of_le hθ0 (le_max_left θ x)
  have hz1 : z ≤ 1 := max_le hθ1.le hx1
  have hzt : θ ≤ z := le_max_left θ x
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    exact div_nonneg (sub_nonneg.mpr hzt) (sub_nonneg.mpr hθ1.le)
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    rw [div_le_one (sub_pos.mpr hθ1)]
    linarith
  have hleft : 0 ≤ 1 - lam := by linarith
  have hinterp : (1 - lam) * θ + lam * 1 = z := by
    dsimp [lam]
    field_simp [ne_of_gt (sub_pos.mpr hθ1)]
    ring
  have hconc : (1 - lam) * Real.log θ + lam * Real.log 1 ≤
      Real.log ((1 - lam) * θ + lam * 1) := by
    simpa [smul_eq_mul] using
      (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hθ0)
        (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 1)) hleft hlam0 (by ring)
  have hlogθ : Real.log θ ≤ 0 := by
    calc
      Real.log θ ≤ Real.log 1 := Real.log_le_log hθ0 hθ1.le
      _ = 0 := by simp
  have hweight : 1 - lam = (1 - z) / (1 - θ) := by
    dsimp [lam]
    field_simp [ne_of_gt (sub_pos.mpr hθ1)]
    ring
  have hline : Real.log θ * (1 - z) / (1 - θ) ≤ Real.log z := by
    simp only [Real.log_one, mul_zero, add_zero] at hconc
    rw [hinterp] at hconc
    rw [hweight] at hconc
    convert hconc using 1 <;> ring
  have hline_mono : Real.log θ * (1 - x) / (1 - θ) ≤
      Real.log θ * (1 - z) / (1 - θ) := by
    apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hθ1.le)
    exact mul_le_mul_of_nonpos_left (sub_le_sub_left (le_max_right θ x) 1) hlogθ
  simpa [z] using hline_mono.trans hline

/-- Jensen's chord lower bound for a clipped logarithm under a finite law. -/
theorem FinProb.expect_log_max_ge_chord {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (θ : ℝ) (q : Ω → ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hq : ∀ ω, 0 ≤ q ω ∧ q ω ≤ 1) :
    P.expect (fun ω => Real.log (max θ (q ω))) ≥
      Real.log θ * (1 - P.expect q) / (1 - θ) := by
  have hpoint (ω : Ω) :
      Real.log θ * (1 - q ω) / (1 - θ) ≤ Real.log (max θ (q ω)) :=
    real_log_max_ge_chord hθ0 hθ1 (hq ω).1 (hq ω).2
  calc
    P.expect (fun ω => Real.log (max θ (q ω))) ≥
        P.expect (fun ω => Real.log θ * (1 - q ω) / (1 - θ)) := by
      unfold FinProb.expect
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left (hpoint ω) (P.nonneg ω)
    _ = Real.log θ * (1 - P.expect q) / (1 - θ) := by
      unfold FinProb.expect
      have hsum :
          (∑ ω, P.w ω * (Real.log θ * (1 - q ω) / (1 - θ))) =
            (Real.log θ * (1 - θ)⁻¹) * (∑ ω, P.w ω * (1 - q ω)) := by
        calc
          (∑ ω, P.w ω * (Real.log θ * (1 - q ω) / (1 - θ))) =
              ∑ ω, (Real.log θ * (1 - θ)⁻¹) * (P.w ω * (1 - q ω)) := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
          _ = (Real.log θ * (1 - θ)⁻¹) * (∑ ω, P.w ω * (1 - q ω)) := by
            rw [Finset.mul_sum]
      have hsum2 : (∑ ω, P.w ω * (1 - q ω)) =
          1 - ∑ ω, P.w ω * q ω := by
        calc
          (∑ ω, P.w ω * (1 - q ω)) =
              ∑ ω, (P.w ω - P.w ω * q ω) := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
          _ = (∑ ω, P.w ω) - ∑ ω, P.w ω * q ω := by
            rw [← Finset.sum_sub_distrib]
          _ = 1 - ∑ ω, P.w ω * q ω := by rw [P.sum_eq_one]
      rw [hsum, hsum2]
      ring

namespace FinProb

theorem p_s10_1c_pr_fiber_single_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (ω : Ω) (hω : A ω) : P.w ω ≤ P.pr A := by
  classical
  unfold FinProb.pr
  calc
    P.w ω = if A ω then P.w ω else 0 := by simp [hω]
    _ ≤ ∑ x, if A x then P.w x else 0 :=
      Finset.single_le_sum
        (f := fun x => if A x then P.w x else 0)
        (fun x hx => by split_ifs with hAx <;> simp [P.nonneg x])
        (Finset.mem_univ ω)

theorem p_s10_1c_expect_cond_eq_sum {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) [DecidablePred A] (hA : 0 < P.pr A) (f : Ω → ℝ) :
    (P.cond A hA).expect f =
      (∑ ω, if A ω then P.w ω * f ω else 0) / P.pr A := by
  classical
  simp only [FinProb.expect, FinProb.cond]
  calc
    _ = ∑ ω, (if A ω then P.w ω * f ω else 0) / P.pr A := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : A ω <;> simp [h] <;> field_simp [ne_of_gt hA] <;> ring
    _ = (∑ ω, if A ω then P.w ω * f ω else 0) / P.pr A := by
      rw [Finset.sum_div]

theorem p_s10_1c_expect_exp_neg_centered_cond_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) [DecidablePred A] (hA : 0 < P.pr A) (X : Ω → ℝ)
    (a b μ s : ℝ) (hab : a ≤ b) (hX : ∀ ω, a ≤ X ω ∧ X ω ≤ b)
    (hs : 0 ≤ s)
    (hmean : μ * P.pr A ≤ ∑ ω, if A ω then P.w ω * X ω else 0) :
    (P.cond A hA).expect (fun ω => Real.exp (-s * (X ω - μ))) ≤
      Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  let Q := P.cond A hA
  have hμ : μ ≤ Q.expect X := by
    rw [p_s10_1c_expect_cond_eq_sum]
    exact (le_div_iff₀ hA).2 hmean
  let mQ : ℝ := Q.expect X
  have hhoeffding := xHoeffdingLemma Q X a b (-s) hab hX
  have hhoeffding' : Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) ≤
      Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
    simpa [mQ, pow_two] using hhoeffding
  have hfactor : Q.expect (fun ω => Real.exp (-s * (X ω - μ))) =
      Real.exp (s * (μ - mQ)) * Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) := by
    unfold FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    change Q.w ω * Real.exp (-s * (X ω - μ)) =
      Real.exp (s * (μ - mQ)) * (Q.w ω * Real.exp (-s * (X ω - mQ)))
    have he : -s * (X ω - μ) = s * (μ - mQ) + -s * (X ω - mQ) := by ring
    rw [he, Real.exp_add]
    ring_nf
  have hscalar : Real.exp (s * (μ - mQ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    dsimp [mQ]
    nlinarith
  have hcenter_nonneg : 0 ≤ Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (Q.nonneg ω) (Real.exp_nonneg _)
  rw [hfactor]
  calc
    _ ≤ 1 * Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) :=
      mul_le_mul_of_nonneg_right hscalar hcenter_nonneg
    _ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by simpa using hhoeffding'

theorem p_s10_1c_fiber_exp_neg_centered_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) [DecidablePred A] (X : Ω → ℝ) (a b μ s : ℝ)
    (hab : a ≤ b) (hX : ∀ ω, a ≤ X ω ∧ X ω ≤ b) (hs : 0 ≤ s)
    (hmean : P.pr A = 0 ∨ μ * P.pr A ≤
      ∑ ω, if A ω then P.w ω * X ω else 0) :
    (∑ ω, if A ω then P.w ω * Real.exp (-s * (X ω - μ)) else 0) ≤
      P.pr A * Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  classical
  have hqnonneg : 0 ≤ P.pr A := by
    unfold FinProb.pr
    apply Finset.sum_nonneg
    intro ω hω
    by_cases hA : A ω
    · simp [hA, P.nonneg ω]
    · simp [hA]
  by_cases hq : P.pr A = 0
  · have hzero (ω : Ω) (hω : A ω) : P.w ω = 0 := by
      have hle := p_s10_1c_pr_fiber_single_le P A ω hω
      rw [hq] at hle
      exact le_antisymm hle (P.nonneg ω)
    have hsum :
        (∑ ω, if A ω then P.w ω * Real.exp (-s * (X ω - μ)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hA : A ω <;> simp [hA, hzero ω]
    rw [hsum, hq]
    simp
  · have hqpos : 0 < P.pr A := by
      by_contra hnot
      have hle : P.pr A ≤ 0 := le_of_not_gt hnot
      exact hq (le_antisymm hle hqnonneg)
    have hmean' : μ * P.pr A ≤ ∑ ω, if A ω then P.w ω * X ω else 0 := by
      rcases hmean with hz | hmean'
      · exact (hq hz).elim
      · exact hmean'
    have hcond := p_s10_1c_expect_exp_neg_centered_cond_le
      P A hqpos X a b μ s hab hX hs hmean'
    rw [p_s10_1c_expect_cond_eq_sum] at hcond
    have hmul := (div_le_iff₀ hqpos).mp hcond
    calc
      _ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) * P.pr A := hmul
      _ = P.pr A * Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by ring

theorem p_s10_1c_expect_mul_fiber_exp_neg_centered_le
    {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]
    (P : FinProb Ω) (history : Ω → H) (F X : Ω → ℝ) (μ s E : ℝ)
    (hFfiber : ∀ ω ω', history ω = history ω' → F ω = F ω')
    (hFnonneg : ∀ ω, 0 ≤ F ω)
    (hlocal : ∀ h : H,
      (∑ ω, if history ω = h then P.w ω * Real.exp (-s * (X ω - μ)) else 0) ≤
        (∑ ω, if history ω = h then P.w ω else 0) * E) :
    P.expect (fun ω => F ω * Real.exp (-s * (X ω - μ))) ≤ E * P.expect F := by
  classical
  have hfiber (h : H) :
      (∑ ω, if history ω = h then P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0) ≤
        E * (∑ ω, if history ω = h then P.w ω * F ω else 0) := by
    by_cases hex : ∃ ω, history ω = h
    · obtain ⟨ω₀, hω₀⟩ := hex
      have hleft :
          (∑ ω, if history ω = h then P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0) =
            F ω₀ * (∑ ω, if history ω = h then P.w ω * Real.exp (-s * (X ω - μ)) else 0) := by
        calc
          _ = ∑ ω, (if history ω = h then P.w ω else 0) *
              (F ω₀ * Real.exp (-s * (X ω - μ))) := by
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h
            · have hF := hFfiber ω ω₀ (hωh.trans hω₀.symm)
              simp [hωh, hF]
            · simp [hωh]
          _ = F ω₀ * (∑ ω, if history ω = h then
                P.w ω * Real.exp (-s * (X ω - μ)) else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h <;> simp [hωh] <;> ring
      have hright :
          (∑ ω, if history ω = h then P.w ω * F ω else 0) =
            F ω₀ * (∑ ω, if history ω = h then P.w ω else 0) := by
        calc
          _ = ∑ ω, (if history ω = h then P.w ω else 0) * F ω₀ := by
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h
            · have hF := hFfiber ω ω₀ (hωh.trans hω₀.symm)
              simp [hωh, hF, mul_comm]
            · simp [hωh]
          _ = F ω₀ * (∑ ω, if history ω = h then P.w ω else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h <;> simp [hωh, mul_comm]
      rw [hleft, hright]
      calc
        F ω₀ * (∑ ω, if history ω = h then
            P.w ω * Real.exp (-s * (X ω - μ)) else 0) ≤
            F ω₀ * ((∑ ω, if history ω = h then P.w ω else 0) * E) :=
          mul_le_mul_of_nonneg_left (hlocal h) (hFnonneg ω₀)
        _ = E * (F ω₀ * ∑ ω, if history ω = h then P.w ω else 0) := by ring
    · have hnone (ω : Ω) : history ω ≠ h := by
        intro heq
        exact hex ⟨ω, heq⟩
      simp [hnone]
  have hpartition (ω : Ω) :
      P.w ω * (F ω * Real.exp (-s * (X ω - μ))) =
        ∑ h : H, if history ω = h then
          P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0 := by
    rw [Finset.sum_eq_single (history ω)]
    · simp
    · intro h hh hne
      have hne' : history ω ≠ h := fun heq => hne heq.symm
      simp [hne']
    · simp
  have hsumF :
      (∑ h : H, ∑ ω, if history ω = h then P.w ω * F ω else 0) = P.expect F := by
    unfold FinProb.expect
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Finset.sum_eq_single (history ω)]
    · simp
    · intro h hh hne
      have hne' : history ω ≠ h := fun heq => hne heq.symm
      simp [hne']
    · simp
  unfold FinProb.expect
  calc
    (∑ ω, P.w ω * (F ω * Real.exp (-s * (X ω - μ)))) =
        ∑ ω, ∑ h : H, if history ω = h then
          P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      exact hpartition ω
    _ = ∑ h : H, ∑ ω, if history ω = h then
          P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0 := Finset.sum_comm
    _ ≤ ∑ h : H, E * (∑ ω, if history ω = h then P.w ω * F ω else 0) :=
      Finset.sum_le_sum fun h hh => hfiber h
    _ = E * P.expect F := by
      rw [← Finset.mul_sum, hsumF]

end FinProb

/-- Local adapted finite Azuma bound, used until the shared concentration node lands. -/
theorem p_s10_1c_xAzuma {Ω : Type*} [Fintype Ω] {k : ℕ}
    (H : Fin (k + 1) → Type*) [∀ t, Fintype (H t)] [∀ t, DecidableEq (H t)] (P : FinProb Ω)
    (history : ∀ t, Ω → H t)
    (project : ∀ i : Fin k, H i.succ → H i.castSucc)
    (hfiltration : ∀ i ω, history i.castSucc ω = project i (history i.succ ω))
    (Δ : Fin k → Ω → ℝ)
    (hadapted : ∀ (m : ℕ) (hm : m ≤ k) (i : Fin k), i.val < m →
      ∀ ω ω', history ⟨m, Nat.lt_succ_of_le hm⟩ ω = history ⟨m, Nat.lt_succ_of_le hm⟩ ω' →
        Δ i ω = Δ i ω')
    (μ lo hi : Fin k → ℝ)
    (hbound : ∀ i ω, lo i ≤ Δ i ω ∧ Δ i ω ≤ hi i)
    (hmean : ∀ i (h : H i.castSucc),
      P.pr (fun ω => history i.castSucc ω = h) = 0 ∨
        μ i * P.pr (fun ω => history i.castSucc ω = h) ≤
          (∑ ω, if history i.castSucc ω = h then P.w ω * Δ i ω else 0))
    (hwidth : 0 < ∑ i, (hi i - lo i) ^ 2) (t : ℝ) (ht : 0 < t) :
    P.pr (fun ω => ∑ i, Δ i ω < (∑ i, μ i) - t) ≤
      Real.exp (-2 * t ^ 2 / ∑ i, (hi i - lo i) ^ 2) := by
  classical
  let yNat : ℕ → Ω → ℝ := fun j ω =>
    if hj : j < k then Δ ⟨j, hj⟩ ω - μ ⟨j, hj⟩ else 0
  let widthNat : ℕ → ℝ := fun j =>
    if hj : j < k then (hi ⟨j, hj⟩ - lo ⟨j, hj⟩) ^ 2 else 0
  let S : ℕ → Ω → ℝ := fun m ω => ∑ j ∈ Finset.range m, yNat j ω
  let W : ℕ → ℝ := fun m => ∑ j ∈ Finset.range m, widthNat j
  let U : ℝ := ∑ i, (hi i - lo i) ^ 2
  have hU : 0 < U := by simpa [U] using hwidth
  let s : ℝ := 4 * t / U
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hΩ : Nonempty Ω := by
    by_contra hne
    haveI : IsEmpty Ω := not_nonempty_iff.mp hne
    have hsum : (∑ ω, P.w ω) = 0 := by simp
    rw [P.sum_eq_one] at hsum
    norm_num at hsum
  have hmgf : ∀ m, m ≤ k →
      P.expect (fun ω => Real.exp (-s * S m ω)) ≤
        Real.exp (s ^ 2 * W m / 8) := by
    intro m
    induction m with
    | zero =>
      intro hm
      simp [S, W, FinProb.expect, P.sum_eq_one]
    | succ m ih =>
      intro hm
      have hm_lt : m < k := by omega
      have hm_le : m ≤ k := by omega
      let i : Fin k := ⟨m, hm_lt⟩
      have hstep (ω : Ω) : S (m + 1) ω = S m ω + (Δ i ω - μ i) := by
        simp [S, yNat, Finset.sum_range_succ, i, hm_lt]
      have hwidthStep : W (m + 1) = W m + (hi i - lo i) ^ 2 := by
        simp [W, widthNat, Finset.sum_range_succ, i, hm_lt]
      have hab : lo i ≤ hi i := by
        obtain ⟨ω⟩ := hΩ
        exact (hbound i ω).1.trans (hbound i ω).2
      have hlocal (g : H i.castSucc) :
          (∑ ω, if history i.castSucc ω = g then
            P.w ω * Real.exp (-s * (Δ i ω - μ i)) else 0) ≤
          (∑ ω, if history i.castSucc ω = g then P.w ω else 0) *
            Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8) := by
        have hlocal' := FinProb.p_s10_1c_fiber_exp_neg_centered_le P
          (fun ω => history i.castSucc ω = g) (Δ i) (lo i) (hi i) (μ i) s
          hab (fun ω => hbound i ω) hs (hmean i g)
        have hprob : P.pr (fun ω => history i.castSucc ω = g) =
            ∑ ω, if history i.castSucc ω = g then P.w ω else 0 := by
          unfold FinProb.pr
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases hEq : history i.castSucc ω = g <;> simp [hEq]
        rw [hprob] at hlocal'
        exact hlocal'
      have hSfiber (ω ω' : Ω)
          (hh : history i.castSucc ω = history i.castSucc ω') : S m ω = S m ω' := by
        unfold S
        apply Finset.sum_congr rfl
        intro j hj
        have hj_lt : j < m := Finset.mem_range.mp hj
        have hj_k : j < k := lt_of_lt_of_le hj_lt (Nat.le_of_lt i.isLt)
        have hΔ := hadapted m hm_le ⟨j, hj_k⟩ hj_lt ω ω' hh
        simp [yNat, hj_k, hΔ]
      have hstepMgf :
          P.expect (fun ω => Real.exp (-s * S (m + 1) ω)) =
            P.expect (fun ω => Real.exp (-s * S m ω) *
              Real.exp (-s * (Δ i ω - μ i))) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro ω hω
        change P.w ω * Real.exp (-s * S (m + 1) ω) =
          P.w ω * (Real.exp (-s * S m ω) * Real.exp (-s * (Δ i ω - μ i)))
        have he : -s * S (m + 1) ω =
            (-s * S m ω) + (-s * (Δ i ω - μ i)) := by
          rw [hstep ω]
          ring
        rw [he, Real.exp_add]
      have htail := FinProb.p_s10_1c_expect_mul_fiber_exp_neg_centered_le P
        (history i.castSucc) (fun ω => Real.exp (-s * S m ω)) (Δ i) (μ i) s
        (Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8))
        (fun ω ω' hh => by rw [hSfiber ω ω' hh])
        (fun ω => Real.exp_nonneg _)
        hlocal
      calc
        P.expect (fun ω => Real.exp (-s * S (m + 1) ω)) =
            P.expect (fun ω => Real.exp (-s * S m ω) *
              Real.exp (-s * (Δ i ω - μ i))) := hstepMgf
        _ ≤ Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8) *
              P.expect (fun ω => Real.exp (-s * S m ω)) := htail
        _ ≤ Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8) *
              Real.exp (s ^ 2 * W m / 8) :=
            mul_le_mul_of_nonneg_left (ih hm_le) (Real.exp_nonneg _)
        _ = Real.exp (s ^ 2 * W (m + 1) / 8) := by
          rw [hwidthStep, ← Real.exp_add]
          congr 1
          ring
  have hWfull : W k = ∑ i, (hi i - lo i) ^ 2 := by
    dsimp [W, widthNat]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => if hj : j < k then (hi ⟨j, hj⟩ - lo ⟨j, hj⟩) ^ 2 else 0)]
    simp
  have hsumY (ω : Ω) : S k ω = ∑ i, (Δ i ω - μ i) := by
    dsimp [S, yNat]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => if hj : j < k then Δ ⟨j, hj⟩ ω - μ ⟨j, hj⟩ else 0)]
    simp
  have hsumCentered (ω : Ω) :
      (∑ i, Δ i ω) - ∑ i, μ i = S k ω := by
    calc
      (∑ i, Δ i ω) - ∑ i, μ i = ∑ i, (Δ i ω - μ i) := by
        rw [Finset.sum_sub_distrib]
      _ = S k ω := (hsumY ω).symm
  have hevent (ω : Ω) :
      (∑ i, Δ i ω < (∑ i, μ i) - t) →
        t ≤ -((∑ i, Δ i ω) - ∑ i, μ i) := by
    intro h
    linarith
  have hmark := FinProb.pr_exp_markov P
    (fun ω => -((∑ i, Δ i ω) - ∑ i, μ i)) s t hs
  have hmgfMark :
      P.expect (fun ω => Real.exp (s * -((∑ i, Δ i ω) - ∑ i, μ i))) ≤
        Real.exp (s ^ 2 * U / 8) := by
    have hfun : (fun ω => Real.exp (s * -((∑ i, Δ i ω) - ∑ i, μ i))) =
        (fun ω => Real.exp (-s * S k ω)) := by
      funext ω
      rw [hsumCentered]
      congr 1
      ring
    rw [hfun]
    simpa [hWfull, U] using hmgf k le_rfl
  calc
    P.pr (fun ω => ∑ i, Δ i ω < (∑ i, μ i) - t) ≤
        P.pr (fun ω => t ≤ -((∑ i, Δ i ω) - ∑ i, μ i)) :=
      FinProb.pr_mono P _ _ hevent
    _ ≤ Real.exp (-s * t) *
          P.expect (fun ω => Real.exp (s * -((∑ i, Δ i ω) - ∑ i, μ i))) := hmark
    _ ≤ Real.exp (-s * t) * Real.exp (s ^ 2 * U / 8) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact hmgfMark
    _ = Real.exp (-2 * t ^ 2 / U) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [s]
      field_simp [ne_of_gt hU]
      ring


open HypercubeRamsey.S10

set_option maxHeartbeats 3000000 in
theorem fixedListBound_explicit :
      ∀ (N r k q : ℕ) (E : Fin N → Fin N → Prop)
        (X Y : Finset (Fin N)) (G : Colour)
        (ρ : FinProb (Fin q)) (D : Fin q → Law N) (ν : Law N)
        (μ : Fin r → Law N) (w ε a wμ wν : ℝ),
        (∀ b, (μ b).SupportedIn X ∧ (μ b).WidthLE wμ) →
        ν.WidthLE wν →
        (∀ j, (D j).SupportedIn Y) →
        (∀ y, (∑ j, ρ.w j * (D j).w y) ≤ 4 * ν.w y) →
        DiscOne E X Y w w ε →
        0 ≤ ε → 100 * ε ≤ a → a ≤ 1 / 10 →
        wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤ w →
        Real.log ((r : ℝ) + 1) ≤ a ^ 2 * (k : ℝ) / 100 →
        ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp (wμ - w) ≤
          Real.exp (-(a ^ 2 * (k : ℝ)) / 50) →
        fixedListFailureWeight (N := N) (r := r) (k := k) (q := q) E G ρ D μ a ≤
          Real.exp (-(1 / 100 : ℝ) * a ^ 2 * (k : ℝ)) := by
  classical
  intro N r k q E X Y G ρ D ν μ w ε a wμ wν hμ hν hD hagg hdisc hε hεa ha hw hlog hexception
  let P : FinProb (Fin r → Fin k → Fin N) :=
    FinProb.pi (fun b => FinProb.pi (fun _ : Fin k => μ b))
  have hPweight (W : Fin r → Fin k → Fin N) : P.w W = tupleArrayWeight μ W := by
    simp [P, tupleArrayWeight, FinProb.pi]
  have htotal : (∑ W : Fin r → Fin k → Fin N, tupleArrayWeight μ W) = 1 := by
    simpa only [← hPweight] using P.sum_eq_one
  have hweight_nonneg (W : Fin r → Fin k → Fin N) : 0 ≤ tupleArrayWeight μ W := by
    exact Finset.prod_nonneg fun b _ => Finset.prod_nonneg fun i _ => (μ b).nonneg (W b i)
  have hfailure_le_one :
      fixedListFailureWeight (N := N) (r := r) (k := k) (q := q) E G ρ D μ a ≤ 1 := by
    unfold fixedListFailureWeight
    calc
      (∑ W : Fin r → Fin k → Fin N,
          if fixedListFailure E G ρ D μ a W then tupleArrayWeight μ W else 0) ≤
          ∑ W : Fin r → Fin k → Fin N, tupleArrayWeight μ W := by
        apply Finset.sum_le_sum
        intro W hW
        by_cases hfail : fixedListFailure E G ρ D μ a W <;> simp [hfail, hweight_nonneg W]
      _ = 1 := htotal
  have hmass_univ :
      squaredClusterMass ρ D (Finset.univ : Finset (Fin N)) = 1 := by
    have hmass (j : Fin q) : lawMassOn (D j) (Finset.univ : Finset (Fin N)) = 1 := by
      simp [lawMassOn, (D j).sum_eq_one]
    simp [squaredClusterMass, hmass, ρ.sum_eq_one]
  have hmass_mono (A B : Finset (Fin N)) (hAB : A ⊆ B) :
      squaredClusterMass ρ D A ≤ squaredClusterMass ρ D B := by
    unfold squaredClusterMass lawMassOn
    apply Finset.sum_le_sum
    intro j hj
    have hmass : (∑ y ∈ A, (D j).w y) ≤ ∑ y ∈ B, (D j).w y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hAB
      intro y hyA hyB
      exact (D j).nonneg y
    have hA : 0 ≤ ∑ y ∈ A, (D j).w y := by
      apply Finset.sum_nonneg
      intro y hy
      exact (D j).nonneg y
    have hB : 0 ≤ ∑ y ∈ B, (D j).w y := by
      apply Finset.sum_nonneg
      intro y hy
      exact (D j).nonneg y
    have hsquare : (∑ y ∈ A, (D j).w y) ^ 2 ≤ (∑ y ∈ B, (D j).w y) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmass) (add_nonneg hA hB)]
    exact mul_le_mul_of_nonneg_left hsquare (ρ.nonneg j)
  have hmass_nonneg (A : Finset (Fin N)) : 0 ≤ squaredClusterMass ρ D A := by
    unfold squaredClusterMass
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ρ.nonneg j) (sq_nonneg (lawMassOn (D j) A))
  by_cases hr : r = 0
  · have hhit (W : Fin r → Fin k → Fin N) : fixedListHitSet E G W = Finset.univ := by
      ext y
      simp [fixedListHitSet, hr]
    have hnot : ∀ W : Fin r → Fin k → Fin N, ¬ fixedListFailure E G ρ D μ a W := by
      intro W
      simp [fixedListFailure, hr, hhit W, hmass_univ]
    simp [fixedListFailureWeight, hnot]
    positivity
  by_cases hk : k = 0
  · have hhit (W : Fin r → Fin k → Fin N) : fixedListHitSet E G W = Finset.univ := by
      ext y
      simp [fixedListHitSet, hk]
    have hhitWithout (W : Fin r → Fin k → Fin N) (b : Fin r) :
        fixedListHitSetWithout E G W b = Finset.univ := by
      ext y
      simp [fixedListHitSetWithout, hk]
    have hnot : ∀ W : Fin r → Fin k → Fin N, ¬ fixedListFailure E G ρ D μ a W := by
      intro W
      simp [fixedListFailure, hk, hhit W, hhitWithout W, hmass_univ]
    simp [fixedListFailureWeight, hnot]
    positivity
  by_cases ha0 : a = 0
  · rw [ha0]
    simpa [ha0] using hfailure_le_one
  · have haPos : 0 < a := by
      have haNonneg : 0 ≤ a := le_trans (by positivity : 0 ≤ 100 * ε) hεa
      exact lt_of_le_of_ne haNonneg (Ne.symm ha0)
    have hrPos : 0 < r := Nat.pos_of_ne_zero hr
    have hkPos : 0 < k := by
      by_contra hknot
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hknot
      subst k
      have hrReal : (1 : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hrPos)
      have hrOne : (1 : ℝ) < (r : ℝ) + 1 := by linarith
      have hlogPos : 0 < Real.log ((r : ℝ) + 1) := Real.log_pos hrOne
      simp at hlog
      linarith
    have hN : 0 < N := by
      by_contra hNnot
      have hN0 : N = 0 := Nat.eq_zero_of_not_pos hNnot
      subst N
      have hsum := ν.sum_eq_one
      simp at hsum
    let x₀ : Fin N := ⟨0, hN⟩
    let α := Fin r × Fin k
    let prefixHitSet : (Fin r → Fin k → Fin N) → Finset α → Finset (Fin N) :=
      fun W S => Finset.univ.filter fun y => ∀ c ∈ S, Hits E G (W c.1 c.2) y
    let prefixMass : (Fin r → Fin k → Fin N) → Finset α → ℝ :=
      fun W S => squaredClusterMass ρ D (prefixHitSet W S)
    have hhit_insert (W : Fin r → Fin k → Fin N) (S : Finset α) (c : α) :
        prefixHitSet W (insert c S) =
          (prefixHitSet W S).filter (fun y => Hits E G (W c.1 c.2) y) := by
      ext y
      simp [prefixHitSet, and_assoc, and_left_comm, and_comm]
    let L : ℝ := Real.exp (-2 * (k : ℝ) * (r : ℝ))
    let c₀ : ℝ := 1 / 2 - a / 10
    let θ : ℝ := c₀ ^ 2
    let pExc : ℝ := Real.exp (wμ - w)
    let oneStepRatio : Finset (Fin N) → Fin N → ℝ := fun J x =>
      squaredClusterMass ρ D (J.filter (fun y => Hits E G x y)) /
        squaredClusterMass ρ D J
    have hLpos : 0 < L := Real.exp_pos _
    have hc₀pos : 0 < c₀ := by dsimp [c₀]; linarith
    have hc₀le : c₀ ≤ 1 := by dsimp [c₀]; linarith
    have hθpos : 0 < θ := by dsimp [θ]; positivity
    have hθle : θ ≤ 1 := by dsimp [θ]; nlinarith [sq_nonneg (c₀ - 1)]
    have hpExc : 0 < pExc := Real.exp_pos _
    have hprefix_exception_bound (b : Fin r) (J : Finset (Fin N))
        (hJ : L ≤ squaredClusterMass ρ D J) :
        ((μ b).pr (fun x => oneStepRatio J x < θ) ≤ pExc) ∧
          (FixedListOwnBlock E G ρ D (μ b) a →
            (μ b).expect (fun x => oneStepRatio J x) ≥ 1 / 4 + a) := by
      classical
      let A := squaredClusterMass ρ D J
      have hApos : 0 < A := lt_of_lt_of_le hLpos hJ
      let m : Fin q → ℝ := fun j => lawMassOn (D j) J
      have hm_nonneg (j : Fin q) : 0 ≤ m j := by
        unfold m lawMassOn
        apply Finset.sum_nonneg
        intro y hy
        exact (D j).nonneg y
      have hm_le_one (j : Fin q) : m j ≤ 1 := by
        unfold m lawMassOn
        calc
          (∑ y ∈ J, (D j).w y) ≤ ∑ y, (D j).w y := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
            intro y hy hyJ
            exact (D j).nonneg y
          _ = 1 := (D j).sum_eq_one
      have hAeq : (∑ j, ρ.w j * (m j) ^ 2) = A := by
        rfl
      let ρJ : FinProb (Fin q) :=
        FinProb.squareTilt ρ m (by rw [hAeq]; exact hApos)
      let Dtilt : Fin q → Law N := fun j => Law.restrictOrSelf (D j) J
      let barD : Law N := Law.mix ρJ Dtilt
      let mHit : Fin q → Fin N → ℝ := fun j x =>
        lawMassOn (D j) (J.filter (fun y => Hits E G x y))
      have hmHit_nonneg (j : Fin q) (x : Fin N) : 0 ≤ mHit j x := by
        unfold mHit lawMassOn
        apply Finset.sum_nonneg
        intro y hy
        exact (D j).nonneg y
      have hmHit_le (j : Fin q) (x : Fin N) : mHit j x ≤ m j := by
        unfold mHit m lawMassOn
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro y hy
        by_cases hxy : Hits E G x y <;> simp [hxy, (D j).nonneg y]
      let qfun : Fin N → ℝ := fun x =>
        squaredClusterMass ρ D (J.filter (fun y => Hits E G x y)) / A
      have hq_identity (x : Fin N) :
          qfun x = ρJ.expect (fun j => (rowDeg E G x (Dtilt j)) ^ 2) := by
        have hdeg_tilt (j : Fin q) (hmj : 0 < m j) :
            rowDeg E G x (Dtilt j) = mHit j x / m j := by
          classical
          have hmj' : 0 < ∑ y ∈ J, (D j).w y := by
            simpa [m, lawMassOn] using hmj
          have htiltEq : Dtilt j = Law.restrict (D j) J hmj' := by
            simp [Dtilt, Law.restrictOrSelf, hmj']
          have hset : Finset.univ.filter (fun y : Fin N => y ∈ J) = J := by
            ext y
            simp
          rw [htiltEq]
          unfold rowDeg
          simp only [Law.restrict]
          calc
            (∑ y, (if y ∈ J then (D j).w y / ∑ z ∈ J, (D j).w z else 0) *
                (if Hits E G x y then 1 else 0)) =
              ∑ y, if y ∈ J then
                (if Hits E G x y then (D j).w y / ∑ z ∈ J, (D j).w z else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hyJ : y ∈ J <;> by_cases hxy : Hits E G x y <;> simp [hyJ, hxy]
            _ = ∑ y ∈ J,
                (if Hits E G x y then (D j).w y / ∑ z ∈ J, (D j).w z else 0) := by
              rw [← Finset.sum_filter, hset]
            _ = (∑ y ∈ J, if Hits E G x y then (D j).w y else 0) /
                (∑ z ∈ J, (D j).w z) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hxy : Hits E G x y <;> simp [hxy]
            _ = mHit j x / m j := by
              unfold mHit m lawMassOn
              rw [Finset.sum_filter]
        have hterm (j : Fin q) :
            ρJ.w j * (rowDeg E G x (Dtilt j)) ^ 2 =
              ρ.w j * (mHit j x) ^ 2 / A := by
          by_cases hmj : 0 < m j
          · rw [hdeg_tilt j hmj]
            simp [ρJ, FinProb.squareTilt, hAeq]
            field_simp [ne_of_gt hmj, ne_of_gt hApos] <;> ring
          · have hmj0 : m j = 0 := le_antisymm (le_of_not_gt hmj) (hm_nonneg j)
            have hmhit0 : mHit j x = 0 := le_antisymm
              (by simpa [hmj0] using hmHit_le j x) (hmHit_nonneg j x)
            simp [ρJ, FinProb.squareTilt, hAeq, hmj0, hmhit0, hApos.ne']
        change (∑ j, ρ.w j * (mHit j x) ^ 2) / A =
          ∑ j, ρJ.w j * (rowDeg E G x (Dtilt j)) ^ 2
        rw [Finset.sum_div]
        symm
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j
      have hbar_degree (x : Fin N) :
          rowDeg E G x barD = ρJ.expect (fun j => rowDeg E G x (Dtilt j)) := by
        classical
        simp only [rowDeg, barD, Law.mix, FinProb.expect]
        calc
          (∑ y, (∑ j, ρJ.w j * (Dtilt j).w y) *
              (if Hits E G x y then 1 else 0)) =
              ∑ y, ∑ j, ρJ.w j * (Dtilt j).w y *
                (if Hits E G x y then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [Finset.sum_mul]
          _ = ∑ j, ∑ y, ρJ.w j * (Dtilt j).w y *
                (if Hits E G x y then 1 else 0) := Finset.sum_comm
          _ = ∑ j, ρJ.w j *
                (∑ y, (Dtilt j).w y * (if Hits E G x y then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y hy
            ring
      have hq_ge_degree_sq (x : Fin N) : (rowDeg E G x barD) ^ 2 ≤ qfun x := by
        rw [hq_identity, hbar_degree]
        exact FinProb.expect_sq_ge_sq_expect ρJ (fun j => rowDeg E G x (Dtilt j))
      have hbar_supported : barD.SupportedIn Y := by
        intro y hy
        change (∑ j, ρJ.w j * (Dtilt j).w y) = 0
        apply Finset.sum_eq_zero
        intro j hj
        have hDtilt : (Dtilt j).w y = 0 := by
          by_cases hm : 0 < m j
          · have hm' : 0 < ∑ x ∈ J, (D j).w x := by
              simpa [m, lawMassOn] using hm
            by_cases hyJ : y ∈ J
            · simp [Dtilt, Law.restrictOrSelf, Law.restrict, hm', hyJ, hD j y hy]
            · simp [Dtilt, Law.restrictOrSelf, Law.restrict, hm', hyJ]
          · have hm' : ¬0 < ∑ x ∈ J, (D j).w x := by
              simpa [m, lawMassOn] using hm
            simp [Dtilt, Law.restrictOrSelf, Law.restrict, hm', hD j y hy]
        simp [hDtilt]
      have hbar_width : barD.WidthLE w := by
        intro y
        have hterm (j : Fin q) :
            ρJ.w j * (Dtilt j).w y ≤ ρ.w j * (D j).w y / A := by
          by_cases hmj : 0 < m j
          · have hmj' : 0 < ∑ x ∈ J, (D j).w x := by
              simpa [m, lawMassOn] using hmj
            by_cases hyJ : y ∈ J
            · have heq :
                  ρJ.w j * (Dtilt j).w y =
                    ρ.w j * m j * (D j).w y / A := by
                simp [ρJ, FinProb.squareTilt, Dtilt, Law.restrictOrSelf,
                  Law.restrict, hmj', hyJ, hAeq]
                field_simp [ne_of_gt hmj', ne_of_gt hApos]
                rw [show m j = ∑ x ∈ J, (D j).w x by rfl]
                ring
              rw [heq]
              have hprod : 0 ≤ ρ.w j * (D j).w y :=
                mul_nonneg (ρ.nonneg j) ((D j).nonneg y)
              have hdrop : 0 ≤ ρ.w j * (D j).w y * (1 - m j) :=
                mul_nonneg hprod (sub_nonneg.mpr (hm_le_one j))
              apply div_le_div_of_nonneg_right _ hApos.le
              calc
                ρ.w j * m j * (D j).w y =
                    (ρ.w j * (D j).w y) * m j := by ring
                _ ≤ ρ.w j * (D j).w y := by nlinarith [hdrop]
            · simp [ρJ, FinProb.squareTilt, Dtilt, Law.restrictOrSelf,
                Law.restrict, hmj', hyJ, hAeq]
              exact div_nonneg
                (mul_nonneg (ρ.nonneg j) ((D j).nonneg y)) hApos.le
          · have hmj0 : m j = 0 := le_antisymm (le_of_not_gt hmj) (hm_nonneg j)
            simp [ρJ, FinProb.squareTilt, Dtilt, Law.restrictOrSelf,
              Law.restrict, hmj0, hAeq]
            exact div_nonneg
              (mul_nonneg (ρ.nonneg j) ((D j).nonneg y)) hApos.le
        have hbar_le : barD.w y ≤ (∑ j, ρ.w j * (D j).w y) / A := by
          calc
            barD.w y = ∑ j, ρJ.w j * (Dtilt j).w y := rfl
            _ ≤ ∑ j, ρ.w j * (D j).w y / A := by
              apply Finset.sum_le_sum
              intro j hj
              exact hterm j
            _ = (∑ j, ρ.w j * (D j).w y) / A := by rw [← Finset.sum_div]
        have hInv : A⁻¹ ≤ Real.exp (2 * (k : ℝ) * (r : ℝ)) := by
          calc
            A⁻¹ ≤ L⁻¹ := (inv_le_inv₀ hApos hLpos).2 hJ
            _ = Real.exp (2 * (k : ℝ) * (r : ℝ)) := by simp [L, Real.exp_neg]
        calc
          barD.w y ≤ (∑ j, ρ.w j * (D j).w y) / A := hbar_le
          _ ≤ 4 * ν.w y / A := by
            exact div_le_div_of_nonneg_right (hagg y) hApos.le
          _ ≤ 4 * (Real.exp wν / N) * A⁻¹ := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hν y) (by positivity)) (by positivity)
          _ ≤ 4 * (Real.exp wν / N) * Real.exp (2 * (k : ℝ) * (r : ℝ)) :=
            mul_le_mul_of_nonneg_left hInv (by positivity)
          _ = Real.exp (wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ)) / N := by
            rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : 0 < (4 : ℝ))]
            ring
          _ ≤ Real.exp w / N := by
            exact div_le_div_of_nonneg_right
              (Real.exp_le_exp.mpr hw) (by exact_mod_cast hN.le)
      let badLabels : Finset (Fin N) :=
        Finset.univ.filter fun x => rowDeg E G x barD < c₀
      have hdeg_nonneg (x : Fin N) : 0 ≤ rowDeg E G x barD := by
        unfold rowDeg
        apply Finset.sum_nonneg
        intro y hy
        by_cases hxy : Hits E G x y <;> simp [hxy, barD.nonneg y]
      have hlow_mem (x : Fin N) (hx : qfun x < θ) : x ∈ badLabels := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        have hsq := hq_ge_degree_sq x
        dsimp [θ] at hx
        nlinarith [hdeg_nonneg x, hc₀pos]
      have hbad_mass : (μ b).pr (fun x => x ∈ badLabels) ≤ pExc := by
        by_contra hnot
        have hlarge : pExc < (μ b).pr (fun x => x ∈ badLabels) := lt_of_not_ge hnot
        have hpr_eq :
            (μ b).pr (fun x => x ∈ badLabels) = ∑ x ∈ badLabels, (μ b).w x := by
          letI : DecidablePred (fun x : Fin N => x ∈ badLabels) :=
            fun x => Classical.propDecidable _
          unfold FinProb.pr
          dsimp only
          rw [← Finset.sum_filter]
          have hset : Finset.univ.filter (fun x : Fin N => x ∈ badLabels) = badLabels := by
            ext x
            simp
          rw [hset]
        have hlarge' : pExc < ∑ x ∈ badLabels, (μ b).w x := by
          rw [← hpr_eq]
          exact hlarge
        have hbadpos : 0 < ∑ x ∈ badLabels, (μ b).w x := lt_trans hpExc hlarge'
        let μBad : Law N := Law.restrict (μ b) badLabels hbadpos
        have hμBadSupported : μBad.SupportedIn X := by
          intro x hx
          by_cases hxB : x ∈ badLabels
          · simp [μBad, Law.restrict, hxB, (hμ b).1 x hx]
          · simp [μBad, Law.restrict, hxB]
        have hmassLog :
            Real.log pExc < Real.log (∑ x ∈ badLabels, (μ b).w x) :=
          Real.log_lt_log hpExc hlarge'
        have hlogExc : Real.log pExc = wμ - w := by simp [pExc]
        have hwidthBadBudget :
            wμ - Real.log (∑ x ∈ badLabels, (μ b).w x) ≤ w := by
          linarith
        have hμBadWidth : μBad.WidthLE w := by
          apply Law.WidthLE.mono (Law.WidthLE.restrict (hμ b).2 hbadpos)
          exact hwidthBadBudget
        have hdiscBad := hdisc μBad barD hμBadSupported hbar_supported hμBadWidth hbar_width G
        have hdens_lower : 1 / 2 - ε ≤ dens E G μBad barD := by
          have h := (abs_le.mp hdiscBad)
          linarith
        have hdens_eq : dens E G μBad barD =
            ∑ x, μBad.w x * rowDeg E G x barD := by
          unfold dens rowDeg
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
        have hdens_upper : dens E G μBad barD ≤ c₀ := by
          rw [hdens_eq]
          calc
            (∑ x, μBad.w x * rowDeg E G x barD) ≤
                ∑ x, μBad.w x * c₀ := by
              apply Finset.sum_le_sum
              intro x hx
              by_cases hxB : x ∈ badLabels
              · have hdeg : rowDeg E G x barD < c₀ := (Finset.mem_filter.mp hxB).2
                exact mul_le_mul_of_nonneg_left hdeg.le (μBad.nonneg x)
              · have hzero : μBad.w x = 0 := by
                  simp [μBad, Law.restrict, hxB]
                simp [hzero]
            _ = c₀ := by
              rw [← Finset.sum_mul, μBad.sum_eq_one]
              ring
        have hgap : c₀ < 1 / 2 - ε := by
          dsimp [c₀]
          nlinarith [hεa, haPos]
        linarith
      have hexception : (μ b).pr (fun x => qfun x < θ) ≤ pExc := by
        change (μ b).pr (fun x => qfun x < θ) ≤ pExc
        calc
          (μ b).pr (fun x => qfun x < θ) ≤ (μ b).pr (fun x => x ∈ badLabels) :=
            FinProb.pr_mono _ _ _ (fun x hx => hlow_mem x hx)
          _ ≤ pExc := hbad_mass
      refine ⟨?_, ?_⟩
      · simpa [oneStepRatio, qfun, A] using hexception
      · intro hOwn
        have hswap :
            (∑ x, (μ b).w x *
              (∑ j, ρJ.w j * (rowDeg E G x (Dtilt j)) ^ 2)) =
              ∑ j, ρJ.w j *
                (∑ x, (μ b).w x * (rowDeg E G x (Dtilt j)) ^ 2) := by
          calc
            _ = ∑ x, ∑ j, (μ b).w x *
                (ρJ.w j * (rowDeg E G x (Dtilt j)) ^ 2) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.mul_sum]
            _ = ∑ j, ∑ x, (μ b).w x *
                (ρJ.w j * (rowDeg E G x (Dtilt j)) ^ 2) := Finset.sum_comm
            _ = ∑ j, ρJ.w j *
                (∑ x, (μ b).w x * (rowDeg E G x (Dtilt j)) ^ 2) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              ring
        have hq_expect :
            (μ b).expect qfun =
              ∑ j, ρJ.w j *
                (∑ x, (μ b).w x * (rowDeg E G x (Dtilt j)) ^ 2) := by
          calc
            (μ b).expect qfun =
                ∑ x, (μ b).w x *
                  (∑ j, ρJ.w j * (rowDeg E G x (Dtilt j)) ^ 2) := by
              unfold FinProb.expect
              apply Finset.sum_congr rfl
              intro x hx
              rw [hq_identity]
              rfl
            _ = _ := hswap
        have hpairMass (j : Fin q) :
            (∑ y, ∑ y', (Dtilt j).w y * (Dtilt j).w y') = 1 := by
          calc
            _ = (∑ y, (Dtilt j).w y) * (∑ y', (Dtilt j).w y') :=
              (Fintype.sum_mul_sum _ _).symm
            _ = 1 := by rw [(Dtilt j).sum_eq_one]; norm_num
        have hpairLower (j : Fin q) (hρJ : 0 < ρJ.w j) :
            1 / 4 + a ≤
              ∑ y, ∑ y', (Dtilt j).w y * (Dtilt j).w y' *
                codeg E G (μ b) y y' := by
          have hρ : 0 < ρ.w j := by
            by_contra hρnot
            have hρ0 : ρ.w j = 0 := le_antisymm (le_of_not_gt hρnot) (ρ.nonneg j)
            have hρJ0 : ρJ.w j = 0 := by
              simp [ρJ, FinProb.squareTilt, hAeq, hρ0]
            linarith
          have hmj : 0 < m j := by
            by_contra hmnot
            have hm0 : m j = 0 := le_antisymm (le_of_not_gt hmnot) (hm_nonneg j)
            have hρJ0 : ρJ.w j = 0 := by
              simp [ρJ, FinProb.squareTilt, hAeq, hm0]
            linarith
          have hmj' : 0 < ∑ y ∈ J, (D j).w y := by
            simpa [m, lawMassOn] using hmj
          have htiltEq : Dtilt j = Law.restrict (D j) J hmj' := by
            simp [Dtilt, Law.restrictOrSelf, hmj']
          have hDpos (y : Fin N) (hy : 0 < (Dtilt j).w y) : 0 < (D j).w y := by
            rw [htiltEq] at hy
            simp only [Law.restrict] at hy
            by_cases hyJ : y ∈ J
            · simp [hyJ] at hy
              exact (div_pos_iff_of_pos_right hmj').mp hy
            · simp [hyJ] at hy
          have hterm (y y' : Fin N) :
              (1 / 4 + a) * ((Dtilt j).w y * (Dtilt j).w y') ≤
                (Dtilt j).w y * (Dtilt j).w y' * codeg E G (μ b) y y' := by
            by_cases hy : 0 < (Dtilt j).w y
            · by_cases hy' : 0 < (Dtilt j).w y'
              · have hcodeg := hOwn j hρ y y' (hDpos y hy) (hDpos y' hy')
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  (mul_le_mul_of_nonneg_left hcodeg
                    (mul_nonneg ((Dtilt j).nonneg y) ((Dtilt j).nonneg y')))
              · have hzero : (Dtilt j).w y' = 0 :=
                  le_antisymm (le_of_not_gt hy') ((Dtilt j).nonneg y')
                simp [hzero]
            · have hzero : (Dtilt j).w y = 0 :=
                le_antisymm (le_of_not_gt hy) ((Dtilt j).nonneg y)
              simp [hzero]
          have hconst : 1 / 4 + a =
              ∑ y, ∑ y', (Dtilt j).w y * (Dtilt j).w y' * (1 / 4 + a) := by
            calc
              1 / 4 + a = (1 / 4 + a) * 1 := by ring
              _ = (1 / 4 + a) *
                  (∑ y, ∑ y', (Dtilt j).w y * (Dtilt j).w y') := by rw [hpairMass j]
              _ = ∑ y, ∑ y', (Dtilt j).w y * (Dtilt j).w y' * (1 / 4 + a) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y hy
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y' hy'
                ring
          calc
            1 / 4 + a =
                ∑ y, ∑ y', (Dtilt j).w y * (Dtilt j).w y' * (1 / 4 + a) := hconst
            _ ≤ ∑ y, ∑ y', (Dtilt j).w y * (Dtilt j).w y' *
                  codeg E G (μ b) y y' := by
              apply Finset.sum_le_sum
              intro y hy
              apply Finset.sum_le_sum
              intro y' hy'
              simpa [mul_comm, mul_left_comm, mul_assoc] using hterm y y'
        have hmean : (μ b).expect qfun ≥ 1 / 4 + a := by
          calc
            (μ b).expect qfun =
                ∑ j, ρJ.w j *
                  (∑ y, ∑ y', (Dtilt j).w y * (Dtilt j).w y' *
                    codeg E G (μ b) y y') := by
              rw [hq_expect]
              apply Finset.sum_congr rfl
              intro j hj
              change ρJ.w j * (μ b).expect (fun x => (rowDeg E G x (Dtilt j)) ^ 2) = _
              rw [FinProb.expect_rowDeg_sq_eq_codeg]
            _ ≥ ∑ j, ρJ.w j * (1 / 4 + a) := by
              apply Finset.sum_le_sum
              intro j hj
              by_cases hρJ : 0 < ρJ.w j
              · exact mul_le_mul_of_nonneg_left (hpairLower j hρJ) (ρJ.nonneg j)
              · have hρJ0 : ρJ.w j = 0 := le_antisymm (le_of_not_gt hρJ) (ρJ.nonneg j)
                simp [hρJ0]
            _ = 1 / 4 + a := by
              rw [← Finset.sum_mul, ρJ.sum_eq_one]
              ring
        simpa [oneStepRatio, qfun, A] using hmean
    let Rows : ∀ b : Fin r, FinProb (Fin k → Fin N) :=
      fun b => FinProb.pi (fun _ : Fin k => μ b)
    let badStep : (Fin r → Fin k → Fin N) → Finset α → α → Prop := fun W S c =>
      L ≤ prefixMass W S ∧ prefixMass W (insert c S) / prefixMass W S < θ
    have hbad_step_prob (S : Finset α) (c : α) (hc : c ∉ S) :
        P.pr (fun W => badStep W S c) ≤ pExc := by
      change (FinProb.pi Rows).pr (fun W => badStep W S c) ≤ pExc
      let eOut := Equiv.piSplitAt c.1 (fun _ : Fin r => Fin k → Fin N)
      let eIn := Equiv.piSplitAt c.2 (fun _ : Fin k => Fin N)
      apply FinProb.pr_piSplitAt_le Rows c.1 (fun W => badStep W S c) pExc hpExc.le
      intro restRows
      apply FinProb.pr_piSplitAt_le (fun _ : Fin k => μ c.1) c.2
        (fun row => badStep (eOut.symm (row, restRows)) S c) pExc hpExc.le
      intro restCols
      let base : Fin r → Fin k → Fin N := eOut.symm (eIn.symm (x₀, restCols), restRows)
      have hcoord_eq (x : Fin N) (d : α) (hd : d ∈ S) :
          (eOut.symm (eIn.symm (x, restCols), restRows)) d.1 d.2 = base d.1 d.2 := by
        have hdc : d ≠ c := by
          intro h
          exact hc (h ▸ hd)
        rcases d with ⟨d₁, d₂⟩
        by_cases h₁ : d₁ = c.1
        · subst d₁
          have h₂ : d₂ ≠ c.2 := by
            intro h
            exact hdc (Prod.ext rfl h)
          simp [base, eOut, eIn, Equiv.piSplitAt, h₂]
        · simp [base, eOut, eIn, Equiv.piSplitAt, h₁]
      have hprefix_eq (x : Fin N) :
          prefixHitSet (eOut.symm (eIn.symm (x, restCols), restRows)) S =
            prefixHitSet base S := by
        ext y
        simp only [prefixHitSet, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h d hd
          have hval := hcoord_eq x d hd
          simpa [hval] using h d hd
        · intro h d hd
          have hval := hcoord_eq x d hd
          simpa [hval] using h d hd
      have hnext_eq (x : Fin N) :
          prefixHitSet (eOut.symm (eIn.symm (x, restCols), restRows)) (insert c S) =
            (prefixHitSet base S).filter (fun y => Hits E G x y) := by
        rw [hhit_insert, hprefix_eq]
        have hcur :
            (eOut.symm (eIn.symm (x, restCols), restRows)) c.1 c.2 = x := by
          simp [eOut, eIn, Equiv.piSplitAt]
        rw [hcur]
      by_cases hregular : L ≤ prefixMass base S
      · have hprefix := hprefix_exception_bound c.1 (prefixHitSet base S) (by
          simpa [prefixMass] using hregular)
        let J := prefixHitSet base S
        have hmass_prev (x : Fin N) :
            prefixMass (eOut.symm (eIn.symm (x, restCols), restRows)) S =
              squaredClusterMass ρ D J := by
          change squaredClusterMass ρ D
              (prefixHitSet (eOut.symm (eIn.symm (x, restCols), restRows)) S) =
            squaredClusterMass ρ D (prefixHitSet base S)
          rw [hprefix_eq x]
        have hmass_next (x : Fin N) :
            prefixMass (eOut.symm (eIn.symm (x, restCols), restRows)) (insert c S) =
              squaredClusterMass ρ D (J.filter (fun y => Hits E G x y)) := by
          simp [prefixMass, J, hnext_eq x]
        have hbad_eq (x : Fin N) :
            badStep (eOut.symm (eIn.symm (x, restCols), restRows)) S c ↔
              oneStepRatio J x < θ := by
          simp only [badStep]
          rw [hmass_prev x, hmass_next x]
          constructor
          · rintro ⟨_, hratio⟩
            exact hratio
          · intro hratio
            exact ⟨hregular, hratio⟩
        change (μ c.1).pr
          (fun x => badStep (eOut.symm (eIn.symm (x, restCols), restRows)) S c) ≤ pExc
        simpa [hbad_eq] using hprefix.1
      · have hfalse (x : Fin N) :
            ¬ badStep (eOut.symm (eIn.symm (x, restCols), restRows)) S c := by
          simp [badStep, prefixMass, hprefix_eq x, hregular]
        letI : DecidablePred (fun x : Fin N =>
            badStep (eOut.symm (eIn.symm (x, restCols), restRows)) S c) :=
          fun x => Classical.propDecidable _
        calc
          (∑ x, if badStep (eOut.symm (eIn.symm (x, restCols), restRows)) S c then
              (μ c.1).w x else 0) = 0 := by
            have hzero :
                (∑ x, if badStep (eOut.symm (eIn.symm (x, restCols), restRows)) S c then
                    (μ c.1).w x else 0) = ∑ x : Fin N, (0 : ℝ) := by
              apply Finset.sum_congr rfl
              intro x hx
              by_cases h : badStep (eOut.symm (eIn.symm (x, restCols), restRows)) S c
              · exact False.elim (hfalse x h)
              · simp [h]
            rw [hzero]
            simp
          _ ≤ pExc := hpExc.le
    let M : ℕ := r * k
    have hMcard : Fintype.card α = M := by simp [M, α]
    have hMreal : (M : ℝ) = (r : ℝ) * (k : ℝ) := by
      simp [M]
    let order : α ≃ Fin M := Fintype.equivFinOfCardEq hMcard
    let canonicalPrefix : Fin (M + 1) → Finset α := fun t =>
      Finset.univ.filter fun c => (order c).val < t.val
    let lastIndex : Fin (M + 1) := Fin.last M
    have hcanonical_zero : canonicalPrefix 0 = ∅ := by
      ext c
      simp [canonicalPrefix]
    have hcanonical_last : canonicalPrefix lastIndex = Finset.univ := by
      ext c
      simp [canonicalPrefix, lastIndex]
    have hcanonical_step (i : Fin M) :
        canonicalPrefix i.succ = insert (order.symm i) (canonicalPrefix i.castSucc) := by
      ext c
      simp only [canonicalPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      have hEq : c = order.symm i ↔ order c = i := by
        constructor
        · intro h
          rw [h]
          exact order.apply_symm_apply i
        · intro h
          apply order.injective
          calc
            order c = i := h
            _ = order (order.symm i) := (order.apply_symm_apply i).symm
      rw [hEq]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hfullHit (W : Fin r → Fin k → Fin N) :
        prefixHitSet W (Finset.univ : Finset α) = fixedListHitSet E G W := by
      ext y
      simp only [prefixHitSet, fixedListHitSet, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · intro h b i
        exact h (b, i) (by simp)
      · intro h c
        intro hc
        rcases c with ⟨b, i⟩
        exact h b i
    have hhalfExp : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
      have h := Real.add_one_le_exp (1 / 2 : ℝ)
      norm_num at h
      exact h
    have hExpOne : (9 / 4 : ℝ) ≤ Real.exp 1 := by
      rw [show (1 : ℝ) = 1 / 2 + 1 / 2 by norm_num, Real.exp_add]
      have hsq := mul_self_le_mul_self (by norm_num : 0 ≤ (3 / 2 : ℝ)) hhalfExp
      norm_num at hsq
      exact hsq
    have hExpTwo : (5 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have hsq := mul_self_le_mul_self (by norm_num : 0 ≤ (9 / 4 : ℝ)) hExpOne
      norm_num at hsq
      have hnum : (5 : ℝ) ≤ 81 / 16 := by norm_num
      exact hnum.trans hsq
    have hExpNegTwo : Real.exp (-2) ≤ 1 / 5 := by
      rw [Real.exp_neg]
      have h := (inv_le_inv₀ (Real.exp_pos 2) (by norm_num : 0 < (5 : ℝ))).2 hExpTwo
      simpa using h
    have hc₀lower : (49 / 100 : ℝ) ≤ c₀ := by
      dsimp [c₀]
      linarith
    have hθlower : 1 / 5 ≤ θ := by
      have hsq : (49 / 100 : ℝ) ^ 2 ≤ c₀ ^ 2 :=
        by simpa [pow_two] using mul_self_le_mul_self (by norm_num) hc₀lower
      have hnum : (1 / 5 : ℝ) ≤ (49 / 100 : ℝ) ^ 2 := by norm_num
      dsimp [θ]
      exact hnum.trans hsq
    have hθExpLower : Real.exp (-2) ≤ θ := le_trans hExpNegTwo hθlower
    have hlog4lo : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 4)]
      exact (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 4))
    have hlog4hi : Real.log 4 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 4)]
      linarith
    have hlogθlowerTwo : -2 ≤ Real.log θ := by
      calc
        -2 = Real.log (Real.exp (-2)) := by rw [Real.log_exp]
        _ ≤ Real.log θ := Real.log_le_log (Real.exp_pos _) hθExpLower
    have hθquarter : θ ≤ 1 / 4 := by
      have hc₀half : c₀ ≤ 1 / 2 := by dsimp [c₀]; linarith [haPos]
      dsimp [θ]
      nlinarith [hc₀pos, hc₀half]
    have hquarterLog : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
    have hlogθupper : Real.log θ ≤ -Real.log 4 := by
      rw [← hquarterLog]
      exact Real.log_le_log hθpos hθquarter
    have hlogθnonpos : Real.log θ ≤ 0 := by
      linarith [hlogθupper, hlog4lo]
    have hlogθ_lt_zero : Real.log θ < 0 := by
      linarith [hlogθupper, hlog4lo]
    have hlogtheta_lower : -Real.log 4 - (42 / 100 : ℝ) * a ≤ Real.log θ := by
      have hxle : a / 5 ≤ 1 / 50 := by nlinarith [ha]
      have hu : 0 < 1 - a / 5 := by linarith
      have hrec := Real.log_le_sub_one_of_pos (show 0 < (1 - a / 5)⁻¹ by positivity)
      rw [Real.log_inv] at hrec
      have hrec' : -Real.log (1 - a / 5) ≤ (a / 5) / (1 - a / 5) := by
        have heq : (1 - a / 5)⁻¹ - 1 = (a / 5) / (1 - a / 5) := by
          have h5a : (5 : ℝ) - a ≠ 0 := by linarith [ha]
          field_simp [ne_of_gt hu, h5a]
          ring
        rw [heq] at hrec
        exact hrec
      have hfrac : (a / 5) / (1 - a / 5) ≤ (21 / 100 : ℝ) * a := by
        apply (div_le_iff₀ hu).2
        nlinarith [mul_nonneg (sub_nonneg.mpr hxle) (le_of_lt haPos)]
      have hlogFactor : -(21 / 100 : ℝ) * a ≤ Real.log (1 - a / 5) := by
        linarith [hrec', hfrac]
      have hθfactor : θ = (1 / 4 : ℝ) * (1 - a / 5) ^ 2 := by
        dsimp [θ, c₀]
        ring
      have hlogEq : Real.log θ = -Real.log 4 + 2 * Real.log (1 - a / 5) := by
        rw [hθfactor, Real.log_mul (by norm_num : (1 / 4 : ℝ) ≠ 0)
          (pow_ne_zero 2 (ne_of_gt hu)), Real.log_pow, hquarterLog]
        ring
      rw [hlogEq]
      nlinarith [haPos, hlogFactor]
    have hlog_chord_target :
        Real.log θ * (3 / 4 - a) / (1 - θ) ≥
          -Real.log 4 + (13 / 20 : ℝ) * a := by
      let A : ℝ := 3 / 4 - a
      let D₀ : ℝ := 3 / 4 + (99 / 1000 : ℝ) * a
      let B : ℝ := -Real.log θ
      have hA : 0 ≤ A := by dsimp [A]; linarith [ha]
      have hD : D₀ ≤ 1 - θ := by
        dsimp [D₀, θ, c₀]
        nlinarith [sq_nonneg a, ha]
      have hden : 0 < 1 - θ := by
        linarith [hθquarter]
      have hB : B ≤ Real.log 4 + (42 / 100 : ℝ) * a := by
        dsimp [B]
        linarith [hlogtheta_lower]
      have hcoef : 0 ≤ Real.log 4 - (13 / 20 : ℝ) * a := by
        nlinarith [hlog4lo, ha]
      have hpoly :
          (Real.log 4 + (42 / 100 : ℝ) * a) * A ≤
            (Real.log 4 - (13 / 20 : ℝ) * a) * D₀ := by
        dsimp [A, D₀]
        nlinarith [mul_nonneg (sub_nonneg.mpr hlog4lo) (le_of_lt haPos), sq_nonneg a]
      have hnum : B * A ≤
          (Real.log 4 - (13 / 20 : ℝ) * a) * (1 - θ) := by
        calc
          B * A ≤ (Real.log 4 + (42 / 100 : ℝ) * a) * A :=
            mul_le_mul_of_nonneg_right hB hA
          _ ≤ (Real.log 4 - (13 / 20 : ℝ) * a) * D₀ := hpoly
          _ ≤ (Real.log 4 - (13 / 20 : ℝ) * a) * (1 - θ) :=
            mul_le_mul_of_nonneg_left hD hcoef
      have hquot : B * A / (1 - θ) ≤
          Real.log 4 - (13 / 20 : ℝ) * a := (div_le_iff₀ hden).2 hnum
      have hsign : Real.log θ * A / (1 - θ) = -(B * A / (1 - θ)) := by
        dsimp [B]
        ring
      change Real.log θ * A / (1 - θ) ≥
        -Real.log 4 + (13 / 20 : ℝ) * a
      rw [hsign]
      linarith
    have hθpowLower (t : Fin (M + 1)) : L ≤ θ ^ (t.val) := by
      have htnat : t.val ≤ M := Nat.le_of_lt_succ t.isLt
      have htreal : (t.val : ℝ) ≤ (M : ℝ) := by exact_mod_cast htnat
      have hExpNat : Real.exp (-2 * (t.val : ℝ)) = (Real.exp (-2)) ^ t.val := by
        rw [show -2 * (t.val : ℝ) = (t.val : ℝ) * (-2) by ring, Real.exp_nat_mul]
      have hbasePow : Real.exp (-2 * (t.val : ℝ)) ≤ θ ^ t.val := by
        rw [hExpNat]
        exact pow_le_pow_left₀ (Real.exp_nonneg _) hθExpLower _
      have hExpExponent : -2 * (M : ℝ) ≤ -2 * (t.val : ℝ) :=
        mul_le_mul_of_nonpos_left htreal (by norm_num)
      have hExpMono : Real.exp (-2 * (M : ℝ)) ≤ Real.exp (-2 * (t.val : ℝ)) :=
        Real.exp_le_exp.mpr hExpExponent
      have hLrewrite : L = Real.exp (-2 * (M : ℝ)) := by
        dsimp [L]
        rw [hMreal]
        congr 1
        ring
      exact hLrewrite ▸ hExpMono.trans hbasePow
    have hcanon_lower (W : Fin r → Fin k → Fin N)
        (hgood : ∀ i : Fin M,
          ¬ badStep W (canonicalPrefix i.castSucc) (order.symm i)) :
        ∀ t : Fin (M + 1),
          L ≤ prefixMass W (canonicalPrefix t) ∧
            θ ^ t.val ≤ prefixMass W (canonicalPrefix t) := by
      intro t
      induction t using Fin.induction with
      | zero =>
          have hmass0 : prefixMass W (canonicalPrefix 0) = 1 := by
            rw [hcanonical_zero]
            simp [prefixMass, prefixHitSet, hmass_univ]
          constructor
          · rw [hmass0]
            have hExp : L ≤ Real.exp 0 := by
              apply Real.exp_le_exp.mpr
              have hkr : 0 ≤ (2 : ℝ) * (k : ℝ) * (r : ℝ) := by positivity
              nlinarith [hkr]
            simpa using hExp
          · simpa [hmass0]
      | succ i ih =>
          have hprev : L ≤ prefixMass W (canonicalPrefix i.castSucc) := ih.1
          have hprevPos : 0 < prefixMass W (canonicalPrefix i.castSucc) :=
            lt_of_lt_of_le hLpos hprev
          have hratio :
              θ ≤ prefixMass W (canonicalPrefix i.succ) /
                prefixMass W (canonicalPrefix i.castSucc) := by
            by_contra hnot
            have hlt :
                prefixMass W (canonicalPrefix i.succ) /
                  prefixMass W (canonicalPrefix i.castSucc) < θ := lt_of_not_ge hnot
            apply hgood i
            refine ⟨hprev, ?_⟩
            simpa [hcanonical_step i] using hlt
          have hmul :
              θ * prefixMass W (canonicalPrefix i.castSucc) ≤
                prefixMass W (canonicalPrefix i.succ) :=
            (le_div_iff₀ hprevPos).mp hratio
          have hnext : θ ^ i.succ.val ≤ prefixMass W (canonicalPrefix i.succ) := by
            rw [Fin.val_succ, pow_succ]
            calc
              θ ^ i.val * θ ≤ prefixMass W (canonicalPrefix i.castSucc) * θ :=
                mul_le_mul_of_nonneg_right (by simpa using ih.2) (le_of_lt hθpos)
              _ = θ * prefixMass W (canonicalPrefix i.castSucc) := by ring
              _ ≤ prefixMass W (canonicalPrefix i.succ) := hmul
          refine ⟨?_, hnext⟩
          exact le_trans (hθpowLower i.succ) hnext
    have habs_subset (W : Fin r → Fin k → Fin N)
        (hfail : squaredClusterMass ρ D (fixedListHitSet E G W) < L) :
        ∃ i : Fin M,
          badStep W (canonicalPrefix i.castSucc) (order.symm i) := by
      have habs : prefixMass W (canonicalPrefix lastIndex) < L := by
        simpa [prefixMass, hcanonical_last, hfullHit W] using hfail
      by_contra hnone
      have hgood : ∀ i : Fin M,
          ¬ badStep W (canonicalPrefix i.castSucc) (order.symm i) := by
        intro i hi
        exact hnone ⟨i, hi⟩
      have hbound := hcanon_lower W hgood lastIndex
      exact (not_lt_of_ge hbound.1) habs
    have hAbsBadPr :
        P.pr (fun W => ∃ i : Fin M,
          badStep W (canonicalPrefix i.castSucc) (order.symm i)) ≤
          (M : ℝ) * pExc := by
      calc
        P.pr (fun W => ∃ i : Fin M,
            badStep W (canonicalPrefix i.castSucc) (order.symm i)) ≤
            ∑ i : Fin M, P.pr (fun W =>
              badStep W (canonicalPrefix i.castSucc) (order.symm i)) :=
          FinProb.pr_iUnion_le P _
        _ ≤ ∑ i : Fin M, pExc := by
          apply Finset.sum_le_sum
          intro i hi
          have hnot : order.symm i ∉ canonicalPrefix i.castSucc := by
            simp [canonicalPrefix]
          exact hbad_step_prob (canonicalPrefix i.castSucc) (order.symm i) hnot
        _ = (M : ℝ) * pExc := by simp
    let absFailure : (Fin r → Fin k → Fin N) → Prop := fun W =>
      squaredClusterMass ρ D (fixedListHitSet E G W) < L
    have hAbsSubset (W : Fin r → Fin k → Fin N) :
        absFailure W → ∃ i : Fin M,
          badStep W (canonicalPrefix i.castSucc) (order.symm i) := by
      intro hfail
      have hlast : prefixMass W (canonicalPrefix lastIndex) < L := by
        simpa [prefixMass, absFailure, hcanonical_last, hfullHit W] using hfail
      by_contra hnone
      have hgood : ∀ i : Fin M,
          ¬badStep W (canonicalPrefix i.castSucc) (order.symm i) := by
        intro i hi
        exact hnone ⟨i, hi⟩
      have hlastLower := (hcanon_lower W hgood lastIndex).1
      exact (not_lt_of_ge hlastLower) hlast
    have hAbsPr : P.pr absFailure ≤ (M : ℝ) * pExc := by
      calc
        P.pr absFailure ≤ P.pr (fun W => ∃ i : Fin M,
            badStep W (canonicalPrefix i.castSucc) (order.symm i)) :=
          FinProb.pr_mono P _ _ hAbsSubset
        _ ≤ (M : ℝ) * pExc := hAbsBadPr
    let deletePrefix : Fin r → Fin (k + 1) → Finset α := fun b t =>
      Finset.univ.filter fun d => d.1 ≠ b ∨ (d.1 = b ∧ (Fin.rev d.2).val < t.val)
    have hdelete_start (b : Fin r) :
        deletePrefix b (0 : Fin (k + 1)) =
          Finset.univ.filter (fun d : α => d.1 ≠ b) := by
      ext d
      simp [deletePrefix]
    have hdelete_finish (b : Fin r) : deletePrefix b (Fin.last k) = Finset.univ := by
      ext d
      rcases d with ⟨d₁, d₂⟩
      have hk' : 0 < k := by omega
      by_cases hdb : d₁ = b <;> simp [deletePrefix, hdb, hk']
    have hdelete_step (b : Fin r) (i : Fin k) :
        deletePrefix b i.succ = insert (b, Fin.rev i) (deletePrefix b i.castSucc) := by
      ext d
      rcases d with ⟨d₁, d₂⟩
      by_cases hdb : d₁ = b
      · subst d₁
        simp only [deletePrefix, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert]
        have hEq : (b, d₂) = (b, Fin.rev i) ↔ Fin.rev d₂ = i := by
          constructor
          · intro h
            have h' := congrArg (fun p : Fin k => Fin.rev p) (congrArg Prod.snd h)
            simpa [Fin.rev_rev] using h'
          · intro h
            apply Prod.ext
            · rfl
            have h' := congrArg (fun p : Fin k => Fin.rev p) h
            simpa [Fin.rev_rev] using h'
        rw [hEq]
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      · simp [deletePrefix, hdb]
    have hfull_sub_deletePrefix (W : Fin r → Fin k → Fin N) (b : Fin r)
        (t : Fin (k + 1)) :
        fixedListHitSet E G W ⊆ prefixHitSet W (deletePrefix b t) := by
      intro y hy
      simp only [fixedListHitSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [prefixHitSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro c hc
      rcases c with ⟨b', i⟩
      exact hy b' i
    have hdelete_prefix_ge_full (W : Fin r → Fin k → Fin N) (b : Fin r)
        (t : Fin (k + 1)) :
        squaredClusterMass ρ D (fixedListHitSet E G W) ≤
          prefixMass W (deletePrefix b t) := by
      change squaredClusterMass ρ D (fixedListHitSet E G W) ≤
        squaredClusterMass ρ D (prefixHitSet W (deletePrefix b t))
      exact hmass_mono _ _ (hfull_sub_deletePrefix W b t)
    have hdelete_final_eq (W : Fin r → Fin k → Fin N) (b : Fin r) :
        prefixMass W (deletePrefix b (Fin.last k)) =
          squaredClusterMass ρ D (fixedListHitSet E G W) := by
      change squaredClusterMass ρ D (prefixHitSet W (deletePrefix b (Fin.last k))) = _
      rw [hdelete_finish b, hfullHit W]
    have hdelete_start_eq (W : Fin r → Fin k → Fin N) (b : Fin r) :
        prefixMass W (deletePrefix b (0 : Fin (k + 1))) =
          squaredClusterMass ρ D (fixedListHitSetWithout E G W b) := by
      change squaredClusterMass ρ D (prefixHitSet W (deletePrefix b (0 : Fin (k + 1)))) = _
      congr 1
      ext y
      simp only [prefixHitSet, fixedListHitSetWithout, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro h b' hb' i
        exact h (b', i) (by simp [deletePrefix, hb'])
      · intro h c hc
        rcases c with ⟨b', i⟩
        have hb' : b' ≠ b := by simpa [deletePrefix] using hc
        exact h b' hb' i
    have hdelete_ratio_lower (W : Fin r → Fin k → Fin N) (b : Fin r)
        (hnoAbs : ¬ absFailure W)
        (hgood : ∀ i : Fin k,
          ¬ badStep W (deletePrefix b i.castSucc) (b, Fin.rev i)) :
        Real.exp (-2 * (k : ℝ)) ≤
          squaredClusterMass ρ D (fixedListHitSet E G W) /
            squaredClusterMass ρ D (fixedListHitSetWithout E G W b) := by
      have hmassLower : L ≤ squaredClusterMass ρ D (fixedListHitSet E G W) :=
        le_of_not_gt (by simpa [absFailure] using hnoAbs)
      have hstart : L ≤ prefixMass W (deletePrefix b (0 : Fin (k + 1))) := by
        have hmono := hdelete_prefix_ge_full W b (0 : Fin (k + 1))
        rw [hdelete_start_eq W b] at hmono
        rw [hdelete_start_eq W b]
        exact le_trans hmassLower hmono
      have hprefixLower (t : Fin (k + 1)) :
          L ≤ prefixMass W (deletePrefix b t) :=
        le_trans hmassLower (hdelete_prefix_ge_full W b t)
      have hpath : ∀ t : Fin (k + 1),
          θ ^ t.val * prefixMass W (deletePrefix b (0 : Fin (k + 1))) ≤
            prefixMass W (deletePrefix b t) := by
        intro t
        induction t using Fin.induction with
        | zero => simpa using le_rfl
        | succ i ih =>
            have ih' : θ ^ i.val * prefixMass W (deletePrefix b 0) ≤
                prefixMass W (deletePrefix b i.castSucc) := by simpa using ih
            have hratio : θ ≤
                prefixMass W (deletePrefix b i.succ) /
                  prefixMass W (deletePrefix b i.castSucc) := by
              by_contra hnot
              have hlt :
                  prefixMass W (deletePrefix b i.succ) /
                    prefixMass W (deletePrefix b i.castSucc) < θ := lt_of_not_ge hnot
              apply hgood i
              refine ⟨hprefixLower i.castSucc, ?_⟩
              simpa [hdelete_step b i] using hlt
            have hprevPos : 0 < prefixMass W (deletePrefix b i.castSucc) :=
              lt_of_lt_of_le hLpos (hprefixLower i.castSucc)
            have hmul : θ * prefixMass W (deletePrefix b i.castSucc) ≤
                prefixMass W (deletePrefix b i.succ) :=
              (le_div_iff₀ hprevPos).mp hratio
            have hnext : θ ^ i.succ.val *
                prefixMass W (deletePrefix b (0 : Fin (k + 1))) ≤
                  prefixMass W (deletePrefix b i.succ) := by
              rw [Fin.val_succ, pow_succ]
              calc
                θ ^ i.val * θ * prefixMass W (deletePrefix b 0) =
                    θ ^ i.val * prefixMass W (deletePrefix b 0) * θ := by ring
                _ ≤ prefixMass W (deletePrefix b i.castSucc) * θ :=
                  mul_le_mul_of_nonneg_right ih' (le_of_lt hθpos)
                _ = θ * prefixMass W (deletePrefix b i.castSucc) := by ring
                _ ≤ prefixMass W (deletePrefix b i.succ) := hmul
            exact hnext
      have hfinal : θ ^ k * prefixMass W (deletePrefix b (0 : Fin (k + 1))) ≤
          squaredClusterMass ρ D (fixedListHitSet E G W) := by
        simpa [hdelete_final_eq] using hpath (Fin.last k)
      have hstartPos : 0 < prefixMass W (deletePrefix b (0 : Fin (k + 1))) :=
        lt_of_lt_of_le hLpos hstart
      have hratio : θ ^ k ≤
          squaredClusterMass ρ D (fixedListHitSet E G W) /
            prefixMass W (deletePrefix b (0 : Fin (k + 1))) :=
        (le_div_iff₀ hstartPos).2 hfinal
      have hpow : Real.exp (-2 * (k : ℝ)) ≤ θ ^ k := by
        have hnat : (Real.exp (-2)) ^ k ≤ θ ^ k :=
          pow_le_pow_left₀ (Real.exp_nonneg _) hθExpLower _
        have hexp : Real.exp (-2 * (k : ℝ)) = (Real.exp (-2)) ^ k := by
          rw [show -2 * (k : ℝ) = (k : ℝ) * (-2) by ring, Real.exp_nat_mul]
        rw [hexp]
        exact hnat
      rw [← hdelete_start_eq W b]
      exact hpow.trans hratio
    have hexternal_subset (W : Fin r → Fin k → Fin N) :
        (∃ b : Fin r, ¬ FixedListOwnBlock E G ρ D (μ b) a ∧
          squaredClusterMass ρ D (fixedListHitSet E G W) /
            squaredClusterMass ρ D (fixedListHitSetWithout E G W b) <
              Real.exp (-2 * (k : ℝ))) →
          absFailure W ∨ ∃ c : α,
            badStep W (deletePrefix c.1 (Fin.rev c.2).castSucc) c := by
      rintro ⟨b, hnotOwn, hratio⟩
      by_cases hfail : absFailure W
      · exact Or.inl hfail
      · right
        by_contra hnone
        have hgood (i : Fin k) :
            ¬ badStep W (deletePrefix b i.castSucc) (b, Fin.rev i) := by
          intro hbad
          apply hnone
          refine ⟨(b, Fin.rev i), ?_⟩
          simpa [Fin.rev_rev] using hbad
        have hlower := hdelete_ratio_lower W b hfail hgood
        exact (not_lt_of_ge hlower) hratio
    have hdelete_bad_Pr :
        P.pr (fun W => ∃ c : α,
          badStep W (deletePrefix c.1 (Fin.rev c.2).castSucc) c) ≤ (M : ℝ) * pExc := by
      calc
        P.pr (fun W => ∃ c : α,
            badStep W (deletePrefix c.1 (Fin.rev c.2).castSucc) c) ≤
            ∑ c : α, P.pr (fun W => badStep W (deletePrefix c.1 (Fin.rev c.2).castSucc) c) :=
          FinProb.pr_iUnion_le P _
        _ ≤ ∑ c : α, pExc := by
          apply Finset.sum_le_sum
          intro c hc
          have hnot : c ∉ deletePrefix c.1 (Fin.rev c.2).castSucc := by
            simp [deletePrefix]
          exact hbad_step_prob (deletePrefix c.1 (Fin.rev c.2).castSucc) c hnot
        _ = (M : ℝ) * pExc := by simp [M, α]
    have hstepBad_union :
        P.pr (fun W => absFailure W ∨ ∃ c : α,
          badStep W (deletePrefix c.1 (Fin.rev c.2).castSucc) c) ≤ 2 * (M : ℝ) * pExc := by
      calc
        _ ≤ P.pr absFailure +
              P.pr (fun W => ∃ c : α,
                badStep W (deletePrefix c.1 (Fin.rev c.2).castSucc) c) :=
          FinProb.pr_union_le P absFailure (fun W => ∃ c : α,
            badStep W (deletePrefix c.1 (Fin.rev c.2).castSucc) c)
        _ ≤ (M : ℝ) * pExc + (M : ℝ) * pExc := add_le_add hAbsPr hdelete_bad_Pr
        _ = 2 * (M : ℝ) * pExc := by ring
    have hstepBad_bound :
        P.pr (fun W => absFailure W ∨ ∃ c : α,
          badStep W (deletePrefix c.1 (Fin.rev c.2).castSucc) c) ≤
            Real.exp (-(a ^ 2 * (k : ℝ)) / 50) := by
      calc
        _ ≤ 2 * (M : ℝ) * pExc := hstepBad_union
        _ ≤ ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * pExc := by
          have hfactor : 2 * (M : ℝ) ≤ ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) := by
            rw [hMreal]
            have hrReal : (1 : ℝ) ≤ (r : ℝ) := by
              exact_mod_cast (Nat.succ_le_iff.mpr hrPos)
            calc
              2 * ((r : ℝ) * (k : ℝ)) ≤
                  ((r : ℝ) + 1) * ((r : ℝ) * (k : ℝ)) :=
                mul_le_mul_of_nonneg_right (by linarith) (by positivity)
              _ = ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) := by ring
          exact mul_le_mul_of_nonneg_right hfactor hpExc.le
        _ ≤ Real.exp (-(a ^ 2 * (k : ℝ)) / 50) := by
          simpa [pExc] using hexception
    let ownMean : ℝ := -Real.log 4 + (13 / 20 : ℝ) * a
    let ownRatio : Fin r → Fin k → (Fin r → Fin k → Fin N) → ℝ := fun b i W =>
      prefixMass W (deletePrefix b i.succ) / prefixMass W (deletePrefix b i.castSucc)
    let ownDelta : Fin r → Fin k → (Fin r → Fin k → Fin N) → ℝ := fun b i W =>
      if L ≤ prefixMass W (deletePrefix b i.castSucc) then
        Real.log (max θ (ownRatio b i W)) else ownMean
    have hown_ratio_bounds (b : Fin r) (i : Fin k) (W : Fin r → Fin k → Fin N)
        (hactive : L ≤ prefixMass W (deletePrefix b i.castSucc)) :
        0 ≤ ownRatio b i W ∧ ownRatio b i W ≤ 1 := by
      have hset : prefixHitSet W (deletePrefix b i.succ) ⊆
          prefixHitSet W (deletePrefix b i.castSucc) := by
        rw [hdelete_step b i, hhit_insert]
        exact Finset.filter_subset _ _
      have hmass : prefixMass W (deletePrefix b i.succ) ≤
          prefixMass W (deletePrefix b i.castSucc) := by
        change squaredClusterMass ρ D (prefixHitSet W (deletePrefix b i.succ)) ≤
          squaredClusterMass ρ D (prefixHitSet W (deletePrefix b i.castSucc))
        exact hmass_mono _ _ hset
      have hnum : 0 ≤ prefixMass W (deletePrefix b i.succ) :=
        hmass_nonneg _
      have hden : 0 < prefixMass W (deletePrefix b i.castSucc) :=
        lt_of_lt_of_le hLpos hactive
      constructor
      · exact div_nonneg hnum hden.le
      · exact (div_le_one hden).2 hmass
    have hclipped_log_mean (b : Fin r) (J : Finset (Fin N))
        (hJ : L ≤ squaredClusterMass ρ D J)
        (hown : FixedListOwnBlock E G ρ D (μ b) a) :
        (μ b).expect (fun x => Real.log (max θ (oneStepRatio J x))) ≥ ownMean := by
      have hqbounds (x : Fin N) : 0 ≤ oneStepRatio J x ∧ oneStepRatio J x ≤ 1 := by
        have hnum : 0 ≤ squaredClusterMass ρ D (J.filter (fun y => Hits E G x y)) :=
          hmass_nonneg _
        have hden : 0 < squaredClusterMass ρ D J := lt_of_lt_of_le hLpos hJ
        have hsubset : J.filter (fun y => Hits E G x y) ⊆ J := Finset.filter_subset _ _
        have hle := hmass_mono _ _ hsubset
        constructor
        · exact div_nonneg hnum hden.le
        · exact (div_le_one hden).2 hle
      have hqmean := (hprefix_exception_bound b J hJ).2 hown
      have hchord := FinProb.expect_log_max_ge_chord (μ b) θ
        (oneStepRatio J) hθpos (lt_of_le_of_lt hθquarter (by norm_num)) hqbounds
      have hden : 0 < 1 - θ := by linarith [hθquarter]
      have hnum : Real.log θ * (3 / 4 - a) ≤
          Real.log θ * (1 - (μ b).expect (oneStepRatio J)) := by
        apply mul_le_mul_of_nonpos_left _ hlogθnonpos
        linarith
      have hquot : Real.log θ * (3 / 4 - a) / (1 - θ) ≤
          Real.log θ * (1 - (μ b).expect (oneStepRatio J)) / (1 - θ) :=
        div_le_div_of_nonneg_right hnum hden.le
      calc
        (μ b).expect (fun x => Real.log (max θ (oneStepRatio J x))) ≥
            Real.log θ * (1 - (μ b).expect (oneStepRatio J)) / (1 - θ) := hchord
        _ ≥ Real.log θ * (3 / 4 - a) / (1 - θ) := hquot
        _ ≥ ownMean := by simpa [ownMean] using hlog_chord_target
    let H : Fin (k + 1) → Type := fun _ => Fin k → Fin N
    let history : ∀ t, (Fin k → Fin N) → H t := fun t row j =>
      if j.val < t.val then row (Fin.rev j) else x₀
    let project : ∀ i : Fin k, H i.succ → H i.castSucc := fun i h j =>
      if j = i then x₀ else h j
    have hfiltration (i : Fin k) (row : Fin k → Fin N) :
        history i.castSucc row = project i (history i.succ row) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [history, project]
      · by_cases hprev : j.val < i.val
        · have hnext : j.val < i.succ.val := by
            simp only [Fin.val_succ]
            omega
          simp [history, project, hji, hprev, hnext] <;> omega
        · have hnext : ¬ j.val < i.succ.val := by
            simp only [Fin.val_succ]
            omega
          simp [history, project, hji, hprev, hnext] <;> omega
    have hown_delta_bound (b : Fin r) (i : Fin k) (W : Fin r → Fin k → Fin N) :
        -2 ≤ ownDelta b i W ∧ ownDelta b i W ≤ 0 := by
      by_cases hactive : L ≤ prefixMass W (deletePrefix b i.castSucc)
      · have hdelta : ownDelta b i W = Real.log (max θ (ownRatio b i W)) := by
          simp [ownDelta, hactive]
        rw [hdelta]
        have hq := hown_ratio_bounds b i W hactive
        have hmax0 : 0 < max θ (ownRatio b i W) :=
          lt_of_lt_of_le hθpos (le_max_left _ _)
        have hmax1 : max θ (ownRatio b i W) ≤ 1 := max_le (by linarith [hθle]) hq.2
        constructor
        · exact le_trans hlogθlowerTwo (Real.log_le_log hθpos (le_max_left _ _))
        · calc
            Real.log (max θ (ownRatio b i W)) ≤ Real.log 1 :=
              Real.log_le_log hmax0 hmax1
            _ = 0 := by simp
      · have hdelta : ownDelta b i W = ownMean := by simp [ownDelta, hactive]
        rw [hdelta]
        have hlow : -2 ≤ ownMean := by
          dsimp [ownMean]
          linarith [hlog4hi, haPos]
        have hhigh : ownMean ≤ 0 := by
          dsimp [ownMean]
          nlinarith [hlog4lo, ha]
        exact ⟨hlow, hhigh⟩
    have hwidthAzuma_pos : 0 < (4 : ℝ) * (k : ℝ) := by positivity
    have hwidthAzuma_eq :
        (∑ i : Fin k, ((0 : ℝ) - (-2 : ℝ)) ^ 2) = 4 * (k : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul] <;> ring
    let outEquiv : ∀ b : Fin r,
        (Fin r → Fin k → Fin N) ≃
          ((Fin k → Fin N) × (∀ j : {j // j ≠ b}, Fin k → Fin N)) :=
      fun b => Equiv.piSplitAt b (fun _ : Fin r => Fin k → Fin N)
    have hmean_row (b : Fin r)
        (restRows : ∀ j : {j // j ≠ b}, Fin k → Fin N)
        (hown : FixedListOwnBlock E G ρ D (μ b) a)
        (i : Fin k) (h : H i.castSucc) :
        (Rows b).pr (fun row => history i.castSucc row = h) = 0 ∨
          ownMean * (Rows b).pr (fun row => history i.castSucc row = h) ≤
            ∑ row, if history i.castSucc row = h then
              (Rows b).w row * ownDelta b i ((outEquiv b).symm (row, restRows)) else 0 := by
      classical
      right
      let c : Fin k := Fin.rev i
      let eIn := Equiv.piSplitAt c (fun _ : Fin k => Fin N)
      let R : FinProb (∀ j : {j // j ≠ c}, Fin N) :=
        FinProb.pi (fun _ : {j // j ≠ c} => μ b)
      let fiber : (Fin k → Fin N) → Prop := fun row => history i.castSucc row = h
      let Delta : (Fin k → Fin N) → ℝ := fun row =>
        ownDelta b i ((outEquiv b).symm (row, restRows))
      let rowAt : Fin N → (∀ j : {j // j ≠ c}, Fin N) → (Fin k → Fin N) :=
        fun x rest => eIn.symm (x, rest)
      let baseRow : (∀ j : {j // j ≠ c}, Fin N) → Fin k → Fin N :=
        fun rest => rowAt x₀ rest
      let fullAt : Fin N → (∀ j : {j // j ≠ c}, Fin N) → Fin r → Fin k → Fin N :=
        fun x rest => (outEquiv b).symm (rowAt x rest, restRows)
      let fullBase : (∀ j : {j // j ≠ c}, Fin N) → Fin r → Fin k → Fin N :=
        fun rest => (outEquiv b).symm (baseRow rest, restRows)
      let S : Finset α := deletePrefix b i.castSucc
      let J : (∀ j : {j // j ≠ c}, Fin N) → Finset (Fin N) :=
        fun rest => prefixHitSet (fullBase rest) S
      have hhistory_eq (rest : ∀ j : {j // j ≠ c}, Fin N) (x : Fin N) :
          history i.castSucc (rowAt x rest) = history i.castSucc (baseRow rest) := by
        funext j
        by_cases hprev : j.val < i.val
        · have hjneq : j ≠ i := by
            intro hj
            subst j
            simp at hprev
          have hrevjc : Fin.rev j ≠ c := by
            intro hj
            have hj' := congrArg Fin.rev hj
            apply hjneq
            simpa [c, Fin.rev_rev] using hj'
          simp [history, rowAt, baseRow, eIn, Equiv.piSplitAt, hrevjc, hprev]
        · simp [history, hprev]
      have hfiber_eq (rest : ∀ j : {j // j ≠ c}, Fin N) (x : Fin N) :
          fiber (rowAt x rest) ↔ fiber (baseRow rest) := by
        simp [fiber, hhistory_eq rest x]
      have hcoord (rest : ∀ j : {j // j ≠ c}, Fin N) (x : Fin N)
          (d : α) (hd : d ∈ S) :
          fullAt x rest d.1 d.2 = fullBase rest d.1 d.2 := by
        rcases d with ⟨b', j⟩
        by_cases hb' : b' = b
        · subst b'
          have hcond : (Fin.rev j).val < i.castSucc.val := by
            have hmem := (Finset.mem_filter.mp hd).2
            simpa [S, deletePrefix] using hmem
          have hjc : j ≠ c := by
            intro hj
            subst j
            simp [c, Fin.rev_rev] at hcond
          simp [fullAt, fullBase, outEquiv, rowAt, baseRow, eIn,
            Equiv.piSplitAt, hjc]
        · simp [fullAt, fullBase, outEquiv, rowAt, baseRow, eIn,
            Equiv.piSplitAt, hb']
      have hpriorHit (rest : ∀ j : {j // j ≠ c}, Fin N) (x : Fin N) :
          prefixHitSet (fullAt x rest) S = J rest := by
        ext y
        have hmemX : y ∈ prefixHitSet (fullAt x rest) S ↔
            ∀ d ∈ S, Hits E G (fullAt x rest d.1 d.2) y := by simp [prefixHitSet]
        have hmemBase : y ∈ J rest ↔
            ∀ d ∈ S, Hits E G (fullBase rest d.1 d.2) y := by simp [J, prefixHitSet]
        rw [hmemX, hmemBase]
        constructor
        · intro hy d hd
          have hh := hy d hd
          rw [hcoord rest x d hd] at hh
          exact hh
        · intro hy d hd
          rw [hcoord rest x d hd]
          exact hy d hd
      have hcurrent (rest : ∀ j : {j // j ≠ c}, Fin N) (x : Fin N) :
          fullAt x rest b c = x := by
        simp [fullAt, outEquiv, rowAt, eIn, c, Equiv.piSplitAt]
      have hpostHit (rest : ∀ j : {j // j ≠ c}, Fin N) (x : Fin N) :
          prefixHitSet (fullAt x rest) (deletePrefix b i.succ) =
            (J rest).filter (fun y => Hits E G x y) := by
        rw [hdelete_step b i, hhit_insert, hpriorHit rest x, hcurrent rest x]
      have hratioEq (rest : ∀ j : {j // j ≠ c}, Fin N) (x : Fin N) :
          ownRatio b i (fullAt x rest) = oneStepRatio (J rest) x := by
        change
          squaredClusterMass ρ D
              (prefixHitSet (fullAt x rest) (deletePrefix b i.succ)) /
            squaredClusterMass ρ D (prefixHitSet (fullAt x rest) S) =
          squaredClusterMass ρ D ((J rest).filter (fun y => Hits E G x y)) /
            squaredClusterMass ρ D (J rest)
        rw [hpostHit rest x, hpriorHit rest x]
      have hactiveEq (rest : ∀ j : {j // j ≠ c}, Fin N) (x : Fin N) :
          (L ≤ prefixMass (fullAt x rest) S) ↔
            L ≤ squaredClusterMass ρ D (J rest) := by
        change L ≤ squaredClusterMass ρ D (prefixHitSet (fullAt x rest) S) ↔ _
        rw [hpriorHit rest x]
      have hdeltaEq (rest : ∀ j : {j // j ≠ c}, Fin N) (x : Fin N) :
          ownDelta b i (fullAt x rest) =
            if L ≤ squaredClusterMass ρ D (J rest) then
              Real.log (max θ (oneStepRatio (J rest) x)) else ownMean := by
        by_cases hbase : L ≤ squaredClusterMass ρ D (J rest)
        · have hactive := (hactiveEq rest x).2 hbase
          have hactive' : L ≤ prefixMass (fullAt x rest) (deletePrefix b i.castSucc) := by
            simpa [S] using hactive
          simp [ownDelta, hactive', hbase, hratioEq rest x]
        · have hactive : ¬ L ≤ prefixMass (fullAt x rest) S := by
            intro h
            exact hbase ((hactiveEq rest x).1 h)
          have hactive' : ¬ L ≤ prefixMass (fullAt x rest) (deletePrefix b i.castSucc) := by
            simpa [S] using hactive
          simp [ownDelta, hactive', hbase]
      have hinner (rest : ∀ j : {j // j ≠ c}, Fin N) :
          ownMean * (if fiber (baseRow rest) then (1 : ℝ) else 0) ≤
            ∑ x, (μ b).w x *
              ((if fiber (rowAt x rest) then (1 : ℝ) else 0) *
                ownDelta b i (fullAt x rest)) := by
        have hfiber (x : Fin N) : fiber (rowAt x rest) ↔ fiber (baseRow rest) :=
          hfiber_eq rest x
        by_cases hf : fiber (baseRow rest)
        · simp only [if_pos hf, one_mul]
          by_cases hactive : L ≤ squaredClusterMass ρ D (J rest)
          · have hmean := hclipped_log_mean b (J rest) hactive hown
            have hdelta (x : Fin N) : ownDelta b i (fullAt x rest) =
                Real.log (max θ (oneStepRatio (J rest) x)) := by
              simp [hdeltaEq rest x, hactive]
            simp_rw [hfiber, hdelta]
            simpa [hf, FinProb.expect] using hmean.le
          · have hdelta (x : Fin N) : ownDelta b i (fullAt x rest) = ownMean := by
              simp [hdeltaEq rest x, hactive]
            simp_rw [hfiber, hdelta, hf]
            have hconst : (∑ x, (μ b).w x * ownMean) = ownMean := by
              calc
                (∑ x, (μ b).w x * ownMean) = (∑ x, (μ b).w x) * ownMean := by
                  rw [← Finset.sum_mul]
                _ = ownMean := by rw [(μ b).sum_eq_one]; ring
            simp only [if_pos (show True from trivial), one_mul, mul_one]
            rw [hconst]
        · simp [hf, hfiber]
      have hweighted_eq :
          (∑ row, if fiber row then (Rows b).w row * Delta row else 0) =
            (Rows b).expect (fun row =>
              (if fiber row then (1 : ℝ) else 0) * Delta row) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro row hrow
        by_cases hf : fiber row <;> simp [hf]
      have hpr_eq :
          (Rows b).pr fiber =
            ∑ rest, R.w rest * (if fiber (baseRow rest) then (1 : ℝ) else 0) := by
        have hpr_expect : (Rows b).pr fiber =
            (Rows b).expect (fun row => if fiber row then (1 : ℝ) else 0) := by
          unfold FinProb.pr FinProb.expect
          apply Finset.sum_congr rfl
          intro row hrow
          by_cases hf : fiber row <;> simp [hf]
        rw [hpr_expect]
        have hsplit := FinProb.expect_piSplitAt_eq
          (fun _ : Fin k => μ b) c (fun row => if fiber row then (1 : ℝ) else 0)
        calc
          (Rows b).expect (fun row => if fiber row then (1 : ℝ) else 0) =
              ∑ rest, R.w rest *
                (∑ x, (μ b).w x *
                  (if fiber (rowAt x rest) then (1 : ℝ) else 0)) := by
              simpa [Rows, R, rowAt, eIn] using hsplit
          _ = ∑ rest, R.w rest * (if fiber (baseRow rest) then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro rest hrest
            by_cases hf : fiber (baseRow rest)
            · have hall (x : Fin N) : fiber (rowAt x rest) :=
                (hfiber_eq rest x).2 hf
              have hsum1 : (∑ x, (μ b).w x *
                  (if fiber (rowAt x rest) then (1 : ℝ) else 0)) = 1 := by
                calc
                  (∑ x, (μ b).w x *
                      (if fiber (rowAt x rest) then (1 : ℝ) else 0)) =
                      ∑ x, (μ b).w x := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    simp [hall x]
                  _ = 1 := (μ b).sum_eq_one
              calc
                R.w rest * (∑ x, (μ b).w x *
                    (if fiber (rowAt x rest) then (1 : ℝ) else 0)) = R.w rest * 1 :=
                  congrArg (fun t : ℝ => R.w rest * t) hsum1
                _ = R.w rest * (if fiber (baseRow rest) then (1 : ℝ) else 0) := by simp [hf]
            · have hnone (x : Fin N) : ¬ fiber (rowAt x rest) := by
                intro hx
                exact hf ((hfiber_eq rest x).1 hx)
              have hsum0 : (∑ x, (μ b).w x *
                  (if fiber (rowAt x rest) then (1 : ℝ) else 0)) = 0 := by
                apply Finset.sum_eq_zero
                intro x hx
                simp [hnone x]
              calc
                R.w rest * (∑ x, (μ b).w x *
                    (if fiber (rowAt x rest) then (1 : ℝ) else 0)) = R.w rest * 0 :=
                  congrArg (fun t : ℝ => R.w rest * t) hsum0
                _ = R.w rest * (if fiber (baseRow rest) then (1 : ℝ) else 0) := by simp [hf]
      have hweighted_split :
          (Rows b).expect (fun row =>
              (if fiber row then (1 : ℝ) else 0) * Delta row) =
            ∑ rest, R.w rest *
              (∑ x, (μ b).w x *
                ((if fiber (rowAt x rest) then (1 : ℝ) else 0) *
                  ownDelta b i (fullAt x rest))) := by
        have hsplit := FinProb.expect_piSplitAt_eq
          (fun _ : Fin k => μ b) c (fun row =>
            (if fiber row then (1 : ℝ) else 0) * Delta row)
        simpa [Rows, R, Delta, fullAt, rowAt, eIn, outEquiv] using hsplit
      rw [hweighted_eq, hweighted_split, hpr_eq]
      calc
        ownMean * (∑ rest, R.w rest *
            (if fiber (baseRow rest) then (1 : ℝ) else 0)) =
            ∑ rest, R.w rest *
              (ownMean * (if fiber (baseRow rest) then (1 : ℝ) else 0)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro rest hrest
                ring
        _ ≤ ∑ rest, R.w rest *
              (∑ x, (μ b).w x *
                ((if fiber (rowAt x rest) then (1 : ℝ) else 0) *
                  ownDelta b i (fullAt x rest))) := by
          apply Finset.sum_le_sum
          intro rest hrest
          exact mul_le_mul_of_nonneg_left (hinner rest) (R.nonneg rest)
    have hAzuma_row (b : Fin r)
        (restRows : ∀ j : {j // j ≠ b}, Fin k → Fin N)
        (hown : FixedListOwnBlock E G ρ D (μ b) a) :
        (Rows b).pr (fun row =>
          ∑ i : Fin k, ownDelta b i ((outEquiv b).symm (row, restRows)) <
            (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ)) ≤
          Real.exp (-(a ^ 2 * (k : ℝ)) / 32) := by
      let AzDelta : Fin k → (Fin k → Fin N) → ℝ := fun i row =>
        ownDelta b i ((outEquiv b).symm (row, restRows))
      let tAz : ℝ := (a / 4) * (k : ℝ)
      have htAz : 0 < tAz := by dsimp [tAz]; positivity
      have hboundAz (i : Fin k) (row : Fin k → Fin N) :
          -2 ≤ AzDelta i row ∧ AzDelta i row ≤ 0 := by
        exact hown_delta_bound b i ((outEquiv b).symm (row, restRows))
      have hadaptedAz (m : ℕ) (hm : m ≤ k) (j : Fin k) (hjm : j.val < m)
          (row row' : Fin k → Fin N)
          (hh : history ⟨m, Nat.lt_succ_of_le hm⟩ row =
            history ⟨m, Nat.lt_succ_of_le hm⟩ row') : AzDelta j row = AzDelta j row' := by
        let Wrow := fun R => (outEquiv b).symm (R, restRows)
        have harrayAt (t : Fin (k + 1)) (ht : t.val ≤ m) (d : α) (hd : d ∈ deletePrefix b t) :
            Wrow row d.1 d.2 = Wrow row' d.1 d.2 := by
          rcases d with ⟨b', j'⟩
          by_cases hb' : b' = b
          · subst b'
            have hcond : (Fin.rev j').val < t.val := by
              have hmem := (Finset.mem_filter.mp hd).2
              simpa [deletePrefix] using hmem
            have hpos : (Fin.rev j').val < m := hcond.trans_le ht
            have hstate := congrFun hh (Fin.rev j')
            have hentry : row j' = row' j' := by
              change (if (Fin.rev j').val < m then
                  row (Fin.rev (Fin.rev j')) else x₀) =
                if (Fin.rev j').val < m then
                  row' (Fin.rev (Fin.rev j')) else x₀ at hstate
              simp only [if_pos hpos] at hstate
              simpa [Fin.rev_rev] using hstate
            simp [Wrow, outEquiv, hentry]
          · simp [Wrow, outEquiv, hb']
        have htpre : (j.castSucc : Fin (k + 1)).val ≤ m := by
          simp only [Fin.val_castSucc]
          omega
        have htpost : j.succ.val ≤ m := by
          simp only [Fin.val_succ]
          omega
        have hsetEq (t : Fin (k + 1)) (ht : t.val ≤ m) :
            prefixHitSet (Wrow row) (deletePrefix b t) =
              prefixHitSet (Wrow row') (deletePrefix b t) := by
          ext y
          have hmemL : y ∈ prefixHitSet (Wrow row) (deletePrefix b t) ↔
              ∀ d ∈ deletePrefix b t, Hits E G (Wrow row d.1 d.2) y := by
            simp [prefixHitSet]
          have hmemR : y ∈ prefixHitSet (Wrow row') (deletePrefix b t) ↔
              ∀ d ∈ deletePrefix b t, Hits E G (Wrow row' d.1 d.2) y := by
            simp [prefixHitSet]
          rw [hmemL, hmemR]
          constructor
          · intro hy d hd
            have hh' := hy d hd
            rw [harrayAt t ht d hd] at hh'
            exact hh'
          · intro hy d hd
            have hh' := hy d hd
            rw [harrayAt t ht d hd]
            exact hh'
        have hpre : prefixMass (Wrow row) (deletePrefix b j.castSucc) =
            prefixMass (Wrow row') (deletePrefix b j.castSucc) := by
          unfold prefixMass
          rw [hsetEq j.castSucc htpre]
        have hpost : prefixMass (Wrow row) (deletePrefix b j.succ) =
            prefixMass (Wrow row') (deletePrefix b j.succ) := by
          unfold prefixMass
          rw [hsetEq j.succ htpost]
        have hratio : ownRatio b j (Wrow row) = ownRatio b j (Wrow row') := by
          simp [ownRatio, hpre, hpost]
        by_cases hactive : L ≤ prefixMass (Wrow row) (deletePrefix b j.castSucc)
        · have hactive' : L ≤ prefixMass (Wrow row') (deletePrefix b j.castSucc) := by
            rw [← hpre]
            exact hactive
          simp [AzDelta, ownDelta, Wrow, hactive, hactive', hratio]
        · have hactive' : ¬ L ≤ prefixMass (Wrow row') (deletePrefix b j.castSucc) := by
            intro h
            exact hactive (by rw [hpre]; exact h)
          simp [AzDelta, ownDelta, Wrow, hactive, hactive']
      have hsumMean :
          (∑ i : Fin k, (fun _ : Fin k => ownMean) i) - tAz =
            (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ) := by
        simp [tAz, ownMean, Finset.sum_const, nsmul_eq_mul] <;> ring
      have hsumMean' : (k : ℝ) * ownMean - tAz =
          (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ) := by
        dsimp [ownMean, tAz]
        ring
      have harg : -2 * tAz ^ 2 / (4 * (k : ℝ)) =
          -(a ^ 2 * (k : ℝ)) / 32 := by
        dsimp [tAz]
        field_simp [ne_of_gt (show (0 : ℝ) < 4 * (k : ℝ) by positivity)]
        ring
      have hAz := p_s10_1c_xAzuma H (Rows b) history project hfiltration AzDelta hadaptedAz
        (fun _ : Fin k => ownMean) (fun _ : Fin k => (-2 : ℝ)) (fun _ : Fin k => (0 : ℝ))
        hboundAz (hmean_row b restRows hown) (by
          simpa [hwidthAzuma_eq] using hwidthAzuma_pos) tAz htAz
      simp [Finset.card_univ, Fintype.card_fin] at hAz
      have hdenExp : (k : ℝ) * (2 : ℝ) ^ 2 = 4 * (k : ℝ) := by ring
      have harg' : -(2 * tAz ^ 2) / (4 * (k : ℝ)) =
          -(a ^ 2 * (k : ℝ)) / 32 := by
        calc
          -(2 * tAz ^ 2) / (4 * (k : ℝ)) = -2 * tAz ^ 2 / (4 * (k : ℝ)) := by ring
          _ = _ := harg
      rw [hdenExp, hsumMean', harg'] at hAz
      simpa [AzDelta] using hAz
    have hownPr (b : Fin r) (hown : FixedListOwnBlock E G ρ D (μ b) a) :
        (FinProb.pi Rows).pr (fun W =>
          ∑ i : Fin k, ownDelta b i W <
            (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ)) ≤
          Real.exp (-(a ^ 2 * (k : ℝ)) / 32) := by
      apply FinProb.pr_piSplitAt_le Rows b _ _ (by positivity)
      intro restRows
      have h := hAzuma_row b restRows hown
      simpa [FinProb.pr, outEquiv] using h
    let stepFailure : (Fin r → Fin k → Fin N) → Prop := fun W =>
      absFailure W ∨ ∃ c : α,
        badStep W (deletePrefix c.1 (Fin.rev c.2).castSucc) c
    have hown_failure_subset (W : Fin r → Fin k → Fin N) :
        (∃ b : Fin r, FixedListOwnBlock E G ρ D (μ b) a ∧
          squaredClusterMass ρ D (fixedListHitSet E G W) /
            squaredClusterMass ρ D (fixedListHitSetWithout E G W b) <
              Real.exp ((-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ))) →
          stepFailure W ∨ ∃ b : Fin r, FixedListOwnBlock E G ρ D (μ b) a ∧
            ∑ i : Fin k, ownDelta b i W <
              (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ) := by
      rintro ⟨b, hown, hratioBad⟩
      by_cases hbad : stepFailure W
      · exact Or.inl hbad
      · right
        have hnoAbs : ¬ absFailure W := by
          intro h
          exact hbad (Or.inl h)
        have hmassLower : L ≤ squaredClusterMass ρ D (fixedListHitSet E G W) :=
          le_of_not_gt (by simpa [absFailure] using hnoAbs)
        have hprefixLower (t : Fin (k + 1)) :
            L ≤ prefixMass W (deletePrefix b t) :=
          le_trans hmassLower (hdelete_prefix_ge_full W b t)
        have hgood (i : Fin k) :
            ¬ badStep W (deletePrefix b i.castSucc) (b, Fin.rev i) := by
          intro hstep
          apply hbad
          right
          refine ⟨(b, Fin.rev i), ?_⟩
          simpa [Fin.rev_rev] using hstep
        have hratioLower (i : Fin k) : θ ≤ ownRatio b i W := by
          by_contra hnot
          have hlt : ownRatio b i W < θ := lt_of_not_ge hnot
          apply hgood i
          refine ⟨hprefixLower i.castSucc, ?_⟩
          simpa [ownRatio, hdelete_step b i] using hlt
        have hdeltaEq (i : Fin k) :
            ownDelta b i W = Real.log (ownRatio b i W) := by
          simp [ownDelta, hprefixLower i.castSucc, max_eq_right (hratioLower i)]
        have hprePos (i : Fin k) : 0 < prefixMass W (deletePrefix b i.castSucc) :=
          lt_of_lt_of_le hLpos (hprefixLower i.castSucc)
        have hpostPos (i : Fin k) : 0 < prefixMass W (deletePrefix b i.succ) := by
          have hmul : θ * prefixMass W (deletePrefix b i.castSucc) ≤
              prefixMass W (deletePrefix b i.succ) :=
            (le_div_iff₀ (hprePos i)).mp (hratioLower i)
          exact lt_of_lt_of_le (mul_pos hθpos (hprePos i)) hmul
        have hlogRatio (i : Fin k) :
            Real.log (ownRatio b i W) =
              Real.log (prefixMass W (deletePrefix b i.succ)) -
                Real.log (prefixMass W (deletePrefix b i.castSucc)) := by
          dsimp [ownRatio]
          exact Real.log_div (ne_of_gt (hpostPos i)) (ne_of_gt (hprePos i))
        let u : Fin (k + 1) → ℝ := fun t => prefixMass W (deletePrefix b t)
        let f : Fin (k + 1) → ℝ := fun t => Real.log (u t)
        have hsumTel :
            (∑ i : Fin k, (f i.succ - f i.castSucc)) = f (Fin.last k) - f 0 := by
          rw [Finset.sum_sub_distrib]
          have hsumSucc := Fin.sum_univ_succ f
          have hsumCast := Fin.sum_univ_castSucc f
          have hsucc : (∑ i : Fin k, f i.succ) = (∑ t : Fin (k + 1), f t) - f 0 := by
            linarith
          have hcast : (∑ i : Fin k, f i.castSucc) =
              (∑ t : Fin (k + 1), f t) - f (Fin.last k) := by
            linarith
          rw [hsucc, hcast]
          ring
        have hsumDelta :
            (∑ i : Fin k, ownDelta b i W) =
              Real.log (squaredClusterMass ρ D (fixedListHitSet E G W) /
                squaredClusterMass ρ D (fixedListHitSetWithout E G W b)) := by
          calc
            (∑ i : Fin k, ownDelta b i W) =
                ∑ i : Fin k, (f i.succ - f i.castSucc) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hdeltaEq i, hlogRatio i]
            _ = f (Fin.last k) - f 0 := hsumTel
            _ = _ := by
              dsimp [f, u]
              rw [hdelete_final_eq W b, hdelete_start_eq W b]
              have hfullPos : 0 < squaredClusterMass ρ D (fixedListHitSet E G W) :=
                lt_of_lt_of_le hLpos hmassLower
              have hwithoutPos :
                  0 < squaredClusterMass ρ D (fixedListHitSetWithout E G W b) := by
                have hs := hprefixLower (0 : Fin (k + 1))
                rw [hdelete_start_eq W b] at hs
                exact lt_of_lt_of_le hLpos hs
              symm
              exact Real.log_div (ne_of_gt hfullPos) (ne_of_gt hwithoutPos)
        have hratioPos :
            0 < squaredClusterMass ρ D (fixedListHitSet E G W) /
              squaredClusterMass ρ D (fixedListHitSetWithout E G W b) :=
          div_pos (lt_of_lt_of_le hLpos hmassLower)
            (by
              have hs := hprefixLower (0 : Fin (k + 1))
              rw [hdelete_start_eq W b] at hs
              exact lt_of_lt_of_le hLpos hs)
        have hlogBad :
            Real.log (squaredClusterMass ρ D (fixedListHitSet E G W) /
              squaredClusterMass ρ D (fixedListHitSetWithout E G W b)) <
                (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ) := by
          calc
            _ < Real.log (Real.exp ((-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ))) :=
              Real.log_lt_log hratioPos hratioBad
            _ = _ := by rw [Real.log_exp]
        refine ⟨b, hown, ?_⟩
        rw [hsumDelta]
        exact hlogBad
    let ownAzumaFailure : (Fin r → Fin k → Fin N) → Prop := fun W =>
      ∃ b : Fin r, FixedListOwnBlock E G ρ D (μ b) a ∧
        ∑ i : Fin k, ownDelta b i W <
          (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ)
    have hfailure_subset (W : Fin r → Fin k → Fin N) :
        fixedListFailure E G ρ D μ a W → stepFailure W ∨ ownAzumaFailure W := by
      intro hfail
      dsimp [fixedListFailure] at hfail
      rcases hfail with habs | hother
      · exact Or.inl (Or.inl (by simpa [absFailure, L] using habs))
      · rcases hother with hown | hexternal
        · exact hown_failure_subset W hown
        · exact Or.inl (hexternal_subset W hexternal)
    have hownTailBound :
        P.pr ownAzumaFailure ≤ (r : ℝ) * Real.exp (-(a ^ 2 * (k : ℝ)) / 32) := by
      calc
        P.pr ownAzumaFailure ≤
            ∑ b : Fin r, P.pr (fun W =>
              FixedListOwnBlock E G ρ D (μ b) a ∧
                ∑ i : Fin k, ownDelta b i W <
                  (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ)) :=
          FinProb.pr_iUnion_le P _
        _ ≤ ∑ b : Fin r, Real.exp (-(a ^ 2 * (k : ℝ)) / 32) := by
          apply Finset.sum_le_sum
          intro b hb
          by_cases hown : FixedListOwnBlock E G ρ D (μ b) a
          · calc
              P.pr (fun W => FixedListOwnBlock E G ρ D (μ b) a ∧
                  ∑ i : Fin k, ownDelta b i W <
                    (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ)) ≤
                  P.pr (fun W =>
                    ∑ i : Fin k, ownDelta b i W <
                      (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ)) :=
                FinProb.pr_mono P _ _ (fun W h => h.2)
              _ ≤ Real.exp (-(a ^ 2 * (k : ℝ)) / 32) := by
                simpa [P, Rows] using hownPr b hown
          · have hzero : P.pr (fun W =>
                FixedListOwnBlock E G ρ D (μ b) a ∧
                  ∑ i : Fin k, ownDelta b i W <
                    (-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ)) = 0 := by
              simp [FinProb.pr, hown]
            rw [hzero]
            positivity
        _ = (r : ℝ) * Real.exp (-(a ^ 2 * (k : ℝ)) / 32) := by simp
    let T : ℝ := a ^ 2 * (k : ℝ)
    have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
    have hlogExp : (r : ℝ) + 1 ≤ Real.exp (T / 100) := by
      have h := (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < (r : ℝ) + 1)).mp hlog
      simpa [T] using h
    have hrExp : (r : ℝ) ≤ Real.exp (T / 100) := by linarith [hlogExp]
    have hownTailCoarse :
        (r : ℝ) * Real.exp (-T / 32) ≤ Real.exp (-T / 50) := by
      calc
        (r : ℝ) * Real.exp (-T / 32) ≤
            Real.exp (T / 100) * Real.exp (-T / 32) :=
          mul_le_mul_of_nonneg_right hrExp (Real.exp_nonneg _)
        _ = Real.exp (T / 100 - T / 32) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-T / 50) := Real.exp_le_exp.mpr (by norm_num; nlinarith [hTnonneg])
    have hlog2 : Real.log 2 ≤ T / 100 := by
      have hr2 : (2 : ℝ) ≤ (r : ℝ) + 1 := by
        have hrN' : 2 ≤ r + 1 := by omega
        exact_mod_cast hrN'
      have hlog2' := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hr2
      have hlog' : Real.log ((r : ℝ) + 1) ≤ T / 100 := by
        change Real.log ((r : ℝ) + 1) ≤ (a ^ 2 * (k : ℝ)) / 100
        exact hlog
      exact hlog2'.trans hlog'
    have hzHalf : Real.exp (-T / 100) ≤ 1 / 2 := by
      calc
        Real.exp (-T / 100) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith [hlog2])
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
    have htwoExp : 2 * Real.exp (-T / 50) ≤ Real.exp (-T / 100) := by
      let z : ℝ := Real.exp (-T / 100)
      have hz0 : 0 ≤ z := Real.exp_nonneg _
      have hzle : z ≤ 1 / 2 := by simpa [z] using hzHalf
      have hexp : Real.exp (-T / 50) = z ^ 2 := by
        dsimp [z]
        rw [show -T / 50 = (-T / 100) + (-T / 100) by ring, Real.exp_add]
        ring
      rw [hexp]
      have hmul := mul_le_mul_of_nonneg_left hzle (by positivity : 0 ≤ 2 * z)
      calc
        2 * z ^ 2 = (2 * z) * z := by ring
        _ ≤ (2 * z) * (1 / 2) := hmul
        _ = z := by ring
    have hfailurePr :
        P.pr (fixedListFailure E G ρ D μ a) ≤ Real.exp (-T / 100) := by
      have hstep : P.pr stepFailure ≤ Real.exp (-T / 50) := by
        simpa [stepFailure, T] using hstepBad_bound
      calc
        P.pr (fixedListFailure E G ρ D μ a) ≤
            P.pr (fun W => stepFailure W ∨ ownAzumaFailure W) :=
          FinProb.pr_mono P _ _ hfailure_subset
        _ ≤ P.pr stepFailure + P.pr ownAzumaFailure :=
          FinProb.pr_union_le P stepFailure ownAzumaFailure
        _ ≤ Real.exp (-T / 50) +
            (r : ℝ) * Real.exp (-T / 32) := by
          exact add_le_add hstep (by simpa [T] using hownTailBound)
        _ ≤ 2 * Real.exp (-T / 50) := by
          have := hownTailCoarse
          nlinarith
        _ ≤ Real.exp (-T / 100) := htwoExp
    have hweight_eq :
        fixedListFailureWeight (N := N) (r := r) (k := k) (q := q) E G ρ D μ a =
          P.pr (fixedListFailure E G ρ D μ a) := by
      unfold fixedListFailureWeight FinProb.pr
      apply Finset.sum_congr rfl
      intro W hW
      simp [hPweight W]
    rw [hweight_eq]
    have hfinalExp : -T / 100 = -(1 / 100 : ℝ) * a ^ 2 * (k : ℝ) := by
      dsimp [T]
      ring
    rw [hfinalExp] at hfailurePr
    exact hfailurePr


end HypercubeRamsey.S14.Geometry_q_s14_geom
