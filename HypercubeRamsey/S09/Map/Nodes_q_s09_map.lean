import HypercubeRamsey.S09.Map.Device
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S05.Clock_q_s05_even
import Mathlib.Data.Nat.Choose.Bounds

/-!
Private support for lane `q-s09-map`.  This file contains translations from the
slice-indexed Section 9 experiment to the generic Section 3 height estimates.
-/

namespace HypercubeRamsey.Lane_q_s09_map

open OAI.HypercubeRamsey Classical
open Filter
open scoped BigOperators symmDiff

set_option maxHeartbeats 600000

variable {P : Params9} {hc : HeightChoice9 P} {n : ℕ}

private abbrev HeightLoc9 := CubeVertex (n - P.m n) × Fin (hc.levels n + 1)

private noncomputable def heightParams9 : HDParams where
  n := n
  d := n - P.m n
  D := 2
  r := P.radius n
  H := hc.levels n
  lam := (n : ℝ) ^ (10 : ℝ)
  b₀ := hc.b₀ - 10
  b := hc.eps'

private noncomputable def sliceIndices (s : CubeVertex (P.m n)) : Finset (Pos9 P hc n) :=
  Finset.univ.filter (fun c => c.slice = s)

private noncomputable def sliceIndexEquiv (s : CubeVertex (P.m n)) :
    {c : Pos9 P hc n // c ∈ sliceIndices (P := P) (hc := hc) (n := n) s} ≃ HeightLoc9 (P := P) (hc := hc) (n := n) where
  toFun c := (c.1.location, c.1.level)
  invFun x := ⟨⟨s, x.1, x.2⟩, by simp [sliceIndices]⟩
  left_inv := by
    intro ⟨⟨sl, loc, lev⟩, hc⟩
    apply Subtype.ext
    have hsl : sl = s := by simpa [sliceIndices] using hc
    subst sl
    rfl
  right_inv := by
    intro x
    rfl

private noncomputable def sliceReadout (s : CubeVertex (P.m n))
    (Pp : Pos9 P hc n → Bool) : HeightLoc9 (P := P) (hc := hc) (n := n) → Bool :=
  fun x => Pp ((sliceIndexEquiv (P := P) (hc := hc) (n := n) s).symm x).1

private theorem eligCount_slice_eq (Pp : Pos9 P hc n → Bool)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    eligCount9 Finset.univ Pp v j =
      (Finset.univ.filter (fun u : CubeVertex (n - P.m n) =>
        sliceReadout (P := P) (hc := hc) (n := n) (specialWord9 (P.m n) v) Pp (u, j) = true ∧
          _root_.hammingDist u (residualWord9 (P.m n) v) ≤ P.radius n)).card := by
  classical
  let s := specialWord9 (P.m n) v
  let A : Finset (Pos9 P hc n) := Finset.univ.filter (fun c =>
    Pp c = true ∧ c.slice = s ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n ∧ c.level = j)
  let B : Finset (CubeVertex (n - P.m n)) := Finset.univ.filter (fun u =>
    sliceReadout (P := P) (hc := hc) (n := n) s Pp (u, j) = true ∧
      _root_.hammingDist u (residualWord9 (P.m n) v) ≤ P.radius n)
  have hcard : A.card = B.card := by
    apply Finset.card_bij (fun c _ => c.location)
    · intro c hcA
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hcA
      rcases hcA with ⟨hp, hs, hd, hj⟩
      have hrepr : c = ⟨s, c.location, j⟩ := by
        cases c
        simp_all
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      constructor
      · change Pp ((sliceIndexEquiv (P := P) (hc := hc) (n := n) s).symm (c.location, j)).1 = true
        rw [show ((sliceIndexEquiv (P := P) (hc := hc) (n := n) s).symm (c.location, j)).1 = c by
          change (⟨s, c.location, j⟩ : Pos9 P hc n) = c
          exact hrepr.symm]
        exact hp
      · exact hd
    · intro c hcA d hdA heq
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hcA hdA
      rcases hcA with ⟨_, hcs, _, hcj⟩
      rcases hdA with ⟨_, hds, _, hdj⟩
      cases c with
      | mk sc lc jc =>
        cases d with
        | mk sd ld jd =>
          simp_all
    · intro u huB
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at huB
      rcases huB with ⟨hread, hd⟩
      refine ⟨⟨s, u, j⟩, ?_, rfl⟩
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · change Pp ((sliceIndexEquiv (P := P) (hc := hc) (n := n) s).symm (u, j)).1 = true at hread
        exact hread
      · exact And.intro hd True.intro
  rw [show eligCount9 Finset.univ Pp v j = A.card by
    simp [eligCount9, A, s]]
  exact hcard

private theorem map_comp {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (P : FinProb α) (f : α → β) (g : β → γ) :
    FinProb.map (FinProb.map P f) g = FinProb.map P (g ∘ f) := by
  classical
  apply FinProb.ext
  intro c
  calc
    (FinProb.map (FinProb.map P f) g).w c =
        (FinProb.map (FinProb.map P f) g).pr (fun z => z = c) :=
      (FinProb.pr_singleton _ _).symm
    _ = (FinProb.map P f).pr (fun b => g b = c) := FinProb.map_pr _ _ _
    _ = P.pr (fun a => g (f a) = c) := FinProb.map_pr _ _ _
    _ = (FinProb.map P (g ∘ f)).pr (fun z => z = c) := by
      simpa only [Function.comp_apply] using
        (FinProb.map_pr P (g ∘ f) (fun z => z = c)).symm
    _ = (FinProb.map P (g ∘ f)).w c := FinProb.pr_singleton _ _

private lemma finProb_pr_mono {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : μ.pr A ≤ μ.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, μ.nonneg]

private lemma finProb_pr_exists_le_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (μ : FinProb Ω) (A : ι → Ω → Prop) :
    μ.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, μ.pr (A i) := by
  classical
  unfold FinProb.pr
  calc
    _ ≤ ∑ ω, ∑ i, if A i ω then μ.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hex : ∃ i, A i ω
      · obtain ⟨i, hi⟩ := hex
        have hsingle :
            (if A i ω then μ.w ω else 0) ≤ ∑ k : ι, if A k ω then μ.w ω else 0 :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun k : ι => if A k ω then μ.w ω else 0)
            (fun k hk => by
              by_cases hkA : A k ω
              · simp [hkA, μ.nonneg]
              · simp [hkA]) (Finset.mem_univ i)
        have hbound : μ.w ω ≤ ∑ k : ι, if A k ω then μ.w ω else 0 := by
          calc
            μ.w ω = (if A i ω then μ.w ω else 0) := by simp [hi]
            _ ≤ ∑ k : ι, if A k ω then μ.w ω else 0 := hsingle
        have hex' : ∃ k, A k ω := ⟨i, hi⟩
        simpa [hex'] using hbound
      · have hfalse : ∀ i, ¬ A i ω := by
          intro i hAi
          exact hex ⟨i, hAi⟩
        have hsum : (∑ i : ι, if A i ω then μ.w ω else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp [hfalse i]
        simp [hex, hsum]
    _ = ∑ i, ∑ ω, if A i ω then μ.w ω else 0 := by rw [Finset.sum_comm]

private theorem pi_reindex_const {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (μ : FinProb Bool) :
    FinProb.map (FinProb.pi (fun _ : α => μ)) (fun x b => x (e.symm b)) =
      FinProb.pi (fun _ : β => μ) := by
  classical
  apply FinProb.ext
  intro y
  simp only [FinProb.map, FinProb.pi]
  rw [Fintype.sum_eq_single (fun a => y (e a))]
  · have hfun : (fun b => (fun a => y (e a)) (e.symm b)) = y := by
      funext b
      simp
    rw [if_pos hfun]
    exact Fintype.prod_equiv e (fun a => μ.w (y (e a))) (fun b => μ.w (y b)) (by
      intro a
      rfl)
  · intro x hx
    split_ifs with h
    · have hxy : x = fun a => y (e a) := by
        funext a
        have := congrFun h (e a)
        simpa only [Equiv.symm_apply_apply] using this
      exact (hx hxy).elim
    · rfl

set_option maxHeartbeats 10000000 in
private theorem heightPos_sliceLaw (s : CubeVertex (P.m n)) :
    FinProb.map (heightPosLaw9 P hc n)
        (fun Pp (x : HeightLoc9 (P := P) (hc := hc) (n := n)) =>
          Pp ((sliceIndexEquiv (P := P) (hc := hc) (n := n) s).symm x).1) =
      (heightParams9 (P := P) (hc := hc) (n := n)).posLaw := by
  classical
  let q : ℝ := (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)
  let proj : (Pos9 P hc n → Bool) →
      ({c : Pos9 P hc n // c ∈ sliceIndices (P := P) (hc := hc) (n := n) s} → Bool) :=
    fun Pp c => Pp c.1
  let reidx :
      ({c : Pos9 P hc n // c ∈ sliceIndices (P := P) (hc := hc) (n := n) s} → Bool) →
        HeightLoc9 (P := P) (hc := hc) (n := n) → Bool :=
    fun f x => f ((sliceIndexEquiv (P := P) (hc := hc) (n := n) s).symm x)
  have hmarg : FinProb.map (heightPosLaw9 P hc n) proj =
      FinProb.pi (fun _ : {c : Pos9 P hc n //
          c ∈ sliceIndices (P := P) (hc := hc) (n := n) s} => FinProb.bernoulli q) := by
    apply FinProb.ext
    intro f
    change (FinProb.map (FinProb.pi (fun _ : Pos9 P hc n => FinProb.bernoulli q)) proj).w f = _
    exact FinProb.pi_marginal (fun _ : Pos9 P hc n => FinProb.bernoulli q)
      (sliceIndices (P := P) (hc := hc) (n := n) s) f
  have hprod : FinProb.map (FinProb.pi
      (fun _ : {c : Pos9 P hc n //
        c ∈ sliceIndices (P := P) (hc := hc) (n := n) s} => FinProb.bernoulli q)) reidx =
      FinProb.pi (fun _ : HeightLoc9 (P := P) (hc := hc) (n := n) => FinProb.bernoulli q) :=
    pi_reindex_const (sliceIndexEquiv (P := P) (hc := hc) (n := n) s) (FinProb.bernoulli q)
  have hcomp := map_comp (heightPosLaw9 P hc n) proj reidx
  change FinProb.map (heightPosLaw9 P hc n) (reidx ∘ proj) =
    FinProb.pi (fun _ : HeightLoc9 (P := P) (hc := hc) (n := n) => FinProb.bernoulli q)
  calc
    FinProb.map (heightPosLaw9 P hc n) (reidx ∘ proj) =
        FinProb.map (FinProb.map (heightPosLaw9 P hc n) proj) reidx := hcomp.symm
    _ = FinProb.map (FinProb.pi
        (fun _ : {c : Pos9 P hc n //
          c ∈ sliceIndices (P := P) (hc := hc) (n := n) s} => FinProb.bernoulli q)) reidx := by rw [hmarg]
    _ = FinProb.pi (fun _ : HeightLoc9 (P := P) (hc := hc) (n := n) => FinProb.bernoulli q) := hprod

private noncomputable def slicePositionCount
    (f : HeightLoc9 (P := P) (hc := hc) (n := n) → Bool)
    (x : CubeVertex (n - P.m n)) (j : Fin (hc.levels n + 1)) : ℕ :=
  (Finset.univ.filter (fun u : CubeVertex (n - P.m n) =>
    f (u, j) = true ∧ _root_.hammingDist u x ≤ P.radius n)).card

private noncomputable def slicePositionLow
    (f : HeightLoc9 (P := P) (hc := hc) (n := n) → Bool) : Prop :=
  ∃ x : CubeVertex (n - P.m n), ∃ j : Fin (hc.levels n + 1),
    ((slicePositionCount (P := P) (hc := hc) (n := n) f x j : ℕ) : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2

private noncomputable def slicePositionBad
    (f : HeightLoc9 (P := P) (hc := hc) (n := n) → Bool) : Prop :=
  ∃ x : CubeVertex (n - P.m n), ∃ j : Fin (hc.levels n + 1),
    let count := slicePositionCount (P := P) (hc := hc) (n := n) f x j
    ((count : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2 ∨ 2 * (n : ℝ) ^ (10 : ℝ) < (count : ℝ))

private theorem slice_position_bad_bound (s : CubeVertex (P.m n))
    (hlam : 0 < ((heightParams9 (P := P) (hc := hc) (n := n)).lam))
    (hV : 0 < (heightParams9 (P := P) (hc := hc) (n := n)).V)
    (hr : (heightParams9 (P := P) (hc := hc) (n := n)).r ≤
      (heightParams9 (P := P) (hc := hc) (n := n)).d)
    (hprob : (heightParams9 (P := P) (hc := hc) (n := n)).lam /
      ((heightParams9 (P := P) (hc := hc) (n := n)).V : ℝ) ≤ 1) :
    (heightPosLaw9 P hc n).pr (fun Pp =>
      slicePositionLow (P := P) (hc := hc) (n := n)
        (sliceReadout (P := P) (hc := hc) (n := n) s Pp)) ≤
      2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
        ((hc.levels n + 1 : ℕ) : ℝ) *
        Real.exp (-((n : ℝ) ^ (10 : ℝ)) / 12) := by
  classical
  let p := heightParams9 (P := P) (hc := hc) (n := n)
  let G : (p.Loc → Bool) → Prop := fun f =>
    ∃ x : CubeVertex p.d, x ∈ (Finset.univ : Finset (CubeVertex p.d)) ∧
      ∃ j : Fin (p.H + 1),
        let count := (Finset.univ.filter (fun u : CubeVertex p.d =>
          f (u, j) = true ∧ _root_.hammingDist u x ≤ p.r)).card
        ((count : ℝ) < p.lam / 2 ∨ 2 * p.lam < (count : ℝ))
  have hgen := height_position_counts p Finset.univ hlam hV hr hprob
  have hgen' : p.posLaw.pr G ≤
      2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
        ((hc.levels n + 1 : ℕ) : ℝ) * Real.exp (-((n : ℝ) ^ (10 : ℝ)) / 12) := by
    change p.posLaw.pr (fun f => ∃ x ∈ (Finset.univ : Finset (CubeVertex p.d)),
      ∃ j : Fin (p.H + 1),
        let count := (Finset.univ.filter (fun u : CubeVertex p.d =>
          f (u, j) = true ∧ _root_.hammingDist u x ≤ p.r)).card
        ((count : ℝ) < p.lam / 2 ∨ 2 * p.lam < (count : ℝ)) ) ≤ _
    exact hgen
  have hbadMono : p.posLaw.pr (slicePositionBad (P := P) (hc := hc) (n := n)) ≤
      p.posLaw.pr G := by
    apply finProb_pr_mono
    intro f hbad
    obtain ⟨x, j, hj⟩ := hbad
    refine ⟨x, Finset.mem_univ _, j, ?_⟩
    rcases hj with hlow | hhigh
    · exact Or.inl hlow
    · exact Or.inr hhigh
  have hbadBound := hbadMono.trans hgen'
  have hlow : p.posLaw.pr (slicePositionLow (P := P) (hc := hc) (n := n)) ≤
      p.posLaw.pr (slicePositionBad (P := P) (hc := hc) (n := n)) := by
    apply finProb_pr_mono
    intro f h
    obtain ⟨x, j, hj⟩ := h
    exact ⟨x, j, Or.inl hj⟩
  let R := sliceReadout (P := P) (hc := hc) (n := n) s
  have hprobEq : (heightPosLaw9 P hc n).pr (fun Pp =>
      slicePositionLow (P := P) (hc := hc) (n := n) (R Pp)) =
        p.posLaw.pr (slicePositionLow (P := P) (hc := hc) (n := n)) := by
    calc
      _ = (FinProb.map (heightPosLaw9 P hc n) R).pr
          (slicePositionLow (P := P) (hc := hc) (n := n)) :=
        (FinProb.map_pr _ _ _).symm
      _ = p.posLaw.pr (slicePositionLow (P := P) (hc := hc) (n := n)) := by
        have hlaw := congrArg
          (fun law : FinProb (HeightLoc9 (P := P) (hc := hc) (n := n) → Bool) =>
            law.pr (slicePositionLow (P := P) (hc := hc) (n := n)))
          (heightPos_sliceLaw (P := P) (hc := hc) (n := n) s)
        change (FinProb.map (heightPosLaw9 P hc n)
            (fun Pp x => Pp ((sliceIndexEquiv (P := P) (hc := hc) (n := n) s).symm x).1)).pr
            (slicePositionLow (P := P) (hc := hc) (n := n)) =
          (heightParams9 (P := P) (hc := hc) (n := n)).posLaw.pr
            (slicePositionLow (P := P) (hc := hc) (n := n))
        exact hlaw
  calc
    _ = p.posLaw.pr (slicePositionLow (P := P) (hc := hc) (n := n)) := hprobEq
    _ ≤ p.posLaw.pr (slicePositionBad (P := P) (hc := hc) (n := n)) := hlow
    _ ≤ _ := by simpa [p, heightParams9] using hbadBound

private theorem height_counts_one_dim
    (hlam : 0 < ((heightParams9 (P := P) (hc := hc) (n := n)).lam))
    (hV : 0 < (heightParams9 (P := P) (hc := hc) (n := n)).V)
    (hr : (heightParams9 (P := P) (hc := hc) (n := n)).r ≤
      (heightParams9 (P := P) (hc := hc) (n := n)).d)
    (hprob : (heightParams9 (P := P) (hc := hc) (n := n)).lam /
      ((heightParams9 (P := P) (hc := hc) (n := n)).V : ℝ) ≤ 1)
    (htail : (2 : ℝ) ^ n *
        (2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
          ((hc.levels n + 1 : ℕ) : ℝ) *
          Real.exp (-((n : ℝ) ^ (10 : ℝ)) / 12)) ≤ Real.exp (-(n : ℝ))) :
    HeightCounts9 P hc n := by
  classical
  let μ := heightPosLaw9 P hc n
  let B : ℝ := 2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
    ((hc.levels n + 1 : ℕ) : ℝ) * Real.exp (-((n : ℝ) ^ (10 : ℝ)) / 12)
  have hsite (v : CubeVertex n) :
      μ.pr (fun Pp => ∃ j : Fin (hc.levels n + 1),
        (eligCount9 Finset.univ Pp v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2) ≤ B := by
    calc
      μ.pr (fun Pp => ∃ j : Fin (hc.levels n + 1),
          (eligCount9 Finset.univ Pp v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2) ≤
          μ.pr (fun Pp => slicePositionLow (P := P) (hc := hc) (n := n)
            (sliceReadout (P := P) (hc := hc) (n := n) (specialWord9 (P.m n) v) Pp) ) := by
        apply finProb_pr_mono μ
        intro Pp hbad
        obtain ⟨j, hj⟩ := hbad
        refine ⟨residualWord9 (P.m n) v, j, ?_⟩
        have heq := eligCount_slice_eq (P := P) (hc := hc) (n := n) Pp v j
        rw [heq] at hj
        simpa only [slicePositionCount] using hj
      _ ≤ B := slice_position_bad_bound (P := P) (hc := hc) (n := n)
        (specialWord9 (P.m n) v) hlam hV hr hprob
  have hunion := finProb_pr_exists_le_sum μ (fun v Pp =>
    ∃ j : Fin (hc.levels n + 1),
      (eligCount9 Finset.univ Pp v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2)
  have hsum : (∑ v : CubeVertex n, μ.pr (fun Pp => ∃ j : Fin (hc.levels n + 1),
      (eligCount9 Finset.univ Pp v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2)) ≤
      (2 : ℝ) ^ n * B := by
    calc
      _ ≤ ∑ _v : CubeVertex n, B := by
        apply Finset.sum_le_sum
        intro v hv
        exact hsite v
      _ = (2 : ℝ) ^ n * B := by simp [B, CubeVertex]
  unfold HeightCounts9
  calc
    μ.pr (fun Pp => ∃ v : CubeVertex n, ∃ j : Fin (hc.levels n + 1),
      (eligCount9 Finset.univ Pp v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2) ≤
        ∑ v : CubeVertex n, μ.pr (fun Pp => ∃ j : Fin (hc.levels n + 1),
          (eligCount9 Finset.univ Pp v j : ℝ) < (n : ℝ) ^ (10 : ℝ) / 2) := by
      simpa using hunion
    _ ≤ (2 : ℝ) ^ n * B := hsum
    _ ≤ Real.exp (-(n : ℝ)) := by simpa [B] using htail

theorem height_counts9_of_bounds (P : Params9) (hc : HeightChoice9 P) (n : ℕ)
    (hlam : 0 < (n : ℝ) ^ (10 : ℝ))
    (hV : 0 < residualBall9 P n)
    (hr : P.radius n ≤ n - P.m n)
    (hprob : (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ) ≤ 1)
    (htail : (2 : ℝ) ^ n *
        (2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
          ((hc.levels n + 1 : ℕ) : ℝ) *
          Real.exp (-((n : ℝ) ^ (10 : ℝ)) / 12)) ≤ Real.exp (-(n : ℝ))) :
    HeightCounts9 P hc n := by
  apply height_counts_one_dim (P := P) (hc := hc) (n := n)
  · simpa [heightParams9, Real.rpow_natCast] using hlam
  · simpa [heightParams9, HDParams.V, residualBall9] using hV
  · simpa [heightParams9] using hr
  · simpa [heightParams9, HDParams.V, residualBall9, Real.rpow_natCast] using hprob
  · simpa only [heightParams9, Real.rpow_natCast] using htail

private theorem eventually_nat_rpow_le_quarter {a : ℝ} (ha : a < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (n : ℝ) ^ a ≤ (n : ℝ) / 4 := by
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - 1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, neg_sub] using h
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  refine ⟨max 2 n₀, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 n₀) hn
  have hn₀' : n₀ ≤ n := le_trans (le_max_right 2 n₀) hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : (n : ℝ) ^ (a - 1) < 1 / 4 := hn₀ n hn₀'
  have hmul := mul_lt_mul_of_pos_right hsmall hnreal
  have hpow : (n : ℝ) ^ (a - 1) * (n : ℝ) = (n : ℝ) ^ a := by
    calc
      (n : ℝ) ^ (a - 1) * (n : ℝ) =
          (n : ℝ) ^ (a - 1) * (n : ℝ) ^ 1 := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((a - 1) + 1) := (Real.rpow_add hnreal _ _).symm
      _ = (n : ℝ) ^ a := by congr 1 <;> ring
  rw [hpow] at hmul
  nlinarith

private theorem eventually_floor_rpow_ge_eleven {a : ℝ} (ha : 0 < a) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, 11 ≤ ⌊(n : ℝ) ^ a⌋₊ := by
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hT 11)
  refine ⟨max 1 n₀, ?_⟩
  intro n hn
  have hn₀' : n₀ ≤ n := le_trans (le_max_right 1 n₀) hn
  have hlarge : (11 : ℝ) ≤ (n : ℝ) ^ a := hn₀ n hn₀'
  exact Nat.le_floor hlarge

private theorem params9_small_internal_scales (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (P.m n : ℝ) ≤ (n : ℝ) / 4 ∧
      (P.radius n : ℝ) ≤ (n : ℝ) / 4 ∧ 11 ≤ P.radius n := by
  rcases hP with ⟨hcommon, hminus, hx, hσ, hχ, hgap, hcaseValid⟩
  rcases hσ with ⟨hσpos, hσsmall⟩
  have hσposR : 0 < (P.σ : ℝ) := by exact_mod_cast hσpos
  have hσlt1q : P.σ < 1 := by
    have hxS : P.xS < 1 := lt_trans hcommon.2.1 (lt_trans hcommon.2.2 (by norm_num))
    linarith
  have hσlt1 : (P.σ : ℝ) < 1 := by exact_mod_cast hσlt1q
  obtain ⟨nσhi, hσhi⟩ := eventually_nat_rpow_le_quarter hσlt1
  obtain ⟨nσlo, hσlo⟩ := eventually_floor_rpow_ge_eleven hσposR
  have hm : ∃ nₘ : ℕ, ∀ n ≥ nₘ, (P.m n : ℝ) ≤ (n : ℝ) / 4 := by
    cases hbranch : P.case with
    | sub yS yD yM =>
        have hv : 0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧
            1 - P.σ < yD ∧ yD < 1 ∧ P.χ < P.σ / 10 := by
          simpa [hbranch] using hcaseValid
        have hyMq : yM < 1 := by linarith [hv.2.2.1, hσpos]
        have hyM : (yM : ℝ) < 1 := by exact_mod_cast hyMq
        obtain ⟨nₘ, hsmall⟩ := eventually_nat_rpow_le_quarter hyM
        refine ⟨max 2 nₘ, ?_⟩
        intro n hn
        have hnₘ : nₘ ≤ n := le_trans (le_max_right 2 nₘ) hn
        have hfloor : (P.m n : ℝ) ≤ (n : ℝ) ^ (yM : ℝ) := by
          rw [Params9.m, hbranch]
          exact Nat.floor_le (show 0 ≤ (n : ℝ) ^ (yM : ℝ) by positivity)
        exact hfloor.trans (hsmall n hnₘ)
    | lin αS αD hB yB =>
        have hv : 0 < 100 * αS ∧ 100 * αS < αD ∧ αD < 1 / 100 ∧
            P.σ < P.χ / 10 ∧ P.hPlus < hB ∧ hB < 1 ∧ 0 < yB ∧ yB < 1 := by
          simpa [hbranch] using hcaseValid
        have h100pos : 0 < (100 : ℚ) * αS := hv.1
        have hαDposq : 0 < αD := lt_trans h100pos hv.2.1
        have hαDpos : (0 : ℝ) < (αD : ℝ) := by exact_mod_cast hαDposq
        have hαDq : αD < (1 : ℚ) / 100 := hv.2.2.1
        have hαD : (αD : ℝ) < (1 : ℝ) / 100 := by
          have hcast : (αD : ℝ) < (((1 : ℚ) / 100 : ℚ) : ℝ) :=
            Rat.cast_lt.mpr hαDq
          simpa using hcast
        refine ⟨2, ?_⟩
        intro n hn
        have hnreal : 0 ≤ (n : ℝ) := by positivity
        have hlin : (P.m n : ℝ) ≤ (αD : ℝ) * (n : ℝ) / 10 := by
          rw [Params9.m, hbranch]
          exact Nat.floor_le (show 0 ≤ (αD : ℝ) * (n : ℝ) / 10 by positivity)
        have hnquarter : (αD : ℝ) * (n : ℝ) / 10 ≤ (n : ℝ) / 4 := by
          nlinarith
        exact hlin.trans hnquarter
  obtain ⟨nₘ, hm⟩ := hm
  refine ⟨max 2 (max nσhi (max nσlo nₘ)), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 _) hn
  have houter : max nσhi (max nσlo nₘ) ≤ n := le_trans (le_max_right 2 _) hn
  have hrest : max nσlo nₘ ≤ n := le_trans (le_max_right nσhi _) houter
  have hnσhi : nσhi ≤ n := le_trans (le_max_left nσhi _) houter
  have hnσlo : nσlo ≤ n := le_trans (le_max_left nσlo nₘ) hrest
  have hnₘ : nₘ ≤ n := le_trans (le_max_right nσlo nₘ) hrest
  have hm' := hm n hnₘ
  have hσhi' := hσhi n hnσhi
  have hσlo' := hσlo n hnσlo
  have hradius : (P.radius n : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) := by
    exact Nat.floor_le (by positivity)
  exact ⟨hm', hradius.trans hσhi', hσlo'⟩

theorem height_base_small_scales9 (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (P.m n : ℝ) ≤ (n : ℝ) / 4 ∧
      (P.radius n : ℝ) ≤ (n : ℝ) / 4 ∧ 11 ≤ P.radius n :=
  params9_small_internal_scales P hP

theorem height_counts9_volume_bounds (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      0 < residualBall9 P n ∧ P.radius n ≤ n - P.m n ∧
      (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ) ≤ 1 := by
  obtain ⟨nGeom, hGeom⟩ := params9_small_internal_scales P hP
  let C : ℕ := 2 ^ 11 * Nat.factorial 11
  refine ⟨max nGeom C, ?_⟩
  intro n hn
  have hnGeom : nGeom ≤ n := le_trans (le_max_left nGeom C) hn
  have hnC : C ≤ n := le_trans (le_max_right nGeom C) hn
  have hsmall := hGeom n hnGeom
  have hn100 : 100 ≤ n := by
    have hC : 100 ≤ C := by norm_num [C]
    omega
  have hmreal : (P.m n : ℝ) ≤ (n : ℝ) / 4 := hsmall.1
  have hrreal : (P.radius n : ℝ) ≤ (n : ℝ) / 4 := hsmall.2.1
  have hmnreal : (P.m n : ℝ) ≤ (n : ℝ) := by linarith
  have hmn : P.m n ≤ n := by exact_mod_cast hmnreal
  have hdcast : ((n - P.m n : ℕ) : ℝ) = (n : ℝ) - (P.m n : ℝ) := by
    exact Nat.cast_sub hmn
  let d : ℕ := n - P.m n
  have hdthree : 3 * (n : ℝ) / 4 ≤ (d : ℝ) := by
    dsimp [d]
    rw [hdcast]
    nlinarith
  have hdlarge : 75 ≤ d := by
    have hn100R : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn100
    have hreal : (75 : ℝ) ≤ (d : ℝ) := by nlinarith
    exact_mod_cast hreal
  have hradiusDreal : (P.radius n : ℝ) ≤ (d : ℝ) := by
    have hdc : (d : ℝ) = (n : ℝ) - (P.m n : ℝ) := by
      dsimp [d]
      exact hdcast
    rw [hdc]
    nlinarith
  have hradiusD : P.radius n ≤ d := by exact_mod_cast hradiusDreal
  have hchoose :
      ((d + 1 - 11 : ℕ) : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) ≤
        (Nat.choose d 11 : ℝ) := by
    exact Nat.pow_le_choose 11 d
  have hsubcast : ((d + 1 - 11 : ℕ) : ℝ) = (d : ℝ) + 1 - 11 := by
    rw [Nat.cast_sub (by omega : 11 ≤ d + 1)]
    norm_num
  have hn100R : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn100
  have hshift : (n : ℝ) / 2 ≤ ((d + 1 - 11 : ℕ) : ℝ) := by
    rw [hsubcast]
    nlinarith [hdthree, hn100R]
  have hpow : ((n : ℝ) / 2) ^ 11 ≤ ((d + 1 - 11 : ℕ) : ℝ) ^ 11 := by
    gcongr
  have hchooseLower :
      (n : ℝ) ^ 11 / ((2 : ℝ) ^ 11 * (Nat.factorial 11 : ℝ)) ≤
        (Nat.choose d 11 : ℝ) := by
    have heq : (n : ℝ) ^ 11 / ((2 : ℝ) ^ 11 * (Nat.factorial 11 : ℝ)) =
        ((n : ℝ) / 2) ^ 11 / (Nat.factorial 11 : ℝ) := by
      field_simp
      <;> ring
    rw [heq]
    exact (div_le_div_of_nonneg_right hpow (by positivity)).trans hchoose
  have hball : Nat.choose d 11 ≤ residualBall9 P n := by
    unfold residualBall9
    apply Finset.single_le_sum
    · intro i hi
      exact Nat.zero_le _
    · exact Finset.mem_range.mpr (by have := hsmall.2.2; dsimp [Params9.radius] at this; omega)
  have hballReal : (Nat.choose d 11 : ℝ) ≤ (residualBall9 P n : ℝ) := by exact_mod_cast hball
  have hCcast : (C : ℝ) = (2 : ℝ) ^ 11 * (Nat.factorial 11 : ℝ) := by norm_num [C]
  have hCpos : 0 < (C : ℝ) := by positivity
  have hnCReal : (C : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnC
  have hratio : (n : ℝ) ^ 10 ≤
      (n : ℝ) ^ 11 / ((2 : ℝ) ^ 11 * (Nat.factorial 11 : ℝ)) := by
    rw [← hCcast]
    apply (le_div_iff₀ hCpos).2
    have hmul := mul_le_mul_of_nonneg_left hnCReal (by positivity : 0 ≤ (n : ℝ) ^ 10)
    rw [pow_succ]
    nlinarith [hmul]
  have hvolumeNat : (n : ℝ) ^ (10 : ℕ) ≤ (residualBall9 P n : ℝ) :=
    hratio.trans hchooseLower |>.trans hballReal
  have hvolumeCast : (n : ℝ) ^ ((10 : ℕ) : ℝ) ≤ (residualBall9 P n : ℝ) := by
    rw [Real.rpow_natCast]
    exact hvolumeNat
  have hvolume : (n : ℝ) ^ (10 : ℝ) ≤ (residualBall9 P n : ℝ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num]
    exact hvolumeCast
  have hVposNat : 0 < residualBall9 P n := by
    have hnpositive : 0 < (n : ℝ) ^ (10 : ℝ) := by positivity
    have : 0 < (residualBall9 P n : ℝ) := lt_of_lt_of_le hnpositive hvolume
    exact_mod_cast this
  have hVpos : (0 : ℝ) < (residualBall9 P n : ℝ) := by exact_mod_cast hVposNat
  have hprob : (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ) ≤ 1 := by
    rw [div_le_one₀ hVpos]
    exact hvolume
  exact ⟨hVposNat, hradiusD, hprob⟩

theorem height_counts9_special_le_n (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, P.m n ≤ n := by
  obtain ⟨n₀, hscale⟩ := params9_small_internal_scales P hP
  refine ⟨n₀, ?_⟩
  intro n hn
  have hm := (hscale n hn).1
  have hm' : (P.m n : ℝ) ≤ (n : ℝ) := by nlinarith
  exact_mod_cast hm'

theorem height_counts9_budget_slack (P : Params9) (hc : HeightChoice9 P)
    (hadm : hc.Admissible) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      3 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') ≤ P.idBudget n := by
  rcases hadm with ⟨hσhpos, hσhζ, hζlt, hθpos, hθlt, ha, hab, hχa, hbpos, hbε, hε, hcase⟩
  let gap : ℝ := P.eps - hc.eps'
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ gap) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hT 3)
  refine ⟨max 2 n₀, ?_⟩
  intro n hn
  have hn₀' : n₀ ≤ n := le_trans (le_max_right 2 n₀) hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlarge : 3 ≤ (n : ℝ) ^ gap := hn₀ n hn₀'
  let a : ℝ := 1 - (P.σ : ℝ) + hc.eps'
  calc
    3 * (n : ℝ) ^ a ≤ (n : ℝ) ^ gap * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hnreal.le _)
    _ = (n : ℝ) ^ a * (n : ℝ) ^ gap := by ring
    _ = (n : ℝ) ^ (a + gap) := (Real.rpow_add hnreal a gap).symm
    _ = (n : ℝ) ^ (1 - (P.σ : ℝ) + P.eps) := by
      congr 1
      dsimp [a, gap]
      ring
    _ = P.idBudget n := by simp [Params9.idBudget]

theorem height_counts9_core_slack (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      6 * (n : ℝ) ^ ((P.χ : ℝ) / 2) ≤ (n : ℝ) ^ (P.χ : ℝ) := by
  rcases hP with ⟨_, _, _, _, ⟨hχpos, _⟩, _, _⟩
  have hχposR : 0 < (P.χ : ℝ) := by exact_mod_cast hχpos
  have hexp : 0 < (P.χ : ℝ) / 2 := by positivity
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ ((P.χ : ℝ) / 2)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hT 6)
  refine ⟨max 2 n₀, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 n₀) hn
  have hn₀' : n₀ ≤ n := le_trans (le_max_right 2 n₀) hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlarge : 6 ≤ (n : ℝ) ^ ((P.χ : ℝ) / 2) := hn₀ n hn₀'
  have hpow : (n : ℝ) ^ (P.χ : ℝ) =
      (n : ℝ) ^ ((P.χ : ℝ) / 2) * (n : ℝ) ^ ((P.χ : ℝ) / 2) := by
    rw [← Real.rpow_add hnreal]
    congr 1
    ring
  calc
    6 * (n : ℝ) ^ ((P.χ : ℝ) / 2) ≤
        (n : ℝ) ^ ((P.χ : ℝ) / 2) * (n : ℝ) ^ ((P.χ : ℝ) / 2) := by nlinarith [hlarge]
    _ = (n : ℝ) ^ (P.χ : ℝ) := hpow.symm

private theorem topScale_coarse_bound (n : ℕ) (σ ζ : ℝ) (hn : 5 ≤ n)
    (hσ : σ < 1) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    topScale n σ ζ ≤ 2 ^ (n ^ 2 + 2 * n) := by
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hn2 : 2 ≤ n := by omega
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpositive : 0 < (n : ℝ) := by positivity
  have hσpow : (n : ℝ) ^ σ ≤ (n : ℝ) := by
    calc
      (n : ℝ) ^ σ ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnreal (le_of_lt hσ)
      _ = (n : ℝ) := by rw [Real.rpow_one]
  have hMceil : ⌈(n : ℝ) ^ σ⌉₊ ≤ n := Nat.ceil_le.2 hσpow
  have hMle : M ≤ n := by
    dsimp [M]
    exact max_le hn2 hMceil
  have hMupper : M ≤ 2 ^ n := hMle.trans (Nat.le_of_lt n.lt_two_pow_self)
  have hMlower : 2 ≤ M := le_max_left _ _
  have hζpow : (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) := by
    calc
      (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hnreal
        linarith
      _ = (n : ℝ) := by rw [Real.rpow_one]
  have htarget : target ≤ n := by
    dsimp [target]
    exact Nat.ceil_le.2 hζpow
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) := by
    simpa using Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hlogSq : Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    calc
      Real.log (n : ℝ) ^ 2 = Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
      _ ≤ (n : ℝ) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hlog hlog0
      _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hlog hn0
      _ = (n : ℝ) ^ 2 := by ring
  have hlogSqCast : Real.log (n : ℝ) ^ 2 ≤ ((n ^ 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow] using hlogSq
  have hRceil : ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ n ^ 2 := Nat.ceil_le.2 hlogSqCast
  have hR0n : R₀ ≤ n ^ 2 := by
    dsimp [R₀]
    have hnsqpos : 0 < n ^ 2 := by positivity
    have hnsqone : 1 ≤ n ^ 2 := by omega
    exact max_le hnsqone hRceil
  have hnTwo : n ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
  have hnsquare : n ^ 2 ≤ (2 ^ n) ^ 2 := by gcongr
  have hpowSquare : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
    calc
      (2 ^ n) ^ 2 = 2 ^ (n * 2) := by rw [Nat.pow_mul]
      _ = 2 ^ (2 * n) := by rw [Nat.mul_comm]
  have hR0 : R₀ ≤ 2 ^ (2 * n) := by
    calc
      R₀ ≤ n ^ 2 := hR0n
      _ ≤ (2 ^ n) ^ 2 := hnsquare
      _ = 2 ^ (2 * n) := hpowSquare
  have hexists : ∃ i : ℕ, target ≤ M ^ i * R₀ := by
    refine ⟨n, ?_⟩
    have hpowM : 2 ^ n ≤ M ^ n := by gcongr
    have hprod : M ^ n ≤ M ^ n * R₀ := by
      calc
        M ^ n = M ^ n * 1 := by simp
        _ ≤ M ^ n * R₀ := Nat.mul_le_mul_left _ (le_max_left 1 _)
    exact htarget.trans (hnTwo.trans (hpowM.trans hprod))
  have hfind : Nat.find hexists ≤ n := Nat.find_min' hexists (by
    have hpowM : 2 ^ n ≤ M ^ n := by gcongr
    have hprod : M ^ n ≤ M ^ n * R₀ := by
      calc
        M ^ n = M ^ n * 1 := by simp
        _ ≤ M ^ n * R₀ := Nat.mul_le_mul_left _ (le_max_left 1 _)
    exact htarget.trans (hnTwo.trans (hpowM.trans hprod)))
  have hdef : topScale n σ ζ = M ^ Nat.find hexists * R₀ := by
    unfold topScale
    rfl
  have hMpow : M ^ Nat.find hexists ≤ (2 ^ n) ^ n := by
    calc
      M ^ Nat.find hexists ≤ M ^ n := by gcongr
      _ ≤ (2 ^ n) ^ n := by gcongr
  have hupper : topScale n σ ζ ≤ (2 ^ n) ^ n * 2 ^ (2 * n) := by
    rw [hdef]
    exact Nat.mul_le_mul hMpow hR0
  calc
    topScale n σ ζ ≤ (2 ^ n) ^ n * 2 ^ (2 * n) := hupper
    _ = 2 ^ (n * n) * 2 ^ (2 * n) := by
      rw [show (2 ^ n) ^ n = 2 ^ (n * n) by rw [Nat.pow_mul]]
    _ = 2 ^ (n * n + 2 * n) := by rw [← Nat.pow_add]
    _ = 2 ^ (n ^ 2 + 2 * n) := by congr 1 <;> ring

private theorem two_nat_pow_le_exp (k : ℕ) :
    (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    linarith
  calc
    (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := by gcongr
    _ = Real.exp (k : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

theorem height_counts9_union_tail (P : Params9) (hc : HeightChoice9 P)
    (hadm : hc.Admissible) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (2 : ℝ) ^ n *
        (2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
          ((hc.levels n + 1 : ℕ) : ℝ) *
          Real.exp (-((n : ℝ) ^ (10 : ℝ)) / 12)) ≤ Real.exp (-(n : ℝ)) := by
  rcases hadm with ⟨hσhpos, hσhζ, hζlt, hθpos, hθlt, ha, hab, hχa, hbpos, hbε, hε, hcase⟩
  have hσh1 : hc.σh < 1 := lt_trans hσhζ hζlt
  have hζpos : 0 < hc.ζ := lt_trans hσhpos hσhζ
  refine ⟨100, ?_⟩
  intro n hn
  have hn5 : 5 ≤ n := by omega
  have hlevels : hc.levels n ≤ 2 ^ (n ^ 2 + 2 * n) := by
    simpa [HeightChoice9.levels] using
      (topScale_coarse_bound n hc.σh hc.ζ hn5 hσh1 hζpos hζlt)
  let k : ℕ := n ^ 2 + 2 * n
  have hkpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hlevelsPlus : hc.levels n + 1 ≤ 2 ^ (k + 1) := by
    calc
      hc.levels n + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right hlevels 1
      _ ≤ 2 ^ k + 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have hdim : n - P.m n ≤ n := Nat.sub_le _ _
  have hcardEq : (Finset.univ : Finset (CubeVertex (n - P.m n))).card =
      2 ^ (n - P.m n) := by simp [CubeVertex]
  have hcard : (Finset.univ : Finset (CubeVertex (n - P.m n))).card ≤ 2 ^ n := by
    rw [hcardEq]
    gcongr
  have hfactorNat : 2 ^ n *
      (2 * (Finset.univ : Finset (CubeVertex (n - P.m n))).card *
        (hc.levels n + 1)) ≤ 2 ^ (n ^ 2 + 4 * n + 2) := by
    rw [hcardEq]
    calc
      2 ^ n * (2 * 2 ^ (n - P.m n) * (hc.levels n + 1)) ≤
          2 ^ n * (2 * 2 ^ n * 2 ^ (k + 1)) := by gcongr
      _ = 2 ^ (n ^ 2 + 4 * n + 2) := by
        have htwo : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
        rw [htwo]
        calc
          2 ^ n * (2 ^ (n + 1) * 2 ^ (k + 1)) =
              2 ^ (n + (n + 1 + (k + 1))) := by
                rw [← Nat.pow_add, ← Nat.pow_add]
          _ = 2 ^ (n ^ 2 + 4 * n + 2) := by congr 1 <;> dsimp [k] <;> omega
  have hfactorReal : (2 : ℝ) ^ n *
      (2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
        ((hc.levels n + 1 : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ (n ^ 2 + 4 * n + 2) := by exact_mod_cast hfactorNat
  have hfactorExp : (2 : ℝ) ^ n *
      (2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
        ((hc.levels n + 1 : ℕ) : ℝ)) ≤
      Real.exp ((n ^ 2 + 4 * n + 2 : ℕ) : ℝ) := by
    exact hfactorReal.trans (two_nat_pow_le_exp (n ^ 2 + 4 * n + 2))
  have hn100R : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1R : 1 ≤ (n : ℝ) := le_trans (by norm_num) hn100R
  have hcube : 100 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    have hmul := mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hn100R)
    nlinarith [hmul]
  have hquad : 100 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 100) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hn100R)
    nlinarith [hprod]
  have hbig : 12 * ((n : ℝ) ^ 2 + 5 * (n : ℝ) + 2) ≤ (n : ℝ) ^ 3 := by
    nlinarith [hcube, hquad, hn100R]
  have hpow310 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 10 :=
    pow_le_pow_right₀ hn1R (by norm_num)
  have hbig10 : (n : ℝ) ^ 2 + 5 * (n : ℝ) + 2 ≤ (n : ℝ) ^ 10 / 12 := by
    nlinarith [hbig, hpow310]
  have hpow10 : (n : ℝ) ^ (10 : ℝ) = (n : ℝ) ^ (10 : ℕ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hBcast : ((n ^ 2 + 4 * n + 2 : ℕ) : ℝ) =
      (n : ℝ) ^ 2 + 4 * (n : ℝ) + 2 := by norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  have hexponent : ((n ^ 2 + 4 * n + 2 : ℕ) : ℝ) -
      (n : ℝ) ^ (10 : ℝ) / 12 ≤ -(n : ℝ) := by
    rw [hBcast, hpow10]
    nlinarith [hbig10]
  calc
    (2 : ℝ) ^ n *
        (2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
          ((hc.levels n + 1 : ℕ) : ℝ) *
          Real.exp (-((n : ℝ) ^ (10 : ℝ)) / 12)) =
        ((2 : ℝ) ^ n *
          (2 * ((Finset.univ : Finset (CubeVertex (n - P.m n))).card : ℝ) *
            ((hc.levels n + 1 : ℕ) : ℝ))) *
          Real.exp (-((n : ℝ) ^ (10 : ℝ)) / 12) := by ring
    _ ≤ Real.exp ((n ^ 2 + 4 * n + 2 : ℕ) : ℝ) *
          Real.exp (-((n : ℝ) ^ (10 : ℝ)) / 12) :=
        mul_le_mul_of_nonneg_right hfactorExp (Real.exp_nonneg _)
    _ = Real.exp (((n ^ 2 + 4 * n + 2 : ℕ) : ℝ) -
          (n : ℝ) ^ (10 : ℝ) / 12) := by rw [← Real.exp_add]; congr 1 <;> ring
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr hexponent

private theorem active_center_of_good_heights
    (Pp A : Pos9 P hc n → Bool) (hg : GoodHeights9 Pp A) (v : CubeVertex n) :
    ∃ c : Pos9 P hc n,
      c.slice = specialWord9 (P.m n) v ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n ∧
      c.level.val = height9 Pp A v ∧ activeAt9 Pp A c := by
  classical
  obtain ⟨hbelow, hgood, _⟩ := hg v
  let j : Fin (hc.levels n + 1) := ⟨height9 Pp A v, by omega⟩
  have hnotbad : ¬ badAt9 Pp A v j := by
    simpa [j] using hgood
  have hnotHole : ¬ holeIn9 Finset.univ Pp A v j := by
    intro hh'
    exact hnotbad (Or.inl hh')
  have hcand : ∃ c : Pos9 P hc n,
      c.slice = specialWord9 (P.m n) v ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n ∧
      c.level = j ∧ activeAt9 Pp A c := by
    by_contra hnone
    apply hnotHole
    intro c hc hs hd hj
    intro hactive
    exact hnone ⟨c, hs, hd, hj, hactive⟩
  obtain ⟨c, hslice, hdist, hlevel, hactive⟩ := hcand
  refine ⟨c, hslice, hdist, ?_, hactive⟩
  exact congrArg Fin.val hlevel

noncomputable def chosenCenterOfGoodHeights
    (Pp A : Pos9 P hc n → Bool) (hg : GoodHeights9 Pp A) :
    CubeVertex n → Pos9 P hc n :=
  fun v => Classical.choose (active_center_of_good_heights (P := P) (hc := hc) (n := n) Pp A hg v)

theorem chosenCenterOfGoodHeights_spec
    (Pp A : Pos9 P hc n → Bool) (hg : GoodHeights9 Pp A) (v : CubeVertex n) :
    let c := chosenCenterOfGoodHeights (P := P) (hc := hc) (n := n) Pp A hg v
    c.slice = specialWord9 (P.m n) v ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n ∧
      c.level.val = height9 Pp A v ∧ activeAt9 Pp A c := by
  exact Classical.choose_spec
    (active_center_of_good_heights (P := P) (hc := hc) (n := n) Pp A hg v)

theorem crowdSame_le_univ (C : Finset (Pos9 P hc n))
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) (R : ℕ) :
    crowdSame9 C Pp A v j R ≤ crowdSame9 Finset.univ Pp A v j R := by
  unfold crowdSame9
  apply Finset.card_mono
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨Finset.mem_univ _, hc.2⟩

theorem crowdAdj_le_univ (C : Finset (Pos9 P hc n))
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) :
    crowdAdj9 C Pp A v j ≤ crowdAdj9 Finset.univ Pp A v j := by
  unfold crowdAdj9
  apply Finset.card_mono
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨Finset.mem_univ _, hc.2⟩

theorem bad_crowd_mono_univ
    (C : Finset (Pos9 P hc n)) (t : ℝ) (Pp A : Pos9 P hc n → Bool)
    (v : CubeVertex n) (j : Fin (hc.levels n + 1))
    (hbad : badIn9 C t Pp A v j) (hnotHole : ¬ holeIn9 C Pp A v j) :
    ∃ j' : Fin (hc.levels n + 1), Nat.dist j.val j'.val ≤ 2 ∧
      (t * (n : ℝ) ^ ((P.χ : ℝ) / 2) <
          (crowdSame9 Finset.univ Pp A v j' (P.radius n) : ℝ) ∨
        t * (n : ℝ) ^ ((P.χ : ℝ) / 2) <
          (crowdAdj9 Finset.univ Pp A v j' : ℝ) ∨
        t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
          (crowdSame9 Finset.univ Pp A v j' (P.radius n + 1) : ℝ)) := by
  classical
  rcases hbad with hhole | ⟨j', hdist, hcounts⟩
  · exact (hnotHole hhole).elim
  · refine ⟨j', hdist, ?_⟩
    rcases hcounts with hsame | hadj | hplus
    · exact Or.inl (lt_of_lt_of_le hsame (by
        exact_mod_cast crowdSame_le_univ (P := P) (hc := hc) (n := n)
          C Pp A v j' (P.radius n)))
    · exact Or.inr (Or.inl (lt_of_lt_of_le hadj (by
        exact_mod_cast crowdAdj_le_univ (P := P) (hc := hc) (n := n)
          C Pp A v j')))
    · exact Or.inr (Or.inr (lt_of_lt_of_le hplus (by
        exact_mod_cast crowdSame_le_univ (P := P) (hc := hc) (n := n)
          C Pp A v j' (P.radius n + 1))))

theorem sharedConsulted_local_bounds
    (v v' : CubeVertex n) (R' : ℕ) (c : Pos9 P hc n)
    (h : c ∈ consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R') :
    _root_.hammingDist c.slice (specialWord9 (P.m n) v) ≤ 2 * R' + 1 ∧
    _root_.hammingDist c.slice (specialWord9 (P.m n) v') ≤ 2 * R' + 1 ∧
    _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n + 2 * R' + 1 ∧
    _root_.hammingDist c.location (residualWord9 (P.m n) v') ≤ P.radius n + 2 * R' + 1 := by
  classical
  rcases Finset.mem_inter.mp h with ⟨hv, hv'⟩
  unfold consulted9 at hv hv'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
  exact ⟨hv.1, hv'.1, hv.2, hv'.2⟩

theorem specialProjectionDist_le {m n : ℕ} (hm : m ≤ n) (v w : CubeVertex n) :
    _root_.hammingDist (specialWord9 m v) (specialWord9 m w) ≤ _root_.hammingDist v w := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i => specialWord9 m v i ≠ specialWord9 m w i)
  let t : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ w i)
  let f : Fin m → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
  have hmap : Set.MapsTo f s t := by
    intro i hi
    have his : specialWord9 m v i ≠ specialWord9 m w i := (Finset.mem_filter.mp hi).2
    have hcoordv : specialWord9 m v i = v (f i) := by
      simp [specialWord9, f, lt_of_lt_of_le i.isLt hm]
    have hcoordw : specialWord9 m w i = w (f i) := by
      simp [specialWord9, f, lt_of_lt_of_le i.isLt hm]
    have hdiff : v (f i) ≠ w (f i) := by simpa [hcoordv, hcoordw] using his
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩
  have hinj : Set.InjOn f s := by
    intro i hi j hj h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    exact hv
  have hsubset : s.image f ⊆ t := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
    exact hmap hi
  have hcardImg : s.card = (s.image f).card :=
    (Finset.card_image_of_injOn hinj).symm
  calc
    _ = s.card := by simp [s, _root_.hammingDist]
    _ = (s.image f).card := hcardImg
    _ ≤ t.card := Finset.card_le_card hsubset
    _ = _ := by simp [t, _root_.hammingDist]

theorem residualProjectionDist_le {m n : ℕ} (hm : m ≤ n) (v w : CubeVertex n) :
    _root_.hammingDist (residualWord9 m v) (residualWord9 m w) ≤ _root_.hammingDist v w := by
  classical
  let k := n - m
  let s : Finset (Fin k) := Finset.univ.filter (fun i => residualWord9 m v i ≠ residualWord9 m w i)
  let t : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ w i)
  let f : Fin k → Fin n := fun i => ⟨m + i.val, by have := i.isLt; omega⟩
  have hmap : Set.MapsTo f s t := by
    intro i hi
    have his : residualWord9 m v i ≠ residualWord9 m w i := (Finset.mem_filter.mp hi).2
    have hcoordv : residualWord9 m v i = v (f i) := by
      simp [residualWord9, f]
    have hcoordw : residualWord9 m w i = w (f i) := by
      simp [residualWord9, f]
    have hdiff : v (f i) ≠ w (f i) := by simpa [hcoordv, hcoordw] using his
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩
  have hinj : Set.InjOn f s := by
    intro i hi j hj h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    omega
  have hsubset : s.image f ⊆ t := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
    exact hmap hi
  have hcardImg : s.card = (s.image f).card :=
    (Finset.card_image_of_injOn hinj).symm
  calc
    _ = s.card := by simp [s, k, _root_.hammingDist]
    _ = (s.image f).card := hcardImg
    _ ≤ t.card := Finset.card_le_card hsubset
    _ = _ := by simp [t, _root_.hammingDist]

theorem cubeWord_eq_of_components {m n : ℕ} (hm : m ≤ n) {v w : CubeVertex n}
    (hs : specialWord9 m v = specialWord9 m w)
    (hr : residualWord9 m v = residualWord9 m w) : v = w := by
  funext i
  by_cases hmi : i.val < m
  · have h := congrArg (fun z : CubeVertex m => z ⟨i.val, hmi⟩) hs
    simpa [specialWord9, hmi] using h
  · let j : Fin (n - m) := ⟨i.val - m, by omega⟩
    have h := congrArg (fun z : CubeVertex (n - m) => z j) hr
    have hidx : m + j.val = i.val := by dsimp [j]; omega
    simpa [residualWord9, j, hidx] using h

theorem splitProjectionDist_add_le {m n : ℕ} (hm : m ≤ n) (v w : CubeVertex n) :
    _root_.hammingDist (specialWord9 m v) (specialWord9 m w) +
        _root_.hammingDist (residualWord9 m v) (residualWord9 m w) ≤
      _root_.hammingDist v w := by
  classical
  let k := n - m
  let s : Finset (Fin m) := Finset.univ.filter (fun i => specialWord9 m v i ≠ specialWord9 m w i)
  let r : Finset (Fin k) := Finset.univ.filter (fun i => residualWord9 m v i ≠ residualWord9 m w i)
  let t : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ w i)
  let fs : Fin m → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
  let fr : Fin k → Fin n := fun i => ⟨m + i.val, by have := i.isLt; omega⟩
  have hsMap : Set.MapsTo fs s t := by
    intro i hi
    have hcoordv : specialWord9 m v i = v (fs i) := by
      simp [specialWord9, fs, lt_of_lt_of_le i.isLt hm]
    have hcoordw : specialWord9 m w i = w (fs i) := by
      simp [specialWord9, fs, lt_of_lt_of_le i.isLt hm]
    have hdiff : v (fs i) ≠ w (fs i) := by
      simpa [hcoordv, hcoordw] using (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩
  have hrMap : Set.MapsTo fr r t := by
    intro i hi
    have hcoordv : residualWord9 m v i = v (fr i) := by simp [residualWord9, fr]
    have hcoordw : residualWord9 m w i = w (fr i) := by simp [residualWord9, fr]
    have hdiff : v (fr i) ≠ w (fr i) := by
      simpa [hcoordv, hcoordw] using (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩
  have hsInj : Set.InjOn fs s := by
    intro i hi j hj h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [fs] at hv
    exact hv
  have hrInj : Set.InjOn fr r := by
    intro i hi j hj h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [fr] at hv
    omega
  have hdisj : Disjoint (s.image fs) (r.image fr) := by
    rw [Finset.disjoint_left]
    intro z hzS hzR
    rcases Finset.mem_image.mp hzS with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hzR with ⟨j, hj, hEq⟩
    have hv := congrArg Fin.val hEq.symm
    dsimp [fs, fr] at hv
    have hiLt : i.val < m := i.isLt
    have hmLe : m ≤ m + j.val := Nat.le_add_right _ _
    omega
  have hsub : s.image fs ∪ r.image fr ⊆ t := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      exact hsMap hi
    · rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      exact hrMap hi
  have hsImg : s.card = (s.image fs).card := (Finset.card_image_of_injOn hsInj).symm
  have hrImg : r.card = (r.image fr).card := (Finset.card_image_of_injOn hrInj).symm
  have hsum : s.card + r.card ≤ t.card := by
    calc
      s.card + r.card = (s.image fs).card + (r.image fr).card := by rw [hsImg, hrImg]
      _ = (s.image fs ∪ r.image fr).card := by rw [Finset.card_union_of_disjoint hdisj]
      _ ≤ t.card := Finset.card_le_card hsub
  simpa [s, r, t, k, _root_.hammingDist] using hsum

theorem splitProjectionDist_ge {m n : ℕ} (hm : m ≤ n) (v w : CubeVertex n) :
    _root_.hammingDist v w ≤
      _root_.hammingDist (specialWord9 m v) (specialWord9 m w) +
        _root_.hammingDist (residualWord9 m v) (residualWord9 m w) := by
  classical
  let k := n - m
  let s : Finset (Fin m) := Finset.univ.filter (fun i => specialWord9 m v i ≠ specialWord9 m w i)
  let r : Finset (Fin k) := Finset.univ.filter (fun i => residualWord9 m v i ≠ residualWord9 m w i)
  let t : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ w i)
  let fs : Fin m → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
  let fr : Fin k → Fin n := fun i => ⟨m + i.val, by have := i.isLt; omega⟩
  have hcover : t ⊆ s.image fs ∪ r.image fr := by
    intro z hz
    have hdiff := (Finset.mem_filter.mp hz).2
    by_cases hzm : z.val < m
    · let i : Fin m := ⟨z.val, hzm⟩
      have hfs : fs i = z := by apply Fin.ext; rfl
      have hcoordv : specialWord9 m v i = v (fs i) := by
        simp [specialWord9, fs, lt_of_lt_of_le i.isLt hm]
      have hcoordw : specialWord9 m w i = w (fs i) := by
        simp [specialWord9, fs, lt_of_lt_of_le i.isLt hm]
      have hsi : i ∈ s := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [hfs, hcoordv, hcoordw] using hdiff
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hsi, hfs⟩)
    · let i : Fin k := ⟨z.val - m, by dsimp [k]; omega⟩
      have hfr : fr i = z := by
        apply Fin.ext
        dsimp [fr, i, k]
        omega
      have hcoordv : residualWord9 m v i = v (fr i) := by simp [residualWord9, fr]
      have hcoordw : residualWord9 m w i = w (fr i) := by simp [residualWord9, fr]
      have hri : i ∈ r := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [hfr, hcoordv, hcoordw] using hdiff
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hri, hfr⟩)
  have hcard : t.card ≤ s.card + r.card := by
    calc
      t.card ≤ (s.image fs ∪ r.image fr).card := Finset.card_le_card hcover
      _ ≤ (s.image fs).card + (r.image fr).card := Finset.card_union_le _ _
      _ ≤ s.card + r.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
  simpa [s, r, t, k, _root_.hammingDist] using hcard

theorem sharedConsulted_residual_separation {P : Params9} {hc : HeightChoice9 P} {n : ℕ}
    (hm : P.m n ≤ n) (v v' : CubeVertex n) (R' : ℕ)
    (hsep : 16 * (R' : ℝ) ≤ (_root_.hammingDist v v' : ℝ))
    (c : Pos9 P hc n)
    (hshared : c ∈ consulted9 (P := P) (hc := hc) (n := n) v R' ∩ consulted9 v' R') :
    12 * R' - 2 ≤
      _root_.hammingDist (residualWord9 (P.m n) v) (residualWord9 (P.m n) v') := by
  have hlocal := sharedConsulted_local_bounds v v' R' c hshared
  have hspecial : _root_.hammingDist (specialWord9 (P.m n) v)
      (specialWord9 (P.m n) v') ≤ 4 * R' + 2 := by
    calc
      _ ≤ _root_.hammingDist (specialWord9 (P.m n) v) c.slice +
          _root_.hammingDist c.slice (specialWord9 (P.m n) v') :=
            _root_.hammingDist_triangle _ _ _
      _ ≤ (2 * R' + 1) + (2 * R' + 1) := by
        exact Nat.add_le_add (by simpa [_root_.hammingDist_comm] using hlocal.1) hlocal.2.1
      _ = 4 * R' + 2 := by omega
  have hfull : 16 * R' ≤ _root_.hammingDist v v' := by exact_mod_cast hsep
  have hprojection := splitProjectionDist_ge hm v v'
  omega

theorem adjacent_projection_classification {m n : ℕ} (hm : m ≤ n) (v w : CubeVertex n)
    (hadj : _root_.hammingDist v w = 1) :
    (_root_.hammingDist (specialWord9 m v) (specialWord9 m w) = 1 ∧
      residualWord9 m v = residualWord9 m w) ∨
    (specialWord9 m v = specialWord9 m w ∧
      _root_.hammingDist (residualWord9 m v) (residualWord9 m w) = 1) := by
  have hsle := specialProjectionDist_le hm v w
  have hrle := residualProjectionDist_le hm v w
  have hsum := splitProjectionDist_add_le hm v w
  have hsbound : _root_.hammingDist (specialWord9 m v) (specialWord9 m w) ≤ 1 := by omega
  have hrbound : _root_.hammingDist (residualWord9 m v) (residualWord9 m w) ≤ 1 := by omega
  by_cases hs0 : _root_.hammingDist (specialWord9 m v) (specialWord9 m w) = 0
  · have hsEq : specialWord9 m v = specialWord9 m w :=
      (hammingDist_lt_one).mp (by omega)
    have hrpos : 0 < _root_.hammingDist (residualWord9 m v) (residualWord9 m w) := by
      by_contra hnot
      have hr0 : _root_.hammingDist (residualWord9 m v) (residualWord9 m w) = 0 := by omega
      have hrEq : residualWord9 m v = residualWord9 m w :=
        (hammingDist_lt_one).mp (by omega)
      have hvw : v = w := cubeWord_eq_of_components hm hsEq hrEq
      subst w
      simp at hadj
    have hrone : _root_.hammingDist (residualWord9 m v) (residualWord9 m w) = 1 := by omega
    exact Or.inr ⟨hsEq, hrone⟩
  · have hsone : _root_.hammingDist (specialWord9 m v) (specialWord9 m w) = 1 := by omega
    have hr0 : _root_.hammingDist (residualWord9 m v) (residualWord9 m w) = 0 := by omega
    have hrEq : residualWord9 m v = residualWord9 m w :=
      (hammingDist_lt_one).mp (by omega)
    exact Or.inl ⟨hsone, hrEq⟩

theorem special_neighbor_count_le {m n : ℕ} (hm : m ≤ n) (v : CubeVertex n) :
    (Finset.univ.filter (fun w : CubeVertex n =>
      _root_.hammingDist v w = 1 ∧
        _root_.hammingDist (specialWord9 m v) (specialWord9 m w) = 1)).card ≤ m := by
  classical
  let S : Finset (CubeVertex n) := Finset.univ.filter (fun w =>
    _root_.hammingDist v w = 1 ∧
      _root_.hammingDist (specialWord9 m v) (specialWord9 m w) = 1)
  let T : Finset (CubeVertex m) := Finset.univ.filter fun z =>
    (cube m).Adj (specialWord9 m v) z
  let f : CubeVertex n → CubeVertex m := fun w => specialWord9 m w
  have hT : T.card ≤ m := cube_adj_neighbors_card_le m (specialWord9 m v)
  have hmap : Set.MapsTo f S T := by
    intro w hw
    change w ∈ S at hw
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    change f w ∈ T
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa [OAI.HypercubeRamsey.cube] using hw.2
  have hinj : Set.InjOn f S := by
    intro w hw w' hw' heq
    have hw'cond : w ∈ S := by change w ∈ S at hw; exact hw
    have hw'cond' : w' ∈ S := by change w' ∈ S at hw'; exact hw'
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hw'cond hw'cond'
    have hres (x : CubeVertex n) (hx :
        _root_.hammingDist v x = 1 ∧
          _root_.hammingDist (specialWord9 m v) (specialWord9 m x) = 1) :
        residualWord9 m v = residualWord9 m x := by
      rcases adjacent_projection_classification hm v x hx.1 with hgood | hbad
      · exact hgood.2
      · have : (0 : ℕ) = 1 := by simpa [hbad.1] using hx.2
        omega
    exact cubeWord_eq_of_components hm heq
      ((hres w hw'cond).symm.trans (hres w' hw'cond'))
  have hcardImg : S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
  calc
    S.card = (S.image f).card := hcardImg
    _ ≤ T.card := by
      apply Finset.card_le_card
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact hmap hw
    _ ≤ m := hT

theorem level_window_card_le_three (H h : ℕ) :
    (Finset.univ.filter (fun j : Fin (H + 1) => Nat.dist j.val h ≤ 1)).card ≤ 3 := by
  classical
  let J : Finset (Fin (H + 1)) :=
    Finset.univ.filter (fun j => Nat.dist j.val h ≤ 1)
  let values : Finset ℕ := {h - 1, h, h + 1}
  have himage : J.image Fin.val ⊆ values := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    have hdist := (Finset.mem_filter.mp hj).2
    unfold Nat.dist at hdist
    simp only [values, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hvalues : values.card ≤ 3 := by
    simpa [values] using
      (Finset.card_le_three : ({h - 1, h, h + 1} : Finset ℕ).card ≤ 3)
  calc
    _ = J.card := by rfl
    _ = (J.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ values.card := Finset.card_le_card himage
    _ ≤ 3 := hvalues

theorem cubeAdj_exists_flip {n : ℕ} (v w : CubeVertex n)
    (hadj : (cube n).Adj v w) : ∃ i : Fin n, cubeFlip v i = w := by
  classical
  change _root_.hammingDist v w = 1 at hadj
  let D : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ w i)
  have hcard : D.card = 1 := by simpa [D, _root_.hammingDist] using hadj
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hdiff : v i ≠ w i := by
    have hmem : i ∈ D := by rw [hi]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hother (j : Fin n) (hji : j ≠ i) : v j = w j := by
    by_contra hne
    have hmem : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hi] at hmem
    simp at hmem
    exact hji hmem
  have hflip : w i = !v i := by
    cases hv : v i <;> cases hw : w i <;> simp_all
  refine ⟨i, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j
    simp [cubeFlip, hflip]
  · have hEq := hother j hji
    simp [cubeFlip, hji, hEq]

theorem hammingDist_cubeFlip_of_eq {d : ℕ} (x y : CubeVertex d) (i : Fin d)
    (hi : x i = y i) :
    _root_.hammingDist x (cubeFlip y i) = _root_.hammingDist x y + 1 := by
  classical
  let D : Finset (Fin d) := Finset.univ.filter (fun j => x j ≠ y j)
  have hfilter : Finset.univ.filter (fun j : Fin d => x j ≠ cubeFlip y i j) = insert i D := by
    ext j
    by_cases hji : j = i
    · subst j
      cases hy : y i <;> simp [D, hi, hy, cubeFlip]
    · have hflip : cubeFlip y i j = y j := by simp [cubeFlip, hji]
      simp [D, hji, hflip]
  have hiD : i ∉ D := by simp [D, hi]
  rw [_root_.hammingDist, hfilter]
  rw [Finset.card_insert_of_notMem hiD]
  simp [D, _root_.hammingDist]

theorem card_flip_neighbors_bound {d : ℕ} (v : CubeVertex d)
    (B : Finset (CubeVertex d)) (D : Finset (Fin d))
    (hB : ∀ b ∈ B, ∃ i ∈ D, cubeFlip v i = b) : B.card ≤ D.card := by
  classical
  let B' := {b : CubeVertex d // b ∈ B}
  let f : B' → Fin d := fun b => Classical.choose (hB b.1 b.2)
  have hspec (b : B') : cubeFlip v (f b) = b.1 := by
    exact (Classical.choose_spec (hB b.1 b.2)).2
  have hmem (b : B') : f b ∈ D := (Classical.choose_spec (hB b.1 b.2)).1
  have hinj : Function.Injective f := by
    intro b c hfc
    apply Subtype.ext
    calc
      b.1 = cubeFlip v (f b) := (hspec b).symm
      _ = cubeFlip v (f c) := by rw [hfc]
      _ = c.1 := hspec c
  have hsubcard : B.card = Fintype.card B' := (Fintype.card_coe B).symm
  have huniv : (Finset.univ : Finset B').card = Fintype.card B' := by simp
  have himagecard : (Finset.univ.image f).card = Fintype.card B' := by
    calc
      (Finset.univ.image f).card = (Finset.univ : Finset B').card :=
        Finset.card_image_of_injective (Finset.univ : Finset B') hinj
      _ = Fintype.card B' := huniv
  have himage : Finset.univ.image f ⊆ D := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨b, _, rfl⟩
    exact hmem b
  calc
    B.card = Fintype.card B' := hsubcard
    _ = (Finset.univ.image f).card := himagecard.symm
    _ ≤ D.card := Finset.card_le_card himage

theorem specialWord9_cubeFlip_residual {m n : ℕ} (hm : m ≤ n)
    (v : CubeVertex n) (i : Fin n) (hi : m ≤ i.val) :
    specialWord9 m (cubeFlip v i) = specialWord9 m v := by
  funext k
  let k' : Fin n := ⟨k.val, lt_of_lt_of_le k.isLt hm⟩
  have hki : k' ≠ i := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [k'] at hv
    omega
  simp [specialWord9, k', cubeFlip, hki, lt_of_lt_of_le k.isLt hm]

theorem residualWord9_cubeFlip_special {m n : ℕ} (hm : m ≤ n)
    (v : CubeVertex n) (i : Fin n) (hi : i.val < m) :
    residualWord9 m (cubeFlip v i) = residualWord9 m v := by
  funext k
  let k' : Fin n := ⟨m + k.val, by omega⟩
  have hki : k' ≠ i := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [k'] at hv
    omega
  simp [residualWord9, k', cubeFlip, hki]

theorem specialWord9_doubleFlip_at_first {m n : ℕ} (hm : m ≤ n)
    (v : CubeVertex n) (i j : Fin n) (hij : i ≠ j) (hi : i.val < m) :
    specialWord9 m (cubeFlip (cubeFlip v i) j) ⟨i.val, hi⟩ ≠
      specialWord9 m v ⟨i.val, hi⟩ := by
  let k' : Fin n := ⟨i.val, lt_of_lt_of_le hi hm⟩
  have hki : k' = i := Fin.ext rfl
  have hkj : k' ≠ j := by
    intro heq
    exact hij (hki.symm.trans heq)
  have houter : cubeFlip (cubeFlip v i) j k' = cubeFlip v i k' :=
    Function.update_of_ne hkj _ _
  have hinner : cubeFlip v i k' = !v k' := by
    rw [hki]
    simp [cubeFlip]
  have hsource : specialWord9 m v ⟨i.val, hi⟩ = v k' := by
    simp [specialWord9, k', lt_of_lt_of_le hi hm]
  have htarget : specialWord9 m (cubeFlip (cubeFlip v i) j) ⟨i.val, hi⟩ =
      cubeFlip (cubeFlip v i) j k' := by
    simp [specialWord9, k', lt_of_lt_of_le hi hm]
  rw [htarget, houter, hinner, hsource]
  cases hv : v k' <;> simp [hv]

theorem residualWord9_cubeFlip_residual {m n : ℕ} (hm : m ≤ n)
    (v : CubeVertex n) (i : Fin n) (hi : m ≤ i.val) :
    let k : Fin (n - m) := ⟨i.val - m, by omega⟩
    residualWord9 m (cubeFlip v i) = cubeFlip (residualWord9 m v) k := by
  dsimp
  let k : Fin (n - m) := ⟨i.val - m, by omega⟩
  funext l
  let l' : Fin n := ⟨m + l.val, by omega⟩
  have hlk : l = k ∨ l ≠ k := Classical.em (l = k)
  rcases hlk with hlk | hlk
  · subst l
    have hidx : l' = i := by
      apply Fin.ext
      dsimp [l', k]
      omega
    simp [residualWord9, cubeFlip, l', k, hidx]
  · have hidx : l' ≠ i := by
      intro heq
      apply hlk
      apply Fin.ext
      have hval := congrArg Fin.val heq
      dsimp [l', k] at hval ⊢
      omega
    simp [residualWord9, cubeFlip, l', k, hidx, hlk]

theorem cubeFlip_involutive {d : ℕ} (v : CubeVertex d) (i : Fin d) :
    cubeFlip (cubeFlip v i) i = v := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [cubeFlip]
  · simp [cubeFlip, hki]

theorem hammingDist_two_cubeFlips {d : ℕ} (v : CubeVertex d) (i j : Fin d)
    (hij : i ≠ j) :
    _root_.hammingDist v (cubeFlip (cubeFlip v i) j) = 2 := by
  classical
  have hcoordi : cubeFlip (cubeFlip v i) j i = !v i := by
    have houter : cubeFlip (cubeFlip v i) j i = cubeFlip v i i :=
      Function.update_of_ne hij _ _
    calc
      _ = cubeFlip v i i := houter
      _ = !v i := by simp [cubeFlip]
  have hcoordj : cubeFlip (cubeFlip v i) j j = !v j := by
    have hinner : cubeFlip v i j = v j := Function.update_of_ne hij.symm _ _
    calc
      _ = !(cubeFlip v i j) := by simp [cubeFlip]
      _ = !v j := by rw [hinner]
  have hcoord_other (k : Fin d) (hki : k ≠ i) (hkj : k ≠ j) :
      cubeFlip (cubeFlip v i) j k = v k := by
    have hinner : cubeFlip v i k = v k := Function.update_of_ne hki _ _
    have houter : cubeFlip (cubeFlip v i) j k = cubeFlip v i k :=
      Function.update_of_ne hkj _ _
    exact houter.trans hinner
  have hfilter :
      Finset.univ.filter (fun k : Fin d => v k ≠ cubeFlip (cubeFlip v i) j k) = {i, j} := by
    ext k
    by_cases hki : k = i
    · subst k
      cases hv : v i <;> simp [hcoordi, hv, hij]
    · by_cases hkj : k = j
      · subst k
        cases hv : v j <;> simp [hcoordj, hv, hij]
      · have hcoord := hcoord_other k hki hkj
        simp [hcoord, hki, hkj]
  rw [_root_.hammingDist, hfilter]
  simp [hij]

private theorem finProb_prod_pr_dep_bound {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinProb α) (ν : FinProb β) (Q : α → Prop) (E : α → β → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ a, Q a → ν.pr (E a) ≤ ε) :
    (FinProb.prod μ ν).pr (fun ab => Q ab.1 ∧ E ab.1 ab.2) ≤ ε := by
  classical
  have hfactor : (FinProb.prod μ ν).pr (fun ab => Q ab.1 ∧ E ab.1 ab.2) =
      ∑ a, μ.w a * ν.pr (fun b => Q a ∧ E a b) := by
    calc
      (FinProb.prod μ ν).pr (fun ab => Q ab.1 ∧ E ab.1 ab.2) =
          ∑ a, ∑ b, if Q a ∧ E a b then μ.w a * ν.w b else 0 := by
        unfold FinProb.pr FinProb.prod
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        simp [FinProb.prod]
      _ = ∑ a, μ.w a * ν.pr (fun b => Q a ∧ E a b) := by
        apply Finset.sum_congr rfl
        intro a ha
        calc
          (∑ b, if Q a ∧ E a b then μ.w a * ν.w b else 0) =
              ∑ b, μ.w a * (if Q a ∧ E a b then ν.w b else 0) := by
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hab : Q a ∧ E a b <;> simp [hab, mul_assoc]
          _ = μ.w a * ∑ b, if Q a ∧ E a b then ν.w b else 0 := by
            rw [Finset.mul_sum]
          _ = μ.w a * ν.pr (fun b => Q a ∧ E a b) := by
            congr 1
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hab : Q a ∧ E a b <;> simp [hab]
  calc
    (FinProb.prod μ ν).pr (fun ab => Q ab.1 ∧ E ab.1 ab.2) =
        ∑ a, μ.w a * ν.pr (fun b => Q a ∧ E a b) := hfactor
    _ ≤ ∑ a, μ.w a * ε := by
      apply Finset.sum_le_sum
      intro a ha
      have htail : ν.pr (fun b => Q a ∧ E a b) ≤ ε := by
        by_cases hq : Q a
        · simpa [hq] using hE a hq
        · simp [FinProb.pr, hq, hε]
      exact mul_le_mul_of_nonneg_left htail (μ.nonneg a)
    _ = (∑ a, μ.w a) * ε := (Finset.sum_mul _ _ _).symm
    _ = ε := by rw [μ.sum_eq_one]; ring

private theorem finProb_pi_expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → FinProb Bool) (f : ι → Bool → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).expect (f i) := by
  classical
  unfold FinProb.expect FinProb.pi
  calc
    _ = ∑ ω : (∀ i, Bool), ∏ i, (P i).w (ω i) * f i (ω i) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, (P i).w b * f i b := by rw [Fintype.prod_sum]
    _ = _ := rfl

private theorem bernoulli_all_false_subset_probability {ι : Type*} [Fintype ι]
    [DecidableEq ι] (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset ι) :
    (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr
      (fun A => ∀ i ∈ S, A i = false) ≤ Real.exp (-q * (S.card : ℝ)) := by
  classical
  let μ : FinProb (∀ _ : ι, Bool) := FinProb.pi (fun _ : ι => FinProb.bernoulli q)
  let E : (∀ _ : ι, Bool) → Prop := fun A => ∀ i ∈ S, A i = false
  let f : ι → Bool → ℝ := fun i b => if i ∈ S then if b = false then 1 else 0 else 1
  have hindicator (A : ∀ _ : ι, Bool) : (if E A then (1 : ℝ) else 0) = ∏ i, f i (A i) := by
    by_cases hA : E A
    · rw [if_pos hA]
      have hprod : ∏ i, f i (A i) = 1 := by
        rw [Finset.prod_ite_mem_eq S]
        apply Finset.prod_eq_one
        intro i hi
        simp [f, hA i hi]
      rw [hprod]
    · have hex : ∃ i, i ∈ S ∧ A i = true := by
        by_contra hnot
        push_neg at hnot
        apply hA
        intro i hi
        cases hval : A i <;> simp_all
      rcases hex with ⟨i, hi, hval⟩
      have hz : f i (A i) = 0 := by simp [f, hi, hval]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hz]
      simp [E, hA]
  have hcoord (i : ι) :
      (FinProb.bernoulli q).expect (fun b => f i b) = if i ∈ S then 1 - q else 1 := by
    by_cases hi : i ∈ S
    · simp [f, hi, FinProb.expect, FinProb.bernoulli, hq0, hq1]
    · simp [f, hi, FinProb.expect, FinProb.bernoulli, hq0, hq1]
  have hfactor : μ.pr E = ∏ i, if i ∈ S then 1 - q else 1 := by
    calc
      μ.pr E = μ.expect (fun A => if E A then (1 : ℝ) else 0) := by
        unfold FinProb.pr FinProb.expect
        apply Finset.sum_congr rfl
        intro A hA
        by_cases h : E A <;> simp [h]
      _ = μ.expect (fun A => ∏ i, f i (A i)) := by
        congr 1
        funext A
        exact hindicator A
      _ = ∏ i, (FinProb.bernoulli q).expect (fun b => f i b) := by
        simpa [μ] using
          (finProb_pi_expect_prod (fun _ : ι => FinProb.bernoulli q) f)
      _ = ∏ i, if i ∈ S then 1 - q else 1 := by simp_rw [hcoord]
  have hprod_le : (∏ i, if i ∈ S then 1 - q else 1) ≤
      ∏ i, if i ∈ S then Real.exp (-q) else 1 := by
    apply Finset.prod_le_prod₀
    · intro i hi
      by_cases his : i ∈ S
      · simp only [if_pos his]
        linarith
      · simp [his]
    · intro i hi
      by_cases his : i ∈ S
      · simp only [if_pos his]
        exact Real.one_sub_le_exp_neg q
      · simp [his]
  have hexp_prod : (∏ i, if i ∈ S then Real.exp (-q) else 1) =
      Real.exp (-q * (S.card : ℝ)) := by
    rw [Finset.prod_ite_mem_eq S (fun _ => Real.exp (-q))]
    rw [← Real.exp_sum]
    congr 1
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    μ.pr E = ∏ i, if i ∈ S then 1 - q else 1 := hfactor
    _ ≤ ∏ i, if i ∈ S then Real.exp (-q) else 1 := hprod_le
    _ = Real.exp (-q * (S.card : ℝ)) := hexp_prod

theorem height_hole_probability_bound (C : Finset (Pos9 P hc n)) (s : ℝ)
    (hs : 0 ≤ s) (v : CubeVertex n) (j : Fin (hc.levels n + 1))
    (hq0 : 0 ≤ (n : ℝ) ^ (hc.b₀ - 10))
    (hq1 : (n : ℝ) ^ (hc.b₀ - 10) ≤ 1)
    (hqpow : (n : ℝ) ^ (hc.b₀ - 10) * (n : ℝ) ^ (10 : ℝ) =
      (n : ℝ) ^ hc.b₀) :
    (heightLaw9 P hc n).pr (fun ω =>
      holeIn9 C ω.1 ω.2 v j ∧
        s * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 C ω.1 v j : ℝ)) ≤
      Real.exp (-s * (n : ℝ) ^ hc.b₀) := by
  classical
  let q : ℝ := (n : ℝ) ^ (hc.b₀ - 10)
  let Q : (Pos9 P hc n → Bool) → Prop := fun Pp =>
    s * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 C Pp v j : ℝ)
  let Hole : (Pos9 P hc n → Bool) → (Pos9 P hc n → Bool) → Prop :=
    fun Pp A => holeIn9 C Pp A v j
  have hActivation (Pp : Pos9 P hc n → Bool) (hQ : Q Pp) :
      (heightActLaw9 P hc n).pr (Hole Pp) ≤ Real.exp (-s * (n : ℝ) ^ hc.b₀) := by
    let S : Finset (Pos9 P hc n) := C.filter fun c =>
      Pp c = true ∧ c.slice = specialWord9 (P.m n) v ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n ∧ c.level = j
    have hScard : (S.card : ℝ) = eligCount9 C Pp v j := by
      simp [S, eligCount9]
    have hSize : s * (n : ℝ) ^ (10 : ℝ) ≤ (S.card : ℝ) := by
      simpa [Q, hScard] using hQ
    have hholeSubset (A : Pos9 P hc n → Bool) (hHole : Hole Pp A) :
        ∀ c ∈ S, A c = false := by
      intro c hcS
      rcases Finset.mem_filter.mp hcS with ⟨hcC, ⟨hPpc, hslice, hdist, hlevel⟩⟩
      have hnotActive := hHole c hcC hslice hdist hlevel
      cases hA : A c
      · rfl
      · exfalso
        apply hnotActive
        exact ⟨hPpc, hA⟩
    have hnoActive := bernoulli_all_false_subset_probability q hq0 hq1 S
    have hnoActive' : (heightActLaw9 P hc n).pr (fun A => ∀ c ∈ S, A c = false) ≤
        Real.exp (-q * (S.card : ℝ)) := by
      simpa [heightActLaw9, q] using hnoActive
    have hmono := finProb_pr_mono (heightActLaw9 P hc n) (Hole Pp)
      (fun A => ∀ c ∈ S, A c = false) hholeSubset
    have hqCard : s * (n : ℝ) ^ hc.b₀ ≤ q * (S.card : ℝ) := by
      calc
        s * (n : ℝ) ^ hc.b₀ = s * (q * (n : ℝ) ^ (10 : ℝ)) := by
          rw [show q = (n : ℝ) ^ (hc.b₀ - 10) by rfl, hqpow]
        _ = q * (s * (n : ℝ) ^ (10 : ℝ)) := by ring
        _ ≤ q * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_left hSize hq0
    have hexp : Real.exp (-q * (S.card : ℝ)) ≤ Real.exp (-s * (n : ℝ) ^ hc.b₀) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hqCard]
    calc
      (heightActLaw9 P hc n).pr (Hole Pp) ≤
          (heightActLaw9 P hc n).pr (fun A => ∀ c ∈ S, A c = false) := hmono
      _ ≤ Real.exp (-q * (S.card : ℝ)) := hnoActive'
      _ ≤ Real.exp (-s * (n : ℝ) ^ hc.b₀) := hexp
  have hprod := finProb_prod_pr_dep_bound (heightPosLaw9 P hc n)
    (heightActLaw9 P hc n) Q Hole (Real.exp (-s * (n : ℝ) ^ hc.b₀))
    (Real.exp_nonneg _) hActivation
  simpa [heightLaw9, Q, Hole, and_comm] using hprod

private theorem finProb_prod_expect {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinProb α) (ν : FinProb β) (f : α → β → ℝ) :
    (FinProb.prod μ ν).expect (fun ab => f ab.1 ab.2) =
      μ.expect (fun a => ν.expect (f a)) := by
  unfold FinProb.expect FinProb.prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem finProb_expect_congr {α : Type*} [Fintype α] (μ : FinProb α)
    {f g : α → ℝ} (h : ∀ x, f x = g x) : μ.expect f = μ.expect g := by
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro x hx
  rw [h x]

private lemma finProb_pr_exp_markov9 {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    (X : Ω → ℝ) (s t : ℝ) (hs : 0 ≤ s) :
    μ.pr (fun ω => t ≤ X ω) ≤
      Real.exp (-s * t) * μ.expect (fun ω => Real.exp (s * X ω)) := by
  classical
  unfold FinProb.pr FinProb.expect
  calc
    (∑ ω, if t ≤ X ω then μ.w ω else 0) ≤
        ∑ ω, μ.w ω * Real.exp (s * (X ω - t)) := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases h : t ≤ X ω
      · have he : 1 ≤ Real.exp (s * (X ω - t)) := by
          apply Real.one_le_exp_iff.mpr
          exact mul_nonneg hs (sub_nonneg.mpr h)
        simp only [if_pos h]
        simpa using (mul_le_mul_of_nonneg_left he (μ.nonneg ω))
      · simp only [if_neg h]
        exact mul_nonneg (μ.nonneg ω) (Real.exp_nonneg _)
    _ = Real.exp (-s * t) * ∑ ω, μ.w ω * Real.exp (s * X ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [show s * (X ω - t) = -s * t + s * X ω by ring, Real.exp_add]
      ring

private theorem exp_third_le_three_halves9 : Real.exp (1 / 3 : ℝ) ≤ 3 / 2 := by
  have hlog := Real.log_le_sub_one_of_pos
    (x := ((3 : ℝ) / 2)⁻¹) (inv_pos.mpr (by norm_num))
  rw [Real.log_inv] at hlog
  have hlog' : 1 / 3 ≤ Real.log ((3 : ℝ) / 2) := by
    norm_num at hlog ⊢
    linarith
  calc
    Real.exp (1 / 3 : ℝ) ≤ Real.exp (Real.log ((3 : ℝ) / 2)) :=
      Real.exp_le_exp.mpr hlog'
    _ = 3 / 2 := Real.exp_log (by norm_num)

/-- Exponential moment for the number of active positions in a fixed finite set. -/
theorem height_active_exp_mgf_bound (S : Finset (Pos9 P hc n)) (p q s : ℝ)
    (hpEq : p = (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ))
    (hqEq : q = (n : ℝ) ^ (hc.b₀ - 10))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hs : 0 ≤ s) :
    (heightLaw9 P hc n).expect (fun ω =>
      Real.exp (s * ∑ c : Pos9 P hc n,
        if c ∈ S ∧ ω.1 c = true ∧ ω.2 c = true then (1 : ℝ) else 0)) ≤
      Real.exp (p * q * (S.card : ℝ) * (Real.exp s - 1)) := by
  classical
  let X : Pos9 P hc n → (Pos9 P hc n → Bool) → Bool → ℝ :=
    fun c Pp b => if c ∈ S ∧ Pp c = true ∧ b = true then 1 else 0
  have hactCoord (Pp : Pos9 P hc n → Bool) (c : Pos9 P hc n) :
      (FinProb.bernoulli q).expect (fun b => Real.exp (s * X c Pp b)) =
        if c ∈ S ∧ Pp c = true then 1 + q * (Real.exp s - 1) else 1 := by
    by_cases h : c ∈ S ∧ Pp c = true
    · simp [X, h, FinProb.expect, FinProb.bernoulli, hq0, hq1] <;> ring
    · simp [X, h, FinProb.expect, FinProb.bernoulli, hq0, hq1]
  have hposCoord (c : Pos9 P hc n) :
      (FinProb.bernoulli p).expect (fun b =>
        if c ∈ S ∧ b = true then 1 + q * (Real.exp s - 1) else 1) =
        if c ∈ S then 1 + p * q * (Real.exp s - 1) else 1 := by
    by_cases h : c ∈ S
    · simp [h, FinProb.expect, FinProb.bernoulli, hp0, hp1] <;> ring
    · have hfun : (fun b : Bool => if c ∈ S ∧ b = true then
          1 + q * (Real.exp s - 1) else 1) = fun _ => (1 : ℝ) := by
        funext b
        simp [h]
      rw [hfun]
      rw [FinProb.expect_const]
      simp [h]
  have hfactor (Pp : Pos9 P hc n → Bool) :
      (heightActLaw9 P hc n).expect (fun A =>
        Real.exp (s * ∑ c : Pos9 P hc n, X c Pp (A c))) =
        ∏ c : Pos9 P hc n,
          if c ∈ S ∧ Pp c = true then 1 + q * (Real.exp s - 1) else 1 := by
    calc
      _ = (heightActLaw9 P hc n).expect (fun A =>
          ∏ c : Pos9 P hc n, Real.exp (s * X c Pp (A c))) := by
        congr 1
        funext A
        rw [Finset.mul_sum, Real.exp_sum]
      _ = ∏ c : Pos9 P hc n,
          (FinProb.bernoulli q).expect (fun b => Real.exp (s * X c Pp b)) := by
        simpa only [heightActLaw9, hqEq] using
          (finProb_pi_expect_prod (fun _ : Pos9 P hc n => FinProb.bernoulli q)
            (fun c b => Real.exp (s * X c Pp b)))
      _ = _ := by simp_rw [hactCoord]
  have houter :
      (heightPosLaw9 P hc n).expect (fun Pp =>
        ∏ c : Pos9 P hc n,
          if c ∈ S ∧ Pp c = true then 1 + q * (Real.exp s - 1) else 1) =
      ∏ c : Pos9 P hc n,
        if c ∈ S then 1 + p * q * (Real.exp s - 1) else 1 := by
    calc
      _ = ∏ c : Pos9 P hc n,
          (FinProb.bernoulli p).expect (fun b =>
            if c ∈ S ∧ b = true then 1 + q * (Real.exp s - 1) else 1) := by
        simpa only [heightPosLaw9, hpEq] using
          (finProb_pi_expect_prod (fun _ : Pos9 P hc n => FinProb.bernoulli p)
            (fun c b => if c ∈ S ∧ b = true then 1 + q * (Real.exp s - 1) else 1))
      _ = _ := by simp_rw [hposCoord]
  have hprodBound :
      (∏ c : Pos9 P hc n, if c ∈ S then 1 + p * q * (Real.exp s - 1) else 1) ≤
        ∏ c : Pos9 P hc n,
          Real.exp (if c ∈ S then p * q * (Real.exp s - 1) else 0) := by
    apply Finset.prod_le_prod₀
    · intro c hc
      by_cases h : c ∈ S
      · rw [if_pos h]
        have hexp : 0 ≤ Real.exp s - 1 := by
          have := Real.one_le_exp_iff.mpr hs
          linarith
        have hpq : 0 ≤ p * q := mul_nonneg hp0 hq0
        exact add_nonneg (by norm_num) (mul_nonneg hpq hexp)
      · simp [h]
    · intro c hc
      by_cases h : c ∈ S
      · simp only [if_pos h]
        have hterm : 0 ≤ p * q * (Real.exp s - 1) :=
          mul_nonneg (mul_nonneg hp0 hq0) (by
            have := Real.one_le_exp_iff.mpr hs
            linarith)
        have := Real.add_one_le_exp (p * q * (Real.exp s - 1))
        nlinarith
      · simp [h]
  have hsum :
      (∑ c : Pos9 P hc n, if c ∈ S then p * q * (Real.exp s - 1) else 0) =
        p * q * (S.card : ℝ) * (Real.exp s - 1) := by
    rw [Finset.sum_ite_mem]
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  have hprodExp :
      (∏ c : Pos9 P hc n,
        Real.exp (if c ∈ S then p * q * (Real.exp s - 1) else 0)) =
        Real.exp (p * q * (S.card : ℝ) * (Real.exp s - 1)) := by
    rw [← Real.exp_sum, hsum]
  calc
    (heightLaw9 P hc n).expect (fun ω =>
        Real.exp (s * ∑ c : Pos9 P hc n,
          if c ∈ S ∧ ω.1 c = true ∧ ω.2 c = true then (1 : ℝ) else 0)) =
        (heightPosLaw9 P hc n).expect (fun Pp =>
          (heightActLaw9 P hc n).expect (fun A =>
            Real.exp (s * ∑ c : Pos9 P hc n, X c Pp (A c)))) := by
      simpa [heightLaw9, X] using
        (finProb_prod_expect (heightPosLaw9 P hc n) (heightActLaw9 P hc n)
          (fun Pp A => Real.exp (s * ∑ c : Pos9 P hc n,
            if c ∈ S ∧ Pp c = true ∧ A c = true then (1 : ℝ) else 0)))
    _ = (heightPosLaw9 P hc n).expect (fun Pp =>
          ∏ c : Pos9 P hc n,
            if c ∈ S ∧ Pp c = true then 1 + q * (Real.exp s - 1) else 1) := by
      apply finProb_expect_congr
      intro Pp
      exact hfactor Pp
    _ = ∏ c : Pos9 P hc n,
          if c ∈ S then 1 + p * q * (Real.exp s - 1) else 1 := houter
    _ ≤ ∏ c : Pos9 P hc n,
          Real.exp (if c ∈ S then p * q * (Real.exp s - 1) else 0) := hprodBound
    _ = Real.exp (p * q * (S.card : ℝ) * (Real.exp s - 1)) := hprodExp

/-- Chernoff tail for the active positions in a fixed set when its mean is far below the threshold. -/
theorem height_active_count_tail (S : Finset (Pos9 P hc n)) (p q τ : ℝ)
    (hpEq : p = (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ))
    (hqEq : q = (n : ℝ) ^ (hc.b₀ - 10))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hτ : 0 ≤ τ) (hmean : p * q * (S.card : ℝ) ≤ τ / 6) :
    (heightLaw9 P hc n).pr (fun ω =>
      τ ≤ ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ)) ≤
      Real.exp (-τ / 4) := by
  classical
  let X : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool) → ℝ := fun ω =>
    ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ)
  have hcard (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) :
      X ω = ∑ c : Pos9 P hc n,
        if c ∈ S ∧ ω.1 c = true ∧ ω.2 c = true then (1 : ℝ) else 0 := by
    dsimp [X]
    rw [Finset.card_eq_sum_ite
      (s := S.filter (fun c => ω.1 c = true ∧ ω.2 c = true))
      (t := Finset.univ) (Finset.subset_univ _)]
    push_cast
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hmgfRaw := height_active_exp_mgf_bound S p q (1 / 3) hpEq hqEq
    hp0 hp1 hq0 hq1 (by norm_num)
  have hmgf : (heightLaw9 P hc n).expect
      (fun ω => Real.exp ((1 / 3 : ℝ) * X ω)) ≤
        Real.exp (p * q * (S.card : ℝ) * (Real.exp (1 / 3 : ℝ) - 1)) := by
    simpa [X, hcard] using hmgfRaw
  have hmark := finProb_pr_exp_markov9 (heightLaw9 P hc n) X (1 / 3) τ (by norm_num)
  have hfactor :
      Real.exp (-(1 / 3 : ℝ) * τ) *
        (heightLaw9 P hc n).expect (fun ω => Real.exp ((1 / 3 : ℝ) * X ω)) ≤
      Real.exp (-τ / 4) := by
    calc
      _ ≤ Real.exp (-(1 / 3 : ℝ) * τ) *
          Real.exp (p * q * (S.card : ℝ) * (Real.exp (1 / 3 : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ ≤ Real.exp (-τ / 4) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hthird : Real.exp (1 / 3 : ℝ) - 1 ≤ 1 / 2 := by
          have := exp_third_le_three_halves9
          linarith
        have hcoef :
            p * q * (S.card : ℝ) * (Real.exp (1 / 3 : ℝ) - 1) ≤ τ / 12 := by
          have hnonneg : 0 ≤ p * q * (S.card : ℝ) := by positivity
          calc
            _ ≤ p * q * (S.card : ℝ) * (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_left hthird hnonneg
            _ ≤ τ / 12 := by nlinarith [hmean]
        nlinarith [hcoef]
  have htailX : (heightLaw9 P hc n).pr (fun ω => τ ≤ X ω) ≤
        Real.exp (-(1 / 3 : ℝ) * τ) *
          (heightLaw9 P hc n).expect (fun ω => Real.exp ((1 / 3 : ℝ) * X ω)) := hmark
  have htailX' : (heightLaw9 P hc n).pr (fun ω => τ ≤ X ω) ≤ Real.exp (-τ / 4) :=
    htailX.trans hfactor
  simpa [X] using htailX'

private def heightDiffSet9 {d : ℕ} (v u : CubeVertex d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => u i ≠ v i)

private def heightVertexOfDiff9 {d : ℕ} (v : CubeVertex d) (s : Finset (Fin d)) :
    CubeVertex d := fun i => if i ∈ s then !(v i) else v i

private def heightDiffEquiv9 {d : ℕ} (v : CubeVertex d) : CubeVertex d ≃ Finset (Fin d) where
  toFun := heightDiffSet9 v
  invFun := heightVertexOfDiff9 v
  left_inv := by
    intro u
    funext i
    by_cases hi : u i = v i
    · simp [heightVertexOfDiff9, heightDiffSet9, hi]
    · have hmem : i ∈ heightDiffSet9 v u := by simp [heightDiffSet9, hi]
      have hbool : v i = !(u i) := by cases hu : u i <;> cases hv : v i <;> simp_all
      simp [heightVertexOfDiff9, hmem, hbool]
  right_inv := by
    intro s
    ext i
    by_cases hi : i ∈ s
    · simp [heightDiffSet9, heightVertexOfDiff9, hi]
    · simp [heightDiffSet9, heightVertexOfDiff9, hi]

private theorem heightDiffSet_card9 {d : ℕ} (v u : CubeVertex d) :
    (heightDiffSet9 v u).card = _root_.hammingDist u v := by
  simp [heightDiffSet9, _root_.hammingDist, ne_comm]

private theorem heightDiffSet_symmDiff9 {d : ℕ} (x y u : CubeVertex d) :
    heightDiffSet9 y u = heightDiffSet9 x u ∆ heightDiffSet9 x y := by
  ext i
  simp only [heightDiffSet9, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_symmDiff]
  cases x i <;> cases y i <;> cases u i <;> simp

private theorem height_card_symmDiff9 {α : Type*} [DecidableEq α]
    (A B : Finset α) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hdisj : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp hxA).2 (Finset.mem_sdiff.mp hxB).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisj]
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  have hcomm : (B ∩ A).card = (A ∩ B).card := by rw [Finset.inter_comm]
  omega

private theorem height_hamming_sphere_card9 {d : ℕ} (r : ℕ) (x : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u x = r)).card =
      Nat.choose d r := by
  classical
  let S : Finset (Finset (Fin d)) := Finset.univ.powersetCard r
  have hcard :
      (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u x = r)).card = S.card := by
    apply Finset.card_bij (fun u _ => heightDiffSet9 x u)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      have hcard' := heightDiffSet_card9 x u
      rw [hcard']
      exact hu
    · intro u hu v hv huv
      exact (heightDiffEquiv9 x).injective huv
    · intro s hs
      have hsCard := (Finset.mem_powersetCard.mp hs).2
      have hdiff : heightDiffSet9 x (heightVertexOfDiff9 x s) = s :=
        (heightDiffEquiv9 x).right_inv s
      refine ⟨heightVertexOfDiff9 x s,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hdiff⟩
      have hdistEq := (heightDiffSet_card9 x (heightVertexOfDiff9 x s)).symm
      rw [hdiff] at hdistEq
      exact hdistEq.trans hsCard
  calc
    _ = S.card := hcard
    _ = Nat.choose d r := by simp [S, Finset.card_powersetCard]

theorem height_binomial_ball_power_bound9 (m n s : ℕ)
    (hm : m ≤ n) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (s + 1), (Nat.choose m i : ℝ)) ≤
      ((s + 1 : ℕ) : ℝ) * (n : ℝ) ^ s := by
  have hmR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    (∑ i ∈ Finset.range (s + 1), (Nat.choose m i : ℝ)) ≤
        ∑ _i ∈ Finset.range (s + 1), (n : ℝ) ^ s := by
      apply Finset.sum_le_sum
      intro i hi
      have his : i ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hchoose : (Nat.choose m i : ℝ) ≤ (m : ℝ) ^ i := by
        exact_mod_cast Nat.choose_le_pow m i
      have hbase : (m : ℝ) ^ i ≤ (n : ℝ) ^ i := by gcongr
      have hexp : (n : ℝ) ^ i ≤ (n : ℝ) ^ s := by gcongr
      exact hchoose.trans (hbase.trans hexp)
    _ = ((s + 1 : ℕ) : ℝ) * (n : ℝ) ^ s := by simp

private def heightBallEquiv9 {d r : ℕ} (v : CubeVertex d) :
    {u : CubeVertex d // _root_.hammingDist u v ≤ r} ≃
      {s : Finset (Fin d) // s.card ≤ r} where
  toFun u := ⟨heightDiffSet9 v u.1, by rw [heightDiffSet_card9]; exact u.2⟩
  invFun s := ⟨heightVertexOfDiff9 v s.1, by
    rw [← heightDiffSet_card9]
    simp [heightDiffSet9, heightVertexOfDiff9]
    exact s.2⟩
  left_inv := by intro u; apply Subtype.ext; exact (heightDiffEquiv9 v).left_inv u.1
  right_inv := by intro s; apply Subtype.ext; exact (heightDiffEquiv9 v).right_inv s.1

private def heightSmallSubsetFiberEquiv9 (d r : ℕ) (i : Fin (r + 1)) :
    {s : {s : Finset (Fin d) // s.card ≤ r} // (⟨s.1.card, by omega⟩ : Fin (r + 1)) = i} ≃
      {s : Finset (Fin d) // s.card = i.val} where
  toFun s := ⟨s.1.1, by
    have h := congrArg Fin.val s.2
    simpa using h⟩
  invFun s := ⟨⟨s.1, by rw [s.2]; omega⟩, by
    apply Fin.ext
    exact s.2⟩
  left_inv := by
    intro s
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    apply Subtype.ext
    rfl

private def heightSmallSubsetsEquiv9 (d r : ℕ) :
    {s : Finset (Fin d) // s.card ≤ r} ≃
      Σ i : Fin (r + 1), {s : Finset (Fin d) // s.card = i.val} := by
  let f : {s : Finset (Fin d) // s.card ≤ r} → Fin (r + 1) :=
    fun s => ⟨s.1.card, by omega⟩
  exact (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight (heightSmallSubsetFiberEquiv9 d r))

private theorem heightSmallSubsetsCard9 (d r : ℕ) :
    Fintype.card {s : Finset (Fin d) // s.card ≤ r} =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  rw [Fintype.card_congr (heightSmallSubsetsEquiv9 d r), Fintype.card_sigma]
  have hfiber (i : Fin (r + 1)) :
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Nat.choose d i.val := by
    let S : Finset (Finset (Fin d)) := Finset.univ.powersetCard i.val
    let e : {s : Finset (Fin d) // s.card = i.val} ≃ S :=
      { toFun := fun s => ⟨s.1, by
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, s.2⟩⟩
        invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
        left_inv := by intro s; apply Subtype.ext; rfl
        right_inv := by intro s; apply Subtype.ext; rfl }
    calc
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Fintype.card S := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose d i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

theorem height_hamming_ball_card9 (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  have hcard : Fintype.card {u : CubeVertex d // _root_.hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubeVertex d => _root_.hammingDist u v ≤ r))
  exact hcard.symm.trans
    ((Fintype.card_congr (heightBallEquiv9 v)).trans (heightSmallSubsetsCard9 d r))

private theorem height_choose_sum_shift9 (d r : ℕ) :
    (∑ i ∈ Finset.range r, Nat.choose d (i + 1)) + Nat.choose d 0 =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ]
      have hright : r + 1 + 1 = (r + 1) + 1 := by omega
      rw [hright, Finset.sum_range_succ]
      nlinarith [ih]

theorem height_hamming_ball_prev_volume_bound9 (d r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d) :
    (∑ i ∈ Finset.range r, Nat.choose d i) * (d - r + 1) ≤
      r * (∑ i ∈ Finset.range (r + 1), Nat.choose d i) := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range r) :
      Nat.choose d i * (d - r + 1) ≤ Nat.choose d (i + 1) * r := by
    have hir : i < r := Finset.mem_range.mp hi
    have hid : i ≤ d := le_trans (Nat.le_of_lt hir) hrd
    have hrec := Nat.choose_succ_right_eq d i
    have hleft : Nat.choose d i * (d - r + 1) ≤ Nat.choose d i * (d - i) := by
      exact Nat.mul_le_mul_left _ (by omega)
    have hright : Nat.choose d (i + 1) * (i + 1) ≤ Nat.choose d (i + 1) * r :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hsum :
      (∑ i ∈ Finset.range r, Nat.choose d i) * (d - r + 1) ≤
        (∑ i ∈ Finset.range r, Nat.choose d (i + 1)) * r := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i ∈ Finset.range r, Nat.choose d (i + 1) * r := by
        apply Finset.sum_le_sum
        intro i hi
        exact hterm i hi
      _ = (∑ i ∈ Finset.range r, Nat.choose d (i + 1)) * r := by rw [Finset.sum_mul]
  have hshift := height_choose_sum_shift9 d r
  have hshift' :
      (∑ i ∈ Finset.range r, Nat.choose d (i + 1)) + 1 =
        ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by simpa using hshift
  have hshiftLe :
      ∑ i ∈ Finset.range r, Nat.choose d (i + 1) ≤
        ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
    omega
  exact (hsum.trans (Nat.mul_le_mul_right r hshiftLe)).trans_eq (by simp [Nat.mul_comm])

theorem height_hamming_ball_next_volume_bound9 (d r : ℕ) :
    (∑ i ∈ Finset.range (r + 2), Nat.choose d i) * (r + 1) ≤
      (∑ i ∈ Finset.range (r + 1), Nat.choose d i) * (r + 1 + d) := by
  have hVplus :
      (∑ i ∈ Finset.range (r + 2), Nat.choose d i) =
        (∑ i ∈ Finset.range (r + 1), Nat.choose d i) + Nat.choose d (r + 1) := by
    have hindex : r + 2 = (r + 1) + 1 := by omega
    rw [hindex, Finset.sum_range_succ]
  have hrec := Nat.choose_succ_right_eq d r
  have hchooseLe : Nat.choose d r ≤ ∑ i ∈ Finset.range (r + 1), Nat.choose d i :=
    Finset.single_le_sum (fun i hi => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self r))
  rw [hVplus]
  calc
    _ = (∑ i ∈ Finset.range (r + 1), Nat.choose d i) * (r + 1) +
        Nat.choose d (r + 1) * (r + 1) := by rw [Nat.add_mul]
    _ = (∑ i ∈ Finset.range (r + 1), Nat.choose d i) * (r + 1) +
        Nat.choose d r * (d - r) := by rw [hrec]
    _ ≤ (∑ i ∈ Finset.range (r + 1), Nat.choose d i) * (r + 1) +
        (∑ i ∈ Finset.range (r + 1), Nat.choose d i) * d := by
      apply Nat.add_le_add_left
      calc
        Nat.choose d r * (d - r) ≤
            (∑ i ∈ Finset.range (r + 1), Nat.choose d i) * (d - r) :=
          Nat.mul_le_mul_right _ hchooseLe
        _ ≤ (∑ i ∈ Finset.range (r + 1), Nat.choose d i) * d :=
          Nat.mul_le_mul_left _ (by omega)
    _ = (∑ i ∈ Finset.range (r + 1), Nat.choose d i) * (r + 1 + d) := by
      ring

theorem height_slice_ball_card9 (slice : CubeVertex (P.m n))
    (x : CubeVertex (n - P.m n)) (j : Fin (hc.levels n + 1)) (R : ℕ) :
    (Finset.univ.filter (fun c : Pos9 P hc n =>
      c.slice = slice ∧ _root_.hammingDist c.location x ≤ R ∧ c.level = j)).card =
      ∑ i ∈ Finset.range (R + 1), Nat.choose (n - P.m n) i := by
  classical
  let S : Finset (Pos9 P hc n) := Finset.univ.filter (fun c =>
    c.slice = slice ∧ _root_.hammingDist c.location x ≤ R ∧ c.level = j)
  let B : Finset (CubeVertex (n - P.m n)) :=
    Finset.univ.filter (fun u => _root_.hammingDist u x ≤ R)
  have hcard : S.card = B.card := by
    apply Finset.card_bij (fun c _ => c.location)
    · intro c hcS
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hcS
      rcases hcS with ⟨_, hd, _⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
    · intro c hcS d hdS heq
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hcS hdS
      rcases hcS with ⟨hcs, _, hcj⟩
      rcases hdS with ⟨hds, _, hdj⟩
      cases c with
      | mk sc lc jc =>
        cases d with
        | mk sd ld jd =>
          simp_all
    · intro u huB
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at huB
      refine ⟨⟨slice, u, j⟩, ?_, rfl⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨huB, trivial⟩
  calc
    _ = S.card := by rfl
    _ = B.card := hcard
    _ = ∑ i ∈ Finset.range (R + 1), Nat.choose (n - P.m n) i := by
      exact height_hamming_ball_card9 (n - P.m n) R x

theorem height_adjacent_ball_card_le9 (slice : CubeVertex (P.m n))
    (x : CubeVertex (n - P.m n)) (j : Fin (hc.levels n + 1)) (R : ℕ) :
    (Finset.univ.filter (fun c : Pos9 P hc n =>
      _root_.hammingDist c.slice slice = 1 ∧
        _root_.hammingDist c.location x ≤ R ∧ c.level = j)).card ≤
      P.m n * (∑ i ∈ Finset.range (R + 1), Nat.choose (n - P.m n) i) := by
  classical
  let S : Finset (Pos9 P hc n) := Finset.univ.filter (fun c =>
    _root_.hammingDist c.slice slice = 1 ∧
      _root_.hammingDist c.location x ≤ R ∧ c.level = j)
  let T : Finset (CubeVertex (P.m n)) :=
    Finset.univ.filter fun z => (cube (P.m n)).Adj slice z
  let B : Finset (CubeVertex (n - P.m n)) :=
    Finset.univ.filter (fun u => _root_.hammingDist u x ≤ R)
  let f : Pos9 P hc n → CubeVertex (P.m n) × CubeVertex (n - P.m n) :=
    fun c => (c.slice, c.location)
  have hT : T.card ≤ P.m n := cube_adj_neighbors_card_le (P.m n) slice
  have hmap : ∀ c, c ∈ S → f c ∈ T ×ˢ B := by
    intro c hcS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hcS
    rcases hcS with ⟨hslice, hloc, hlevel⟩
    rw [Finset.mem_product]
    constructor
    · change c.slice ∈ Finset.univ.filter (fun z : CubeVertex (P.m n) =>
        (cube (P.m n)).Adj slice z)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [OAI.HypercubeRamsey.cube, _root_.hammingDist_comm] using hslice
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hloc⟩
  have hinj : Set.InjOn f S := by
    intro c hcS d hdS hfd
    change c ∈ S at hcS
    change d ∈ S at hdS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hcS hdS
    rcases hcS with ⟨_, _, hcj⟩
    rcases hdS with ⟨_, _, hdj⟩
    have hsl : c.slice = d.slice := by simpa [f] using congrArg Prod.fst hfd
    have hloc : c.location = d.location := by simpa [f] using congrArg Prod.snd hfd
    cases c with
    | mk sc lc jc =>
      cases d with
      | mk sd ld jd =>
        simp_all
  have himage : S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
  have himageSub : S.image f ⊆ T ×ˢ B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨c, hc, rfl⟩
    exact hmap c hc
  have hB : B.card = ∑ i ∈ Finset.range (R + 1), Nat.choose (n - P.m n) i :=
    height_hamming_ball_card9 (n - P.m n) R x
  calc
    S.card = (S.image f).card := himage
    _ ≤ (T ×ˢ B).card := Finset.card_le_card himageSub
    _ = T.card * B.card := by rw [Finset.card_product]
    _ ≤ P.m n * B.card := Nat.mul_le_mul_right _ hT
    _ = P.m n * (∑ i ∈ Finset.range (R + 1), Nat.choose (n - P.m n) i) := by rw [hB]

private noncomputable def heightBallVolReal9 (d r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1), (Nat.choose d i : ℝ)

theorem height_rpow_eventually_ge9 (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, K ≤ (n : ℝ) ^ δ := by
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hT K)
  exact ⟨n₀, hn₀⟩

theorem height_base_volume_ratio_bounds9 (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      0 < (residualBall9 P n : ℝ) ∧
      heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
          (residualBall9 P n : ℝ) ≤ 2 * (P.radius n : ℝ) / (n : ℝ) ∧
      heightBallVolReal9 (n - P.m n) (P.radius n + 1) /
          (residualBall9 P n : ℝ) ≤ 2 * (n : ℝ) ^ (1 - (P.σ : ℝ)) := by
  obtain ⟨nGeom, hGeom⟩ := height_base_small_scales9 P hP
  obtain ⟨nVol, hVol⟩ := height_counts9_volume_bounds P hP
  refine ⟨max nGeom nVol, ?_⟩
  intro n hn
  have hnGeom : nGeom ≤ n := le_trans (le_max_left _ _) hn
  have hnVol : nVol ≤ n := le_trans (le_max_right _ _) hn
  have hsmall := hGeom n hnGeom
  have hvolume := hVol n hnVol
  have hn1 : 1 ≤ n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnreal1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hmquarter : (P.m n : ℝ) ≤ (n : ℝ) / 4 := hsmall.1
  have hrquarter : (P.radius n : ℝ) ≤ (n : ℝ) / 4 := hsmall.2.1
  have hr11 : 11 ≤ P.radius n := hsmall.2.2
  have hrpos : 1 ≤ P.radius n := by omega
  have hrd : P.radius n ≤ n - P.m n := hvolume.2.1
  have hmle : P.m n ≤ n := by
    have h : (P.m n : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast h
  have hdcast : ((n - P.m n : ℕ) : ℝ) = (n : ℝ) - (P.m n : ℝ) :=
    Nat.cast_sub hmle
  have hden : (n : ℝ) / 2 ≤ ((n - P.m n - P.radius n + 1 : ℕ) : ℝ) := by
    have hcastSub : ((n - P.m n - P.radius n : ℕ) : ℝ) =
        (n : ℝ) - (P.m n : ℝ) - (P.radius n : ℝ) := by
      rw [Nat.cast_sub hrd, hdcast]
    rw [Nat.cast_add, hcastSub]
    nlinarith
  have hdenpos : 0 < ((n - P.m n - P.radius n + 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le (by positivity) hden
  have hVpos : 0 < (residualBall9 P n : ℝ) := by exact_mod_cast hvolume.1
  have hprevNat := height_hamming_ball_prev_volume_bound9
    (n - P.m n) (P.radius n) hrpos hrd
  have hrsub : P.radius n - 1 + 1 = P.radius n := Nat.sub_add_cancel hrpos
  have hprev :
      heightBallVolReal9 (n - P.m n) (P.radius n - 1) *
          ((n - P.m n - P.radius n + 1 : ℕ) : ℝ) ≤
        (P.radius n : ℝ) * (residualBall9 P n : ℝ) := by
    simpa [heightBallVolReal9, residualBall9, hrsub] using (by exact_mod_cast hprevNat)
  have hratioPrev :
      heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
          (residualBall9 P n : ℝ) ≤
        (P.radius n : ℝ) / ((n - P.m n - P.radius n + 1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ hVpos hdenpos).2
    nlinarith [hprev]
  have hrposR : 0 ≤ (P.radius n : ℝ) := Nat.cast_nonneg _
  have hratioPrev2 :
      (P.radius n : ℝ) / ((n - P.m n - P.radius n + 1 : ℕ) : ℝ) ≤
        2 * (P.radius n : ℝ) / (n : ℝ) := by
    apply (div_le_div_iff₀ hdenpos hnreal).2
    nlinarith [hden, hrposR]
  have hnextNat := height_hamming_ball_next_volume_bound9
    (n - P.m n) (P.radius n)
  have hVeq : heightBallVolReal9 (n - P.m n) (P.radius n) =
      (residualBall9 P n : ℝ) := by simp [heightBallVolReal9, residualBall9]
  have hnextReal :
      heightBallVolReal9 (n - P.m n) (P.radius n + 1) *
          ((P.radius n + 1 : ℕ) : ℝ) ≤
        (residualBall9 P n : ℝ) *
          ((P.radius n + 1 + (n - P.m n) : ℕ) : ℝ) := by
    rw [← hVeq]
    have hnextCast :
        ((∑ i ∈ Finset.range (P.radius n + 2), Nat.choose (n - P.m n) i : ℕ) : ℝ) *
            ((P.radius n + 1 : ℕ) : ℝ) ≤
          ((∑ i ∈ Finset.range (P.radius n + 1), Nat.choose (n - P.m n) i : ℕ) : ℝ) *
            ((P.radius n + 1 + (n - P.m n) : ℕ) : ℝ) := by exact_mod_cast hnextNat
    simpa [heightBallVolReal9] using hnextCast
  have hrplus : 0 < ((P.radius n + 1 : ℕ) : ℝ) := by positivity
  have hratioNext :
      heightBallVolReal9 (n - P.m n) (P.radius n + 1) /
          (residualBall9 P n : ℝ) ≤
        ((P.radius n + 1 + (n - P.m n) : ℕ) : ℝ) /
          ((P.radius n + 1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ hVpos hrplus).2
    nlinarith [hnextReal]
  have hdle : ((n - P.m n : ℕ) : ℝ) ≤ (n : ℝ) := by
    rw [hdcast]
    have : 0 ≤ (P.m n : ℝ) := Nat.cast_nonneg _
    linarith
  have hrpow : (n : ℝ) ^ (P.σ : ℝ) < ((P.radius n + 1 : ℕ) : ℝ) := by
    simpa [Params9.radius] using (Nat.lt_floor_add_one ((n : ℝ) ^ (P.σ : ℝ)))
  have hrpowpos : 0 < (n : ℝ) ^ (P.σ : ℝ) := Real.rpow_pos_of_pos hnreal _
  have hdenPow :
      ((n - P.m n : ℕ) : ℝ) / ((P.radius n + 1 : ℕ) : ℝ) ≤
        (n : ℝ) ^ (1 - (P.σ : ℝ)) := by
    calc
      _ ≤ (n : ℝ) / ((P.radius n + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hdle hrplus.le
      _ ≤ (n : ℝ) / (n : ℝ) ^ (P.σ : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hrpowpos hrpow.le
      _ = (n : ℝ) ^ (1 - (P.σ : ℝ)) := by
        calc
          (n : ℝ) / (n : ℝ) ^ (P.σ : ℝ) =
              (n : ℝ) ^ (1 : ℝ) / (n : ℝ) ^ (P.σ : ℝ) := by rw [Real.rpow_one]
          _ = (n : ℝ) ^ (1 - (P.σ : ℝ)) :=
            (Real.rpow_sub hnreal 1 (P.σ : ℝ)).symm
  have hratioNextBound :
      heightBallVolReal9 (n - P.m n) (P.radius n + 1) /
          (residualBall9 P n : ℝ) ≤ 2 * (n : ℝ) ^ (1 - (P.σ : ℝ)) := by
    have hratioEq :
        ((P.radius n + 1 + (n - P.m n) : ℕ) : ℝ) /
            ((P.radius n + 1 : ℕ) : ℝ) =
          1 + ((n - P.m n : ℕ) : ℝ) /
            ((P.radius n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add]
      field_simp [ne_of_gt hrplus]
      <;> ring
    have hσsmall : (P.σ : ℝ) < 1 := by
      rcases hP with ⟨hcommon, _, _, hσ, _, _, _⟩
      have hxS : P.xS < 1 := lt_trans hcommon.2.1 (lt_trans hcommon.2.2 (by norm_num))
      have hσq : P.σ < 1 := by linarith [hσ.2]
      exact_mod_cast hσq
    have hpow1 : 1 ≤ (n : ℝ) ^ (1 - (P.σ : ℝ)) :=
      Real.one_le_rpow hnreal1 (by linarith)
    calc
      _ ≤ 1 + ((n - P.m n : ℕ) : ℝ) /
            ((P.radius n + 1 : ℕ) : ℝ) := by rw [← hratioEq]; exact hratioNext
      _ ≤ 1 + (n : ℝ) ^ (1 - (P.σ : ℝ)) := by linarith [hdenPow]
      _ ≤ 2 * (n : ℝ) ^ (1 - (P.σ : ℝ)) := by nlinarith [hpow1]
  exact ⟨hVpos, hratioPrev.trans hratioPrev2, hratioNextBound⟩

theorem height_base_mean_slack9 (P : Params9) (hP : P.Valid)
    (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (n : ℝ) ^ hc.b₀ ≤ (n : ℝ) ^ ((P.χ : ℝ) / 2) / 18 ∧
      (n : ℝ) ^ hc.b₀ * (P.m n : ℝ) *
          heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
            (residualBall9 P n : ℝ) ≤ (n : ℝ) ^ ((P.χ : ℝ) / 2) / 18 ∧
      (n : ℝ) ^ hc.b₀ *
          heightBallVolReal9 (n - P.m n) (P.radius n + 1) /
            (residualBall9 P n : ℝ) ≤
        (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') / 18 := by
  rcases hP with ⟨hcommon, hminus, hx, hσ, hχ, hgap, hvalidCase⟩
  have hP' : P.Valid := ⟨hcommon, hminus, hx, hσ, hχ, hgap, hvalidCase⟩
  rcases hadm with ⟨_, _, _, _, _, _, _, _, _, hbε, heps, hcaseAdm⟩
  let α : ℝ := (P.χ : ℝ) / 2
  let sameGap : ℝ := α - hc.b₀
  let plusGap : ℝ := hc.eps' - hc.b₀
  let adjExponent : ℝ := match P.case with
    | .sub _ _ _ => hc.b₀
    | .lin _ _ _ _ => hc.b₀ + (P.σ : ℝ)
  let adjGap : ℝ := α - adjExponent
  have hSameGap : 0 < sameGap := by
    cases hbranch : P.case with
    | sub yS yD yM =>
        have hcase : hc.b₀ < α := by simpa [hbranch, α] using hcaseAdm
        dsimp [sameGap]
        linarith
    | lin αS αD hB yB =>
        have hcase : hc.b₀ + (P.σ : ℝ) < α := by simpa [hbranch, α] using hcaseAdm
        have hσpos : 0 < (P.σ : ℝ) := by exact_mod_cast hσ.1
        dsimp [sameGap]
        linarith
  have hPlusGap : 0 < plusGap := by dsimp [plusGap]; linarith
  have hAdjGap : 0 < adjGap := by
    cases hbranch : P.case with
    | sub yS yD yM =>
        have hcase : hc.b₀ < α := by simpa [hbranch, α] using hcaseAdm
        simpa [adjGap, adjExponent, hbranch] using (sub_pos.mpr hcase)
    | lin αS αD hB yB =>
        have hcase : hc.b₀ + (P.σ : ℝ) < α := by simpa [hbranch, α] using hcaseAdm
        simpa [adjGap, adjExponent, hbranch] using (sub_pos.mpr hcase)
  obtain ⟨nGeom, hGeom⟩ := height_base_small_scales9 P hP'
  obtain ⟨nRatio, hRatio⟩ := height_base_volume_ratio_bounds9 P hP'
  obtain ⟨nSame, hSame⟩ := height_rpow_eventually_ge9 sameGap 18 hSameGap (by norm_num)
  obtain ⟨nAdj, hAdj⟩ := height_rpow_eventually_ge9 adjGap 36 hAdjGap (by norm_num)
  obtain ⟨nPlus, hPlus⟩ := height_rpow_eventually_ge9 plusGap 36 hPlusGap (by norm_num)
  refine ⟨max nGeom (max nRatio (max nSame (max nAdj nPlus))), ?_⟩
  intro n hn
  have hnGeom : nGeom ≤ n := le_trans (le_max_left _ _) hn
  have hnRest : max nRatio (max nSame (max nAdj nPlus)) ≤ n :=
    le_trans (le_max_right _ _) hn
  have hnRatio : nRatio ≤ n := le_trans (le_max_left _ _) hnRest
  have hnRest2 : max nSame (max nAdj nPlus) ≤ n := le_trans (le_max_right _ _) hnRest
  have hnSame : nSame ≤ n := le_trans (le_max_left _ _) hnRest2
  have hnRest3 : max nAdj nPlus ≤ n := le_trans (le_max_right _ _) hnRest2
  have hnAdj : nAdj ≤ n := le_trans (le_max_left _ _) hnRest3
  have hnPlus : nPlus ≤ n := le_trans (le_max_right _ _) hnRest3
  have hsmall := hGeom n hnGeom
  have hratios := hRatio n hnRatio
  have hradiusReal : (11 : ℝ) ≤ (P.radius n : ℝ) := by exact_mod_cast hsmall.2.2
  have hn44Real : 44 ≤ (n : ℝ) := by nlinarith [hsmall.2.1, hradiusReal]
  have hn44 : 44 ≤ n := by exact_mod_cast hn44Real
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnreal1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hSameLarge := hSame n hnSame
  have hAdjLarge := hAdj n hnAdj
  have hPlusLarge := hPlus n hnPlus
  have hpowSame : (n : ℝ) ^ α = (n : ℝ) ^ hc.b₀ * (n : ℝ) ^ sameGap := by
    calc
      _ = (n : ℝ) ^ (hc.b₀ + sameGap) := by congr 1; dsimp [sameGap]; ring
      _ = _ := Real.rpow_add hnreal hc.b₀ sameGap
  have hpowAdj : (n : ℝ) ^ α = (n : ℝ) ^ adjExponent * (n : ℝ) ^ adjGap := by
    calc
      _ = (n : ℝ) ^ (adjExponent + adjGap) := by congr 1; dsimp [adjGap]; ring
      _ = _ := Real.rpow_add hnreal adjExponent adjGap
  have hpowPlus :
      (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') =
        (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.b₀) * (n : ℝ) ^ plusGap := by
    calc
      _ = (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.b₀ + plusGap) := by
        congr 1
        dsimp [plusGap]
        ring
      _ = _ := Real.rpow_add hnreal _ plusGap
  have hnbase : 0 ≤ (n : ℝ) ^ hc.b₀ := Real.rpow_nonneg hnreal.le _
  have hSamePowBound : 18 * (n : ℝ) ^ hc.b₀ ≤ (n : ℝ) ^ α := by
    rw [hpowSame]
    have hmul := mul_le_mul_of_nonneg_left hSameLarge hnbase
    nlinarith [hmul]
  have hSameMean : (n : ℝ) ^ hc.b₀ ≤ (n : ℝ) ^ α / 18 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 18)).2
    nlinarith [hSamePowBound]
  have hAdjPowBound :
      36 * (n : ℝ) ^ adjExponent ≤ (n : ℝ) ^ α := by
    rw [hpowAdj]
    have hmul := mul_le_mul_of_nonneg_left hAdjLarge
      (Real.rpow_nonneg hnreal.le adjExponent)
    nlinarith [hmul]
  have hPlusPowBound :
      36 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.b₀) ≤
        (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') := by
    rw [hpowPlus]
    have hmul := mul_le_mul_of_nonneg_left hPlusLarge
      (Real.rpow_nonneg hnreal.le (1 - (P.σ : ℝ) + hc.b₀))
    nlinarith [hmul]
  have hAdjacentRatio :
      (P.m n : ℝ) * heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
        (residualBall9 P n : ℝ) ≤
        (match P.case with
         | .sub _ _ _ => (2 : ℝ)
         | .lin _ _ _ _ => (n : ℝ) ^ (P.σ : ℝ) / 2) := by
    cases hbranch : P.case with
    | sub yS yD yM =>
        have hv : 0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧
            1 - P.σ < yD ∧ yD < 1 ∧ P.χ < P.σ / 10 := by
          simpa [hbranch] using hvalidCase
        have hyq : yM + P.σ < 1 := by linarith [hv.2.2.1]
        have hy : (yM : ℝ) + (P.σ : ℝ) < 1 := by exact_mod_cast hyq
        have hmPow : (P.m n : ℝ) ≤ (n : ℝ) ^ (yM : ℝ) := by
          rw [Params9.m, hbranch]
          exact Nat.floor_le (by positivity)
        have hrPow : (P.radius n : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) :=
          Nat.floor_le (by positivity)
        have hdiv : 2 * (P.radius n : ℝ) / (n : ℝ) ≤
            2 * (n : ℝ) ^ (P.σ : ℝ) / (n : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrPow (by norm_num)) hnreal.le
        have hprod : (P.m n : ℝ) * (2 * (P.radius n : ℝ) / (n : ℝ)) ≤
            (n : ℝ) ^ (yM : ℝ) * (2 * (n : ℝ) ^ (P.σ : ℝ) / (n : ℝ)) :=
          mul_le_mul hmPow hdiv (by positivity) (by positivity)
        have hbaseEq :
            (n : ℝ) ^ (yM : ℝ) *
                (2 * (n : ℝ) ^ (P.σ : ℝ) / (n : ℝ)) =
              2 * (n : ℝ) ^ ((yM : ℝ) + (P.σ : ℝ) - 1) := by
          calc
            _ = 2 * ((n : ℝ) ^ (yM : ℝ) * (n : ℝ) ^ (P.σ : ℝ)) / (n : ℝ) := by ring
            _ = 2 * (n : ℝ) ^ ((yM : ℝ) + (P.σ : ℝ)) / (n : ℝ) := by
              rw [← (Real.rpow_add hnreal (yM : ℝ) (P.σ : ℝ))]
            _ = 2 * (n : ℝ) ^ ((yM : ℝ) + (P.σ : ℝ) - 1) := by
              have hdivPow :
                  (n : ℝ) ^ ((yM : ℝ) + (P.σ : ℝ)) / (n : ℝ) =
                    (n : ℝ) ^ ((yM : ℝ) + (P.σ : ℝ) - 1) := by
                calc
                  _ = (n : ℝ) ^ ((yM : ℝ) + (P.σ : ℝ)) / (n : ℝ) ^ (1 : ℝ) := by
                    rw [Real.rpow_one]
                  _ = _ :=
                    (Real.rpow_sub hnreal ((yM : ℝ) + (P.σ : ℝ)) 1).symm
              calc
                _ = 2 * ((n : ℝ) ^ ((yM : ℝ) + (P.σ : ℝ)) / (n : ℝ)) := by ring
                _ = _ := congrArg (fun z : ℝ => 2 * z) hdivPow
        have hexpNonpos : (yM : ℝ) + (P.σ : ℝ) - 1 ≤ 0 := by linarith
        have hsmallPow := Real.rpow_le_one_of_one_le_of_nonpos hnreal1 hexpNonpos
        calc
          _ = (P.m n : ℝ) *
              (heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
                (residualBall9 P n : ℝ)) := by ring
          _ ≤ (P.m n : ℝ) * (2 * (P.radius n : ℝ) / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hratios.2.1 (Nat.cast_nonneg _)
          _ ≤ (n : ℝ) ^ (yM : ℝ) *
                (2 * (n : ℝ) ^ (P.σ : ℝ) / (n : ℝ)) := hprod
          _ = 2 * (n : ℝ) ^ ((yM : ℝ) + (P.σ : ℝ) - 1) := hbaseEq
          _ ≤ 2 := by nlinarith [hsmallPow]
    | lin αS αD hB yB =>
        have hprod : (P.m n : ℝ) * (2 * (P.radius n : ℝ) / (n : ℝ)) ≤
            ((n : ℝ) / 4) * (2 * (P.radius n : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hsmall.1 (by positivity)
        have hprodEq : ((n : ℝ) / 4) * (2 * (P.radius n : ℝ) / (n : ℝ)) =
            (P.radius n : ℝ) / 2 := by
          field_simp [ne_of_gt hnreal]
          <;> ring
        calc
          _ = (P.m n : ℝ) *
              (heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
                (residualBall9 P n : ℝ)) := by ring
          _ ≤ (P.m n : ℝ) * (2 * (P.radius n : ℝ) / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hratios.2.1 (Nat.cast_nonneg _)
          _ ≤ ((n : ℝ) / 4) * (2 * (P.radius n : ℝ) / (n : ℝ)) := hprod
          _ = (P.radius n : ℝ) / 2 := hprodEq
          _ ≤ (n : ℝ) ^ (P.σ : ℝ) / 2 := by
            exact div_le_div_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)
  have hAdjacentMean :
      (n : ℝ) ^ hc.b₀ * (P.m n : ℝ) *
          heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
            (residualBall9 P n : ℝ) ≤ (n : ℝ) ^ α / 18 := by
    cases hbranch : P.case with
    | sub yS yD yM =>
        have hratioSub :
            (P.m n : ℝ) * heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
              (residualBall9 P n : ℝ) ≤ 2 := by
          simpa [hbranch] using hAdjacentRatio
        have hAdjBound : 36 * (n : ℝ) ^ hc.b₀ ≤ (n : ℝ) ^ α := by
          simpa [adjExponent, hbranch] using hAdjPowBound
        calc
          _ = (n : ℝ) ^ hc.b₀ *
              ((P.m n : ℝ) * heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
                (residualBall9 P n : ℝ)) := by ring
          _ ≤ (n : ℝ) ^ hc.b₀ * 2 :=
            mul_le_mul_of_nonneg_left hratioSub hnbase
          _ ≤ (n : ℝ) ^ α / 18 := by nlinarith [hAdjBound]
    | lin αS αD hB yB =>
        have hratioLin :
            (P.m n : ℝ) * heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
              (residualBall9 P n : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) / 2 := by
          simpa [hbranch] using hAdjacentRatio
        have hAdjBound :
            36 * (n : ℝ) ^ (hc.b₀ + (P.σ : ℝ)) ≤ (n : ℝ) ^ α := by
          simpa [adjExponent, hbranch] using hAdjPowBound
        have hpowSigma :
            (n : ℝ) ^ hc.b₀ * (n : ℝ) ^ (P.σ : ℝ) =
              (n : ℝ) ^ (hc.b₀ + (P.σ : ℝ)) :=
          (Real.rpow_add hnreal hc.b₀ (P.σ : ℝ)).symm
        calc
          _ = (n : ℝ) ^ hc.b₀ *
              ((P.m n : ℝ) * heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
                (residualBall9 P n : ℝ)) := by ring
          _ ≤ (n : ℝ) ^ hc.b₀ * ((n : ℝ) ^ (P.σ : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hratioLin hnbase
          _ = ((n : ℝ) ^ hc.b₀ * (n : ℝ) ^ (P.σ : ℝ)) / 2 := by ring
          _ = (n : ℝ) ^ (hc.b₀ + (P.σ : ℝ)) / 2 := by rw [hpowSigma]
          _ ≤ (n : ℝ) ^ α / 18 := by nlinarith [hAdjBound]
  have hPlusMean :
      (n : ℝ) ^ hc.b₀ *
          heightBallVolReal9 (n - P.m n) (P.radius n + 1) /
            (residualBall9 P n : ℝ) ≤
        (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') / 18 := by
    have hbase :
        (n : ℝ) ^ hc.b₀ *
          heightBallVolReal9 (n - P.m n) (P.radius n + 1) /
            (residualBall9 P n : ℝ) ≤
          2 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.b₀) := by
      calc
        _ = (n : ℝ) ^ hc.b₀ *
            (heightBallVolReal9 (n - P.m n) (P.radius n + 1) /
              (residualBall9 P n : ℝ)) := by ring
        _ ≤ (n : ℝ) ^ hc.b₀ * (2 * (n : ℝ) ^ (1 - (P.σ : ℝ))) :=
          mul_le_mul_of_nonneg_left hratios.2.2 hnbase
        _ = 2 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.b₀) := by
          calc
            _ = 2 * ((n : ℝ) ^ (1 - (P.σ : ℝ)) * (n : ℝ) ^ hc.b₀) := by ring
            _ = 2 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.b₀) := by
              rw [← (Real.rpow_add hnreal (1 - (P.σ : ℝ)) hc.b₀)]
    calc
      _ ≤ 2 * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.b₀) := hbase
      _ ≤ (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') / 18 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 18)).2
        have hpow := hPlusPowBound
        nlinarith [hpow]
  exact ⟨hSameMean, hAdjacentMean, hPlusMean⟩

private theorem height_pr_exists_finset_le9 {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (μ : FinProb Ω) (S : Finset ι) (E : ι → Ω → Prop) :
    μ.pr (fun ω => ∃ i ∈ S, E i ω) ≤ ∑ i ∈ S, μ.pr (E i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert a S ha ih =>
      have hEq : (fun ω => ∃ i ∈ insert a S, E i ω) =
          (fun ω => E a ω ∨ ∃ i ∈ S, E i ω) := by
        funext ω
        apply propext
        constructor
        · rintro ⟨i, hi, hEi⟩
          rcases Finset.mem_insert.mp hi with h | h
          · subst i
            exact Or.inl hEi
          · exact Or.inr ⟨i, h, hEi⟩
        · rintro (hEi | ⟨i, hi, hEi⟩)
          · exact ⟨a, Finset.mem_insert_self _ _, hEi⟩
          · exact ⟨i, Finset.mem_insert_of_mem hi, hEi⟩
      rw [hEq]
      calc
        μ.pr (fun ω => E a ω ∨ ∃ i ∈ S, E i ω) ≤
            μ.pr (E a) + μ.pr (fun ω => ∃ i ∈ S, E i ω) :=
          FinProb.pr_union μ (E a) (fun ω => ∃ i ∈ S, E i ω)
        _ ≤ μ.pr (E a) + ∑ i ∈ S, μ.pr (E i) := add_le_add le_rfl ih
        _ = ∑ i ∈ insert a S, μ.pr (E i) := by simp [Finset.sum_insert, ha]

theorem height_level_window_card_le_five9 (H h : ℕ) :
    (Finset.univ.filter (fun j : Fin (H + 1) => Nat.dist j.val h ≤ 2)).card ≤ 5 := by
  classical
  let J : Finset (Fin (H + 1)) :=
    Finset.univ.filter (fun j => Nat.dist j.val h ≤ 2)
  let f : Fin 5 → ℕ := fun i =>
    if i.val = 0 then h - 2 else if i.val = 1 then h - 1 else
      if i.val = 2 then h else if i.val = 3 then h + 1 else h + 2
  let values : Finset ℕ := Finset.univ.image f
  have hvalues : J.image Fin.val ⊆ values := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    have hdist : Nat.dist j.val h ≤ 2 := (Finset.mem_filter.mp hj).2
    have hcases : j.val = h - 2 ∨ j.val = h - 1 ∨ j.val = h ∨
        j.val = h + 1 ∨ j.val = h + 2 := by
      unfold Nat.dist at hdist
      omega
    change j.val ∈ Finset.univ.image f
    rcases hcases with hval | hval | hval | hval | hval
    · exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, by simp [f, hval]⟩
    · exact Finset.mem_image.mpr ⟨⟨1, by omega⟩, Finset.mem_univ _, by simp [f, hval]⟩
    · exact Finset.mem_image.mpr ⟨⟨2, by omega⟩, Finset.mem_univ _, by simp [f, hval]⟩
    · exact Finset.mem_image.mpr ⟨⟨3, by omega⟩, Finset.mem_univ _, by simp [f, hval]⟩
    · exact Finset.mem_image.mpr ⟨⟨4, by omega⟩, Finset.mem_univ _, by simp [f, hval]⟩
  have hvaluesCard : values.card ≤ 5 := by
    calc
      values.card ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
      _ = 5 := by simp
  calc
    _ = J.card := by rfl
    _ = (J.image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ values.card := Finset.card_le_card hvalues
    _ ≤ 5 := hvaluesCard

private theorem crowdSame_le_active_slice_ball9 (C : Finset (Pos9 P hc n))
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) (R : ℕ) :
    crowdSame9 C Pp A v j R ≤
      ((Finset.univ.filter (fun c : Pos9 P hc n =>
        c.slice = specialWord9 (P.m n) v ∧
          _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ R ∧ c.level = j)).filter
        (fun c => Pp c = true ∧ A c = true)).card := by
  classical
  let S : Finset (Pos9 P hc n) := Finset.univ.filter (fun c =>
    c.slice = specialWord9 (P.m n) v ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ R ∧ c.level = j)
  apply Finset.card_le_card
  intro c hc
  simp only [crowdSame9, Finset.mem_filter] at hc
  rcases hc with ⟨hcC, ⟨hactive, hslice, hdist, hlevel⟩⟩
  rcases hactive with ⟨hP, hA⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨hslice, hdist, hlevel⟩, ⟨hP, hA⟩⟩

private theorem crowdAdj_le_active_slice_ball9 (C : Finset (Pos9 P hc n))
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) :
    crowdAdj9 C Pp A v j ≤
      ((Finset.univ.filter (fun c : Pos9 P hc n =>
        _root_.hammingDist c.slice (specialWord9 (P.m n) v) = 1 ∧
          _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n - 1 ∧
            c.level = j)).filter (fun c => Pp c = true ∧ A c = true)).card := by
  classical
  let S : Finset (Pos9 P hc n) := Finset.univ.filter (fun c =>
    _root_.hammingDist c.slice (specialWord9 (P.m n) v) = 1 ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n - 1 ∧
        c.level = j)
  apply Finset.card_le_card
  intro c hc
  simp only [crowdAdj9, Finset.mem_filter] at hc
  rcases hc with ⟨hcC, ⟨hactive, hslice, hdist, hlevel⟩⟩
  rcases hactive with ⟨hP, hA⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨hslice, hdist, hlevel⟩, ⟨hP, hA⟩⟩

theorem height_base_probability_bound9 (P : Params9) (hP : P.Valid)
    (hc : HeightChoice9 P) (hadm : hc.Admissible) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, HeightBase9 P hc n (hc.b₀ / 4) := by
  rcases hP with ⟨hcommon, hminus, hx, hσ, hχ, hgap, hvalidCase⟩
  have hP' : P.Valid := ⟨hcommon, hminus, hx, hσ, hχ, hgap, hvalidCase⟩
  rcases hadm with ⟨hσhpos, hσhζ, hζlt, hθpos, hθlt, ha, hab, hχa,
    hbpos, hbε, heps, hcaseAdm⟩
  let α : ℝ := (P.χ : ℝ) / 2
  let γ : ℝ := hc.b₀ / 4
  have hγpos : 0 < γ := by dsimp [γ]; positivity
  have hAlphaGap : 0 < α - γ := by
    have hσposR : 0 < (P.σ : ℝ) := by exact_mod_cast hσ.1
    cases hbranch : P.case with
    | sub yS yD yM =>
        have hcase : hc.b₀ < α := by simpa [hbranch, α] using hcaseAdm
        dsimp [γ, α] at hcase ⊢
        nlinarith [hbpos, hcase]
    | lin αS αD hB yB =>
        have hcase : hc.b₀ + (P.σ : ℝ) < α := by simpa [hbranch, α] using hcaseAdm
        have hσposR : 0 < (P.σ : ℝ) := by exact_mod_cast hσ.1
        dsimp [γ, α] at hcase ⊢
        nlinarith [hbpos, hσposR, hcase]
  have hHoleGap : 0 < hc.b₀ - γ := by dsimp [γ]; linarith [hbpos]
  have hσlt1 : (P.σ : ℝ) < 1 := by
    have hxS : P.xS < 1 := lt_trans hcommon.2.1 (lt_trans hcommon.2.2 (by norm_num))
    have hσq : P.σ < 1 := by linarith [hσ.2]
    exact_mod_cast hσq
  have hPlusGap : 0 < 1 - (P.σ : ℝ) + hc.eps' - γ := by
    dsimp [γ]
    have hthird : hc.b₀ / 4 < hc.eps' := by linarith [hbpos, hbε]
    linarith
  have hadm' : hc.Admissible :=
    ⟨hσhpos, hσhζ, hζlt, hθpos, hθlt, ha, hab, hχa, hbpos, hbε, heps, hcaseAdm⟩
  obtain ⟨nGeom, hGeom⟩ := height_base_small_scales9 P hP'
  obtain ⟨nV, hV⟩ := height_counts9_volume_bounds P hP'
  obtain ⟨nMean, hMean⟩ := height_base_mean_slack9 P hP' hc hadm'
  obtain ⟨nTailSame, hTailSame⟩ := height_rpow_eventually_ge9 (α - γ) 24
    hAlphaGap (by norm_num)
  obtain ⟨nTailPlus, hTailPlus⟩ := height_rpow_eventually_ge9
    (1 - (P.σ : ℝ) + hc.eps' - γ) 24 hPlusGap (by norm_num)
  obtain ⟨nTailHole, hTailHole⟩ := height_rpow_eventually_ge9 (hc.b₀ - γ) 16
    hHoleGap (by norm_num)
  obtain ⟨nTailExp, hTailExp⟩ := height_rpow_eventually_ge9 γ 4 hγpos (by norm_num)
  refine ⟨max nGeom (max nV (max nMean
    (max nTailSame (max nTailPlus (max nTailHole nTailExp))))), ?_⟩
  intro n hn
  have hnRestGeom : max nV (max nMean
      (max nTailSame (max nTailPlus (max nTailHole nTailExp)))) ≤ n :=
    le_trans (le_max_right _ _) hn
  have hnGeom : nGeom ≤ n := le_trans (le_max_left _ _) hn
  have hnOuter : max nMean (max nTailSame (max nTailPlus (max nTailHole nTailExp))) ≤ n :=
    le_trans (le_max_right _ _) hnRestGeom
  have hnV : nV ≤ n := le_trans (le_max_left _ _) hnRestGeom
  have hnMeanOuter : max nTailSame (max nTailPlus (max nTailHole nTailExp)) ≤ n :=
    le_trans (le_max_right _ _) hnOuter
  have hnMean : nMean ≤ n := le_trans (le_max_left _ _) hnOuter
  have hnTailOuter : max nTailPlus (max nTailHole nTailExp) ≤ n :=
    le_trans (le_max_right _ _) hnMeanOuter
  have hnTailSame : nTailSame ≤ n := le_trans (le_max_left _ _) hnMeanOuter
  have hnTailInner : max nTailHole nTailExp ≤ n := le_trans (le_max_right _ _) hnTailOuter
  have hnTailPlus : nTailPlus ≤ n := le_trans (le_max_left _ _) hnTailOuter
  have hnTailHole : nTailHole ≤ n := le_trans (le_max_left _ _) hnTailInner
  have hnTailExp : nTailExp ≤ n := le_trans (le_max_right _ _) hnTailInner
  have hgeomn := hGeom n hnGeom
  have hradiusReal : (11 : ℝ) ≤ (P.radius n : ℝ) := by exact_mod_cast hgeomn.2.2
  have hn44Real : 44 ≤ (n : ℝ) := by nlinarith [hgeomn.2.1, hradiusReal]
  have hn44 : 44 ≤ n := by exact_mod_cast hn44Real
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnreal1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hVn := hV n hnV
  have hMeann := hMean n hnMean
  have hSameGapLarge := hTailSame n hnTailSame
  have hPlusGapLarge := hTailPlus n hnTailPlus
  have hHoleGapLarge := hTailHole n hnTailHole
  have hExpGapLarge := hTailExp n hnTailExp
  have hpowSameTail : (n : ℝ) ^ α = (n : ℝ) ^ γ * (n : ℝ) ^ (α - γ) := by
    calc
      _ = (n : ℝ) ^ (γ + (α - γ)) := by congr 1; ring
      _ = _ := Real.rpow_add hnreal γ (α - γ)
  have hpowPlusTail :
      (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') =
        (n : ℝ) ^ γ * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps' - γ) := by
    calc
      _ = (n : ℝ) ^ (γ + (1 - (P.σ : ℝ) + hc.eps' - γ)) := by congr 1; ring
      _ = _ := Real.rpow_add hnreal γ _
  have hpowHoleTail : (n : ℝ) ^ hc.b₀ =
      (n : ℝ) ^ γ * (n : ℝ) ^ (hc.b₀ - γ) := by
    calc
      _ = (n : ℝ) ^ (γ + (hc.b₀ - γ)) := by congr 1; ring
      _ = _ := Real.rpow_add hnreal γ _
  have hSameTailExponent : 2 * (n : ℝ) ^ γ ≤ ((1 / 3 : ℝ) * (n : ℝ) ^ α) / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hSameGapLarge
      (Real.rpow_nonneg hnreal.le γ)
    rw [hpowSameTail]
    dsimp [α]
    nlinarith [hmul]
  have hPlusTailExponent : 2 * (n : ℝ) ^ γ ≤
      ((1 / 3 : ℝ) * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps')) / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hPlusGapLarge
      (Real.rpow_nonneg hnreal.le γ)
    rw [hpowPlusTail]
    nlinarith [hmul]
  have hHoleTailExponent : 2 * (n : ℝ) ^ γ ≤ (1 / 8 : ℝ) * (n : ℝ) ^ hc.b₀ := by
    have hmul := mul_le_mul_of_nonneg_left hHoleGapLarge
      (Real.rpow_nonneg hnreal.le γ)
    rw [hpowHoleTail]
    nlinarith [hmul]
  have hExpLarge : 16 ≤ Real.exp ((n : ℝ) ^ γ) := by
    have hbase : 16 ≤ Real.exp 4 := by
      have h := two_nat_pow_le_exp 4
      norm_num at h ⊢
      exact h
    exact le_trans hbase (Real.exp_le_exp.mpr hExpGapLarge)
  have hSmallTailSum :
      16 * Real.exp (-2 * (n : ℝ) ^ γ) ≤ Real.exp (-(n : ℝ) ^ γ) := by
    calc
      16 * Real.exp (-2 * (n : ℝ) ^ γ) ≤
          Real.exp ((n : ℝ) ^ γ) * Real.exp (-2 * (n : ℝ) ^ γ) :=
        mul_le_mul_of_nonneg_right hExpLarge (Real.exp_nonneg _)
      _ = Real.exp (-(n : ℝ) ^ γ) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hεlt1 : P.eps < 1 := by
    cases hbranch : P.case with
    | sub yS yD yM =>
        simp [Params9.eps, hbranch]
        have hmin : min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) ≤ (P.σ : ℝ) :=
          min_le_left _ _
        nlinarith [hσlt1, hmin]
    | lin αS αD hB yB =>
        simp [Params9.eps, hbranch]
        nlinarith [hσlt1]
  have hb0lt1 : hc.b₀ < 1 := lt_trans hbε (lt_trans heps hεlt1)
  have hqexp : hc.b₀ - 10 ≤ 0 := by linarith
  let p : ℝ := (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ)
  let q : ℝ := (n : ℝ) ^ (hc.b₀ - 10)
  have hpEq : p = (n : ℝ) ^ (10 : ℝ) / (residualBall9 P n : ℝ) := rfl
  have hqEq : q = (n : ℝ) ^ (hc.b₀ - 10) := rfl
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := hVn.2.2
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact Real.rpow_le_one_of_one_le_of_nonpos hnreal1 hqexp
  have hqpow : q * (n : ℝ) ^ (10 : ℝ) = (n : ℝ) ^ hc.b₀ := by
    dsimp [q]
    calc
      _ = (n : ℝ) ^ (10 : ℝ) * (n : ℝ) ^ (hc.b₀ - 10) := by ring
      _ = (n : ℝ) ^ ((10 : ℝ) + (hc.b₀ - 10)) :=
        (Real.rpow_add hnreal (10 : ℝ) (hc.b₀ - 10)).symm
      _ = _ := by congr 1 <;> ring
  have hpqEq : p * q = (n : ℝ) ^ hc.b₀ / (residualBall9 P n : ℝ) := by
    dsimp [p, q]
    have hqpowRaw : (n : ℝ) ^ (hc.b₀ - 10) * (n : ℝ) ^ (10 : ℝ) =
        (n : ℝ) ^ hc.b₀ := by simpa [q] using hqpow
    calc
      _ = ((n : ℝ) ^ (10 : ℝ) * (n : ℝ) ^ (hc.b₀ - 10)) /
          (residualBall9 P n : ℝ) := by ring
      _ = (n : ℝ) ^ (hc.b₀ - 10) * (n : ℝ) ^ (10 : ℝ) /
          (residualBall9 P n : ℝ) := by congr 1 <;> ring
      _ = (n : ℝ) ^ hc.b₀ / (residualBall9 P n : ℝ) := by rw [hqpowRaw]
  let μ : FinProb ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) :=
    heightLaw9 P hc n
  have hε : 0 ≤ Real.exp (-2 * (n : ℝ) ^ γ) := Real.exp_nonneg _
  have hcrowd (C : Finset (Pos9 P hc n)) (t s : ℝ) (ht : 1 / 3 ≤ t)
      (hs : 1 / 8 ≤ s) (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
      μ.pr (fun ω => badIn9 C t ω.1 ω.2 v j ∧
        s * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 C ω.1 v j : ℝ)) ≤
          Real.exp (-(n : ℝ) ^ γ) := by
    classical
    let Q : (Pos9 P hc n → Bool) → Prop := fun Pp =>
      s * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 C Pp v j : ℝ)
    let Hole : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop :=
      fun ω => holeIn9 C ω.1 ω.2 v j ∧ Q ω.1
    let J : Finset (Fin (hc.levels n + 1)) :=
      Finset.univ.filter (fun j' => Nat.dist j.val j'.val ≤ 2)
    let Crowd : (Pos9 P hc n → Bool) → (Pos9 P hc n → Bool) →
        Fin (hc.levels n + 1) → Prop := fun Pp A j' =>
      (t * (n : ℝ) ^ α < (crowdSame9 C Pp A v j' (P.radius n) : ℝ)) ∨
      (t * (n : ℝ) ^ α < (crowdAdj9 C Pp A v j' : ℝ)) ∨
      (t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
        (crowdSame9 C Pp A v j' (P.radius n + 1) : ℝ))
    let CrowdBad : ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop :=
      fun ω => ∃ j' ∈ J, Crowd ω.1 ω.2 j'
    let τ : ℝ := (1 / 3 : ℝ) * (n : ℝ) ^ α
    let τplus : ℝ := (1 / 3 : ℝ) * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps')
    have hSameτ : τ / 6 = (n : ℝ) ^ α / 18 := by dsimp [τ]; ring
    have hPlusτ : τplus / 6 =
        (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') / 18 := by dsimp [τplus]; ring
    have hHoleProb : μ.pr Hole ≤ Real.exp (-s * (n : ℝ) ^ hc.b₀) := by
      simpa [μ, Hole, Q] using
        (height_hole_probability_bound (P := P) (hc := hc) (n := n) C s
          (by linarith : 0 ≤ s) v j hq0 hq1 hqpow)
    have hSameCrowd (j' : Fin (hc.levels n + 1)) :
        μ.pr (fun ω => t * (n : ℝ) ^ α <
          (crowdSame9 C ω.1 ω.2 v j' (P.radius n) : ℝ)) ≤
            Real.exp (-2 * (n : ℝ) ^ γ) := by
      let S : Finset (Pos9 P hc n) := Finset.univ.filter (fun c =>
        c.slice = specialWord9 (P.m n) v ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n ∧ c.level = j')
      have hScardNat : S.card = residualBall9 P n := by
        simpa [S, residualBall9] using
          (height_slice_ball_card9 (P := P) (hc := hc) (n := n)
            (specialWord9 (P.m n) v) (residualWord9 (P.m n) v) j' (P.radius n))
      have hScard : (S.card : ℝ) = (residualBall9 P n : ℝ) := by exact_mod_cast hScardNat
      have hmean : p * q * (S.card : ℝ) ≤ τ / 6 := by
        calc
          _ = (n : ℝ) ^ hc.b₀ := by rw [hpqEq, hScard]; field_simp [ne_of_gt hVn.1]
          _ ≤ (n : ℝ) ^ α / 18 := hMeann.1
          _ = τ / 6 := hSameτ.symm
      have htail := height_active_count_tail (P := P) (hc := hc) (n := n)
        S p q τ hpEq hqEq hp0 hp1 hq0 hq1 (by positivity) hmean
      have hdom (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool))
          (hbad : t * (n : ℝ) ^ α <
            (crowdSame9 C ω.1 ω.2 v j' (P.radius n) : ℝ)) :
          τ ≤ ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ) := by
        have hcount := crowdSame_le_active_slice_ball9 C ω.1 ω.2 v j' (P.radius n)
        have hcountR : (crowdSame9 C ω.1 ω.2 v j' (P.radius n) : ℝ) ≤
            ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ) := by
          exact_mod_cast hcount
        have htau : τ ≤ t * (n : ℝ) ^ α := by
          dsimp [τ]
          exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hnreal.le _)
        exact le_trans (le_trans htau (le_of_lt hbad)) hcountR
      have hmono := finProb_pr_mono μ
        (fun ω => t * (n : ℝ) ^ α <
          (crowdSame9 C ω.1 ω.2 v j' (P.radius n) : ℝ))
        (fun ω => τ ≤ ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ)) hdom
      have hexp : Real.exp (-τ / 4) ≤ Real.exp (-2 * (n : ℝ) ^ γ) :=
        Real.exp_le_exp.mpr (by linarith [hSameTailExponent])
      exact hmono.trans (htail.trans hexp)
    have hAdjCrowd (j' : Fin (hc.levels n + 1)) :
        μ.pr (fun ω => t * (n : ℝ) ^ α < (crowdAdj9 C ω.1 ω.2 v j' : ℝ)) ≤
          Real.exp (-2 * (n : ℝ) ^ γ) := by
      let S : Finset (Pos9 P hc n) := Finset.univ.filter (fun c =>
        _root_.hammingDist c.slice (specialWord9 (P.m n) v) = 1 ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n - 1 ∧
          c.level = j')
      have hScardNat : S.card ≤ P.m n *
          (∑ i ∈ Finset.range (P.radius n - 1 + 1),
            Nat.choose (n - P.m n) i) := by
        simpa [S] using
          (height_adjacent_ball_card_le9 (P := P) (hc := hc) (n := n)
            (specialWord9 (P.m n) v) (residualWord9 (P.m n) v) j' (P.radius n - 1))
      have hScard : (S.card : ℝ) ≤
          (P.m n : ℝ) * heightBallVolReal9 (n - P.m n) (P.radius n - 1) := by
        simpa [heightBallVolReal9] using (by exact_mod_cast hScardNat)
      have hmean : p * q * (S.card : ℝ) ≤ τ / 6 := by
        calc
          _ ≤ p * q * ((P.m n : ℝ) * heightBallVolReal9
                (n - P.m n) (P.radius n - 1)) :=
              mul_le_mul_of_nonneg_left hScard (mul_nonneg hp0 hq0)
          _ = (n : ℝ) ^ hc.b₀ * (P.m n : ℝ) *
                heightBallVolReal9 (n - P.m n) (P.radius n - 1) /
                  (residualBall9 P n : ℝ) := by rw [hpqEq]; ring
          _ ≤ (n : ℝ) ^ α / 18 := hMeann.2.1
          _ = τ / 6 := hSameτ.symm
      have htail := height_active_count_tail (P := P) (hc := hc) (n := n)
        S p q τ hpEq hqEq hp0 hp1 hq0 hq1 (by positivity) hmean
      have hdom (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool))
          (hbad : t * (n : ℝ) ^ α < (crowdAdj9 C ω.1 ω.2 v j' : ℝ)) :
          τ ≤ ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ) := by
        have hcount := crowdAdj_le_active_slice_ball9 C ω.1 ω.2 v j'
        have hcountR : (crowdAdj9 C ω.1 ω.2 v j' : ℝ) ≤
            ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ) := by
          exact_mod_cast hcount
        have htau : τ ≤ t * (n : ℝ) ^ α := by
          dsimp [τ]
          exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hnreal.le _)
        exact le_trans (le_trans htau (le_of_lt hbad)) hcountR
      have hmono := finProb_pr_mono μ
        (fun ω => t * (n : ℝ) ^ α < (crowdAdj9 C ω.1 ω.2 v j' : ℝ))
        (fun ω => τ ≤ ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ)) hdom
      have hexp : Real.exp (-τ / 4) ≤ Real.exp (-2 * (n : ℝ) ^ γ) :=
        Real.exp_le_exp.mpr (by linarith [hSameTailExponent])
      exact hmono.trans (htail.trans hexp)
    have hPlusCrowd (j' : Fin (hc.levels n + 1)) :
        μ.pr (fun ω => t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
          (crowdSame9 C ω.1 ω.2 v j' (P.radius n + 1) : ℝ)) ≤
            Real.exp (-2 * (n : ℝ) ^ γ) := by
      let S : Finset (Pos9 P hc n) := Finset.univ.filter (fun c =>
        c.slice = specialWord9 (P.m n) v ∧
        _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n + 1 ∧
          c.level = j')
      have hScardNat : S.card =
          ∑ i ∈ Finset.range (P.radius n + 2), Nat.choose (n - P.m n) i := by
        simpa [S] using
          (height_slice_ball_card9 (P := P) (hc := hc) (n := n)
            (specialWord9 (P.m n) v) (residualWord9 (P.m n) v) j' (P.radius n + 1))
      have hScard : (S.card : ℝ) =
          heightBallVolReal9 (n - P.m n) (P.radius n + 1) := by
        simpa [heightBallVolReal9] using (by exact_mod_cast hScardNat)
      have hmean : p * q * (S.card : ℝ) ≤ τplus / 6 := by
        calc
          _ = (n : ℝ) ^ hc.b₀ *
                heightBallVolReal9 (n - P.m n) (P.radius n + 1) /
                  (residualBall9 P n : ℝ) := by rw [hpqEq, hScard]; ring
          _ ≤ (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') / 18 := hMeann.2.2
          _ = τplus / 6 := hPlusτ.symm
      have htail := height_active_count_tail (P := P) (hc := hc) (n := n)
        S p q τplus hpEq hqEq hp0 hp1 hq0 hq1 (by positivity) hmean
      have hdom (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool))
          (hbad : t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
            (crowdSame9 C ω.1 ω.2 v j' (P.radius n + 1) : ℝ)) :
          τplus ≤ ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ) := by
        have hcount := crowdSame_le_active_slice_ball9 C ω.1 ω.2 v j' (P.radius n + 1)
        have hcountR : (crowdSame9 C ω.1 ω.2 v j' (P.radius n + 1) : ℝ) ≤
            ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ) := by
          exact_mod_cast hcount
        have htau : τplus ≤ t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') := by
          dsimp [τplus]
          exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hnreal.le _)
        exact le_trans (le_trans htau (le_of_lt hbad)) hcountR
      have hmono := finProb_pr_mono μ
        (fun ω => t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
          (crowdSame9 C ω.1 ω.2 v j' (P.radius n + 1) : ℝ))
        (fun ω => τplus ≤ ((S.filter (fun c => ω.1 c = true ∧ ω.2 c = true)).card : ℝ)) hdom
      have hexp : Real.exp (-τplus / 4) ≤ Real.exp (-2 * (n : ℝ) ^ γ) :=
        Real.exp_le_exp.mpr (by linarith [hPlusTailExponent])
      exact hmono.trans (htail.trans hexp)
    let E : Fin (hc.levels n + 1) →
        ((Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) → Prop := fun j' ω =>
      (t * (n : ℝ) ^ α < (crowdSame9 C ω.1 ω.2 v j' (P.radius n) : ℝ)) ∨
      (t * (n : ℝ) ^ α < (crowdAdj9 C ω.1 ω.2 v j' : ℝ)) ∨
      (t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
        (crowdSame9 C ω.1 ω.2 v j' (P.radius n + 1) : ℝ))
    have hCrowdProb : μ.pr CrowdBad ≤ 15 * Real.exp (-2 * (n : ℝ) ^ γ) := by
      have hExists := height_pr_exists_finset_le9 μ J E
      have hEach (j' : Fin (hc.levels n + 1)) : μ.pr (E j') ≤
          3 * Real.exp (-2 * (n : ℝ) ^ γ) := by
        have h23 := FinProb.pr_union μ
          (fun ω => t * (n : ℝ) ^ α < (crowdAdj9 C ω.1 ω.2 v j' : ℝ))
          (fun ω => t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
            (crowdSame9 C ω.1 ω.2 v j' (P.radius n + 1) : ℝ))
        calc
          μ.pr (E j') ≤
              μ.pr (fun ω => t * (n : ℝ) ^ α <
                (crowdSame9 C ω.1 ω.2 v j' (P.radius n) : ℝ)) +
              μ.pr (fun ω => t * (n : ℝ) ^ α <
                (crowdAdj9 C ω.1 ω.2 v j' : ℝ) ∨
                t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
                (crowdSame9 C ω.1 ω.2 v j' (P.radius n + 1) : ℝ)) :=
            FinProb.pr_union μ _ _
          _ ≤ Real.exp (-2 * (n : ℝ) ^ γ) +
              (Real.exp (-2 * (n : ℝ) ^ γ) + Real.exp (-2 * (n : ℝ) ^ γ)) := by
            have h23Bound :
                μ.pr (fun ω => t * (n : ℝ) ^ α < (crowdAdj9 C ω.1 ω.2 v j' : ℝ) ∨
                  t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
                    (crowdSame9 C ω.1 ω.2 v j' (P.radius n + 1) : ℝ)) ≤
                  Real.exp (-2 * (n : ℝ) ^ γ) + Real.exp (-2 * (n : ℝ) ^ γ) := by
              calc
                _ ≤ μ.pr (fun ω => t * (n : ℝ) ^ α <
                    (crowdAdj9 C ω.1 ω.2 v j' : ℝ)) +
                    μ.pr (fun ω => t * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') <
                      (crowdSame9 C ω.1 ω.2 v j' (P.radius n + 1) : ℝ)) := h23
                _ ≤ _ := add_le_add (hAdjCrowd j') (hPlusCrowd j')
            exact add_le_add (hSameCrowd j') h23Bound
          _ = 3 * Real.exp (-2 * (n : ℝ) ^ γ) := by ring
      have hsum :
          (∑ j' ∈ J, μ.pr (E j')) ≤
            ∑ _j' ∈ J, 3 * Real.exp (-2 * (n : ℝ) ^ γ) := by
        apply Finset.sum_le_sum
        intro j' hj'
        exact hEach j'
      have hJcardNat : J.card ≤ 5 := by
        simpa [J, Nat.dist_comm] using
          (height_level_window_card_le_five9 (hc.levels n) j.val)
      have hcardJR : (J.card : ℝ) ≤ 5 := by
        exact_mod_cast hJcardNat
      calc
        μ.pr CrowdBad ≤ ∑ j' ∈ J, μ.pr (E j') := by
          simpa [CrowdBad, E] using hExists
        _ ≤ ∑ _j' ∈ J, 3 * Real.exp (-2 * (n : ℝ) ^ γ) := hsum
        _ = (J.card : ℝ) * (3 * Real.exp (-2 * (n : ℝ) ^ γ)) := by simp
        _ ≤ 15 * Real.exp (-2 * (n : ℝ) ^ γ) := by
          have hmul := mul_le_mul_of_nonneg_right hcardJR (by positivity :
            0 ≤ 3 * Real.exp (-2 * (n : ℝ) ^ γ))
          nlinarith [hmul]
    have hnbase : 0 ≤ (n : ℝ) ^ hc.b₀ := Real.rpow_nonneg hnreal.le _
    have hHoleFinal : Real.exp (-s * (n : ℝ) ^ hc.b₀) ≤
        Real.exp (-2 * (n : ℝ) ^ γ) := by
      have hsLow : 1 / 8 ≤ s := hs
      have hbase : (1 / 8 : ℝ) * (n : ℝ) ^ hc.b₀ ≤ s * (n : ℝ) ^ hc.b₀ :=
        mul_le_mul_of_nonneg_right hsLow hnbase
      have hexp : 2 * (n : ℝ) ^ γ ≤ s * (n : ℝ) ^ hc.b₀ :=
        le_trans (by linarith [hHoleTailExponent]) hbase
      exact Real.exp_le_exp.mpr (by linarith [hexp])
    have hbadSubset (ω : (Pos9 P hc n → Bool) × (Pos9 P hc n → Bool)) :
        (badIn9 C t ω.1 ω.2 v j ∧ Q ω.1) → Hole ω ∨ CrowdBad ω := by
      intro hbad
      rcases hbad with ⟨hbad, hQ⟩
      rcases hbad with hhole | ⟨j', hdist, hcounts⟩
      · exact Or.inl ⟨hhole, hQ⟩
      · right
        refine ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩, ?_⟩
        exact hcounts
    have hmono := finProb_pr_mono μ
      (fun ω => badIn9 C t ω.1 ω.2 v j ∧ Q ω.1)
      (fun ω => Hole ω ∨ CrowdBad ω) hbadSubset
    have hprobOr := FinProb.pr_union μ Hole CrowdBad
    have hfinal : μ.pr (fun ω => badIn9 C t ω.1 ω.2 v j ∧ Q ω.1) ≤
        Real.exp (-(n : ℝ) ^ γ) := by
      calc
        _ ≤ μ.pr (fun ω => Hole ω ∨ CrowdBad ω) := hmono
        _ ≤ μ.pr Hole + μ.pr CrowdBad := hprobOr
        _ ≤ Real.exp (-s * (n : ℝ) ^ hc.b₀) +
            15 * Real.exp (-2 * (n : ℝ) ^ γ) :=
          add_le_add hHoleProb hCrowdProb
        _ ≤ 16 * Real.exp (-2 * (n : ℝ) ^ γ) := by
          calc
            _ ≤ Real.exp (-2 * (n : ℝ) ^ γ) +
                15 * Real.exp (-2 * (n : ℝ) ^ γ) :=
              calc
                _ = 15 * Real.exp (-2 * (n : ℝ) ^ γ) +
                    Real.exp (-s * (n : ℝ) ^ hc.b₀) := by ring
                _ ≤ 15 * Real.exp (-2 * (n : ℝ) ^ γ) +
                    Real.exp (-2 * (n : ℝ) ^ γ) :=
                  add_le_add_right hHoleFinal _
                _ = _ := by ring
            _ = 16 * Real.exp (-2 * (n : ℝ) ^ γ) := by ring
        _ ≤ Real.exp (-(n : ℝ) ^ γ) := hSmallTailSum
    simpa only [Q] using hfinal
  intro C t s ht htu hs v j
  simpa [μ] using hcrowd C t s ht hs v j

theorem sharedConsulted_residual_separation_general9
    (hm : P.m n ≤ n) (v v' : CubeVertex n) (R' : ℕ) (K : ℝ)
    (hsep : K * (R' : ℝ) ≤ (_root_.hammingDist v v' : ℝ))
    (c : Pos9 P hc n)
    (hshared : c ∈ consulted9 (P := P) (hc := hc) (n := n) v R' ∩
      consulted9 v' R') :
    (K - 4) * (R' : ℝ) - 2 ≤
      (_root_.hammingDist (residualWord9 (P.m n) v)
        (residualWord9 (P.m n) v') : ℝ) := by
  have hlocal := sharedConsulted_local_bounds v v' R' c hshared
  have hspecial :
      (_root_.hammingDist (specialWord9 (P.m n) v)
        (specialWord9 (P.m n) v') : ℝ) ≤ 4 * (R' : ℝ) + 2 := by
    have hnat : _root_.hammingDist (specialWord9 (P.m n) v)
        (specialWord9 (P.m n) v') ≤ 4 * R' + 2 := by
      calc
        _ ≤ _root_.hammingDist (specialWord9 (P.m n) v) c.slice +
            _root_.hammingDist c.slice (specialWord9 (P.m n) v') :=
          _root_.hammingDist_triangle _ _ _
        _ ≤ (2 * R' + 1) + (2 * R' + 1) := by
          exact Nat.add_le_add (by simpa [_root_.hammingDist_comm] using hlocal.1)
            hlocal.2.1
        _ = 4 * R' + 2 := by omega
    exact_mod_cast hnat
  have hproj := splitProjectionDist_ge hm v v'
  have hprojR : (_root_.hammingDist v v' : ℝ) ≤
      (_root_.hammingDist (specialWord9 (P.m n) v)
        (specialWord9 (P.m n) v') : ℝ) +
      (_root_.hammingDist (residualWord9 (P.m n) v)
        (residualWord9 (P.m n) v') : ℝ) := by exact_mod_cast hproj
  linarith

private theorem uniform_subset_contains_probability9 {d s : ℕ}
    (hd : 0 < d) (hsd : s ≤ d) (A : Finset (Fin d)) (hAs : A.card ≤ s) :
    (CubeGeometryPToolsCubeR.sampleLaw d s hsd).pr
        (fun B : Finset (Fin d) => A ⊆ B) ≤ ((s : ℝ) / (d : ℝ)) ^ A.card := by
  classical
  let μ := CubeGeometryPToolsCubeR.sampleLaw d s hsd
  let X : Finset (Fin d) → ℝ := fun B =>
    (Nat.choose (A ∩ B).card A.card : ℝ)
  have hXnonneg : ∀ B, 0 ≤ X B := by
    intro B
    dsimp [X]
    positivity
  have hsubset (B : Finset (Fin d)) (hAB : A ⊆ B) : 1 ≤ X B := by
    have hinter : A ∩ B = A := Finset.inter_eq_left.mpr hAB
    simp [X, hinter]
  have hmono := finProb_pr_mono μ (fun B => A ⊆ B) (fun B => 1 ≤ X B) hsubset
  have hmark := FinProb.markov μ X 1 hXnonneg (by norm_num)
  have hmoment := CubeGeometryPToolsCubeR.sampleLaw_factorialMoment
    A hsd hAs
  have hmoment' : μ.expect X =
      (Nat.choose s A.card : ℝ) / (Nat.choose d A.card : ℝ) := by
    simpa [μ, X, CubeGeometryPToolsCubeR.intersectionWeight, div_eq_mul_inv] using hmoment
  have hratio := CubeGeometryPToolsCubeR.choose_ratio_le_pow
    (K := s) (d := d) (j := A.card) hsd hd
  calc
    μ.pr (fun B => A ⊆ B) ≤ μ.pr (fun B => 1 ≤ X B) := hmono
    _ ≤ μ.expect X / 1 := hmark
    _ = (Nat.choose s A.card : ℝ) / (Nat.choose d A.card : ℝ) := by rw [hmoment']; norm_num
    _ ≤ ((s : ℝ) / (d : ℝ)) ^ A.card := by
      simpa using hratio

private theorem uniform_subset_intersection_ge_probability9 {d s : ℕ}
    (hd : 0 < d) (hsd : s ≤ d) (A : Finset (Fin d)) (k : ℕ)
    (hk : 1 ≤ k) (hks : k ≤ s) :
    (CubeGeometryPToolsCubeR.sampleLaw d s hsd).pr
        (fun B : Finset (Fin d) => k ≤ (A ∩ B).card) ≤
      (2 : ℝ) ^ A.card * ((s : ℝ) / (d : ℝ)) ^ k := by
  classical
  let μ := CubeGeometryPToolsCubeR.sampleLaw d s hsd
  let Ts : Finset (Finset (Fin d)) := A.powersetCard k
  let E : Finset (Fin d) → Prop := fun B => k ≤ (A ∩ B).card
  let F : Finset (Fin d) → Prop := fun B => ∃ T ∈ Ts, T ⊆ B
  have hEF (B : Finset (Fin d)) (hB : E B) : F B := by
    obtain ⟨T, hTA, hTcard⟩ := Finset.exists_subset_card_eq hB
    have hTsubA : T ⊆ A := by
      intro x hx
      exact (Finset.mem_inter.mp (hTA hx)).1
    have hTsubB : T ⊆ B := by
      intro x hx
      exact (Finset.mem_inter.mp (hTA hx)).2
    have hTmem : T ∈ Ts := by
      exact Finset.mem_powersetCard.mpr ⟨hTsubA, hTcard⟩
    exact ⟨T, hTmem, hTsubB⟩
  have hmono := finProb_pr_mono μ E F hEF
  have hEach (T : Finset (Fin d)) (hT : T ∈ Ts) :
      μ.pr (fun B => T ⊆ B) ≤ ((s : ℝ) / (d : ℝ)) ^ k := by
    have hTprop := Finset.mem_powersetCard.mp hT
    have hTcard : T.card = k := hTprop.2
    have hTk : T.card ≤ s := by omega
    simpa [μ, hTcard] using uniform_subset_contains_probability9
      (d := d) (s := s) hd hsd T hTk
  have hExists := height_pr_exists_finset_le9 μ Ts (fun T B => T ⊆ B)
  have hcardTs : Ts.card = Nat.choose A.card k := by
    simp [Ts, Finset.card_powersetCard]
  have hchoose : (Ts.card : ℝ) ≤ (2 : ℝ) ^ A.card := by
    rw [hcardTs]
    exact_mod_cast Nat.choose_le_two_pow A.card k
  have hsum : (∑ T ∈ Ts, μ.pr (fun B => T ⊆ B)) ≤
      (Ts.card : ℝ) * ((s : ℝ) / (d : ℝ)) ^ k := by
    calc
      _ ≤ ∑ _T ∈ Ts, ((s : ℝ) / (d : ℝ)) ^ k := by
        apply Finset.sum_le_sum
        intro T hT
        exact hEach T hT
      _ = (Ts.card : ℝ) * ((s : ℝ) / (d : ℝ)) ^ k := by simp
  have hbase := hmono.trans hExists
  calc
    μ.pr E ≤ ∑ T ∈ Ts, μ.pr (fun B => T ⊆ B) := hbase
    _ ≤ (Ts.card : ℝ) * ((s : ℝ) / (d : ℝ)) ^ k := hsum
    _ ≤ (2 : ℝ) ^ A.card * ((s : ℝ) / (d : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_right hchoose (by positivity)

private theorem shell_subset_intersection_count9 {d s : ℕ}
    (A : Finset (Fin d)) (k : ℕ) (hsd : s ≤ d)
    (hk : 1 ≤ k) (hks : k ≤ s) :
    (let Bset : Finset (Finset (Fin d)) := Finset.univ.filter (fun B =>
      B.card = s ∧ k ≤ (A ∩ B).card);
     (Bset.card : ℝ) ≤
      (Nat.choose d s : ℝ) *
        ((2 : ℝ) ^ A.card * ((s : ℝ) / (d : ℝ)) ^ k)) := by
  classical
  let Bset : Finset (Finset (Fin d)) := Finset.univ.filter (fun B =>
    B.card = s ∧ k ≤ (A ∩ B).card)
  let μ := CubeGeometryPToolsCubeR.sampleLaw d s hsd
  let E : Finset (Fin d) → Prop := fun B => k ≤ (A ∩ B).card
  letI : DecidablePred E := fun B => Classical.propDecidable (E B)
  have hset : (CubeGeometryPToolsCubeR.samples d s).filter E = Bset := by
    ext X
    simp [Bset, CubeGeometryPToolsCubeR.samples, E, and_comm]
  have hprob := uniform_subset_intersection_ge_probability9
    (d := d) (s := s) (by omega : 0 < d) hsd A k hk hks
  have hchoosePos : 0 < (Nat.choose d s : ℝ) := by
    exact_mod_cast Nat.choose_pos hsd
  have hprobEq : μ.pr E = (Bset.card : ℝ) / (Nat.choose d s : ℝ) := by
    calc
      μ.pr E =
          ((CubeGeometryPToolsCubeR.samples d s).filter E).card /
            (Nat.choose d s : ℝ) := by
          simpa [μ] using CubeGeometryPToolsCubeR.sampleLaw_pr hsd E
      _ = _ := by rw [hset]
  have hratio : (Bset.card : ℝ) / (Nat.choose d s : ℝ) ≤
      (2 : ℝ) ^ A.card * ((s : ℝ) / (d : ℝ)) ^ k := by
    calc
      _ = μ.pr E := hprobEq.symm
      _ ≤ _ := hprob
  have hmul := (div_le_iff₀ hchoosePos).1 hratio
  have hmul' : (Bset.card : ℝ) ≤
      (2 : ℝ) ^ A.card * ((s : ℝ) / (d : ℝ)) ^ k *
        (Nat.choose d s : ℝ) := by simpa [mul_assoc] using hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'

private theorem choose_lower_layer_ratio9 (d R i : ℕ)
    (hi : i ≤ R) (hR : 1 ≤ R) (hRhalf : 2 * R ≤ d) :
    (Nat.choose d i : ℝ) / Nat.choose d R ≤
      ((2 * (R : ℝ)) / (d : ℝ)) ^ (R - i) := by
  have hdi : R ≤ d - i := by omega
  have hdiPos : 0 < d - i := by omega
  have hChooseMulNat : Nat.choose d R * Nat.choose R i =
      Nat.choose d i * Nat.choose (d - i) (R - i) := Nat.choose_mul hi
  have hChooseMul : (Nat.choose d R : ℝ) * Nat.choose R i =
      (Nat.choose d i : ℝ) * Nat.choose (d - i) (R - i) := by
    exact_mod_cast hChooseMulNat
  have hDen : (Nat.choose d R : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : R ≤ d)).ne'
  have hDenSub : (Nat.choose (d - i) (R - i) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : R - i ≤ d - i)).ne'
  have hratioEq : (Nat.choose d i : ℝ) / Nat.choose d R =
      (Nat.choose R i : ℝ) / Nat.choose (d - i) (R - i) := by
    apply (div_eq_div_iff hDen hDenSub).2
    nlinarith [hChooseMul]
  have hsum : R = i + (R - i) := by omega
  have hsymm : Nat.choose R i = Nat.choose R (R - i) := Nat.choose_symm_of_eq_add hsum
  have hratioPow := CubeGeometryPToolsCubeR.choose_ratio_le_pow
    (K := R) (d := d - i) (j := R - i) hdi hdiPos
  have hbase : (R : ℝ) / (d - i : ℕ) ≤ 2 * (R : ℝ) / d := by
    apply (div_le_div_iff₀ (by exact_mod_cast hdiPos) (by exact_mod_cast (show 0 < d by omega))).2
    have hden : (d : ℝ) / 2 ≤ ((d - i : ℕ) : ℝ) := by
      have hDi : ((d - i : ℕ) : ℝ) = (d : ℝ) - (i : ℝ) := Nat.cast_sub (by omega)
      rw [hDi]
      have hiR : (i : ℝ) ≤ (R : ℝ) := by exact_mod_cast hi
      have hRhalfR : 2 * (R : ℝ) ≤ (d : ℝ) := by exact_mod_cast hRhalf
      nlinarith
    have hRposR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
    nlinarith [hden, hRposR]
  calc
    _ = (Nat.choose R i : ℝ) / Nat.choose (d - i) (R - i) := hratioEq
    _ = (Nat.choose R (R - i) : ℝ) / Nat.choose (d - i) (R - i) := by rw [hsymm]
    _ ≤ ((R : ℝ) / (d - i : ℕ)) ^ (R - i) := hratioPow
    _ ≤ ((2 * (R : ℝ)) / (d : ℝ)) ^ (R - i) := by gcongr

theorem choose_upper_layer_ratio9 (d r k : ℕ)
    (hr : 1 ≤ r) (hrk : r + k ≤ d) :
    (Nat.choose d (r + k) : ℝ) / Nat.choose d r ≤ ((d : ℝ) / r) ^ k := by
  induction k with
  | zero =>
      have hchoosePos : 0 < (Nat.choose d r : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega : r ≤ d)
      simp only [Nat.add_zero, pow_zero]
      exact le_of_eq (div_self hchoosePos.ne')
  | succ k ih =>
      have hrk' : r + k ≤ d := by omega
      let s := r + k
      have hsle : s ≤ d := by dsimp [s]; omega
      have hspos : 0 < s + 1 := by omega
      have hChoosePos : 0 < (Nat.choose d s : ℝ) := by
        exact_mod_cast Nat.choose_pos hsle
      have hChooseNextPos : 0 < (Nat.choose d (s + 1) : ℝ) := by
        exact_mod_cast Nat.choose_pos (by dsimp [s]; omega)
      have hChooseRPos : 0 < (Nat.choose d r : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega)
      have hrec := Nat.choose_succ_right_eq d s
      have hrecR : (Nat.choose d (s + 1) : ℝ) * (s + 1) =
          (Nat.choose d s : ℝ) * (d - s) := by exact_mod_cast hrec
      have hstep : (Nat.choose d (s + 1) : ℝ) / Nat.choose d s ≤
          (d : ℝ) / (s + 1) := by
        apply (div_le_div_iff₀ hChoosePos (by positivity : (0 : ℝ) < s + 1)).2
        nlinarith [hrecR]
      have hstep' : (d : ℝ) / (s + 1) ≤ (d : ℝ) / r := by
        apply div_le_div_of_nonneg_left (by positivity : 0 ≤ (d : ℝ))
          (by exact_mod_cast hr : (0 : ℝ) < r)
        exact_mod_cast (show r ≤ s + 1 by dsimp [s]; omega)
      have hsplit :
          (Nat.choose d (s + 1) : ℝ) / Nat.choose d r =
            ((Nat.choose d (s + 1) : ℝ) / Nat.choose d s) *
              ((Nat.choose d s : ℝ) / Nat.choose d r) := by
        field_simp [ne_of_gt hChoosePos, ne_of_gt hChooseRPos]
        <;> ring
      calc
        _ = ((Nat.choose d (s + 1) : ℝ) / Nat.choose d s) *
              ((Nat.choose d s : ℝ) / Nat.choose d r) := hsplit
        _ ≤ ((d : ℝ) / r) * ((d : ℝ) / r) ^ k :=
          mul_le_mul (hstep.trans hstep') (ih hrk') (by positivity) (by positivity)
        _ = ((d : ℝ) / r) ^ (k + 1) := by rw [pow_succ]; ring

private theorem height_vertex_shell_intersection_count9 {d R D i k : ℕ}
    (x y : CubeVertex d) (hD : _root_.hammingDist x y = D)
    (hi : i ≤ d) (hDle : D ≤ d) (hk : 1 ≤ k) (hki : k ≤ i)
    (hneed : ∀ u : CubeVertex d, _root_.hammingDist u x = i →
      _root_.hammingDist u y ≤ R →
        k ≤ (heightDiffSet9 x u ∩ heightDiffSet9 x y).card) :
    ((Finset.univ.filter (fun u : CubeVertex d =>
      _root_.hammingDist u x = i ∧ _root_.hammingDist u y ≤ R)).card : ℝ) ≤
      (Nat.choose d i : ℝ) *
        ((2 : ℝ) ^ D * ((i : ℝ) / (d : ℝ)) ^ k) := by
  classical
  let A : Finset (Fin d) := heightDiffSet9 x y
  let U : Finset (CubeVertex d) := Finset.univ.filter (fun u =>
    _root_.hammingDist u x = i ∧ _root_.hammingDist u y ≤ R)
  let B : Finset (Finset (Fin d)) := Finset.univ.filter (fun S =>
    S.card = i ∧ k ≤ (S ∩ A).card)
  have hAcard : A.card = D := by
    have h := heightDiffSet_card9 x y
    dsimp [A]
    simpa [_root_.hammingDist_comm, hD] using h
  have hmap : ∀ u, u ∈ U → heightDiffSet9 x u ∈ B := by
    intro u hu
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hcard : (heightDiffSet9 x u).card = i := by
      rw [heightDiffSet_card9]
      simpa [_root_.hammingDist_comm] using hu.1
    have hint := hneed u hu.1 hu.2
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcard, by simpa [A] using hint⟩
  have hinj : Set.InjOn (heightDiffSet9 x) U := by
    intro u hu v hv huv
    exact (heightDiffEquiv9 x).injective huv
  have himageSub : U.image (heightDiffSet9 x) ⊆ B := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨u, hu, rfl⟩
    exact hmap u hu
  have hcard : U.card ≤ B.card := by
    calc
      U.card = (U.image (heightDiffSet9 x)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ B.card := Finset.card_le_card himageSub
  have hBbound : (B.card : ℝ) ≤
      (Nat.choose d i : ℝ) * ((2 : ℝ) ^ A.card * ((i : ℝ) / (d : ℝ)) ^ k) := by
    simpa [B, Finset.inter_comm] using
      shell_subset_intersection_count9 (d := d) (s := i) A k hi hk hki
  have hcardR : (U.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hcard
  calc
    (U.card : ℝ) ≤ (B.card : ℝ) := hcardR
    _ ≤ (Nat.choose d i : ℝ) *
        ((2 : ℝ) ^ A.card * ((i : ℝ) / (d : ℝ)) ^ k) := hBbound
    _ = (Nat.choose d i : ℝ) *
        ((2 : ℝ) ^ D * ((i : ℝ) / (d : ℝ)) ^ k) := by rw [hAcard]

private theorem height_diff_intersection_lower9 {d i R D k : ℕ}
    (x y u : CubeVertex d) (hD : _root_.hammingDist x y = D)
    (hix : _root_.hammingDist u x = i) (hiy : _root_.hammingDist u y ≤ R)
    (hneed : R - i + 2 * k ≤ D) :
    k ≤ (heightDiffSet9 x u ∩ heightDiffSet9 x y).card := by
  have hSCard : (heightDiffSet9 x u).card = i := by
    rw [heightDiffSet_card9]
    simpa [_root_.hammingDist_comm] using hix
  have hACard : (heightDiffSet9 x y).card = D := by
    have h := heightDiffSet_card9 x y
    simpa [_root_.hammingDist_comm, hD] using h
  have hdistSet :
      _root_.hammingDist u y =
        (heightDiffSet9 x u ∆ heightDiffSet9 x y).card := by
    rw [← heightDiffSet_card9 y u, heightDiffSet_symmDiff9]
  have hsymm := height_card_symmDiff9 (heightDiffSet9 x u) (heightDiffSet9 x y)
  rw [hSCard, hACard] at hsymm
  rw [hdistSet] at hiy
  have hsum : i + D ≤ R + 2 * (heightDiffSet9 x u ∩ heightDiffSet9 x y).card := by
    omega
  omega

theorem height_ball_intersection_shell_sum9 {d R D k : ℕ}
    (x y : CubeVertex d) (hD : _root_.hammingDist x y = D)
    (hDle : D ≤ d) (hRhalf : 2 * R ≤ d)
    (hRpos : 1 ≤ R) (hk : 1 ≤ k) (hk4 : 4 * k ≤ D) :
    ((Finset.univ.filter (fun u : CubeVertex d =>
      _root_.hammingDist u x ≤ R ∧ _root_.hammingDist u y ≤ R)).card : ℝ) ≤
      ((R + 1 : ℕ) : ℝ) * (Nat.choose d R : ℝ) *
        ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k +
          ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) := by
  classical
  let I : Finset (CubeVertex d) := Finset.univ.filter (fun u =>
    _root_.hammingDist u x ≤ R ∧ _root_.hammingDist u y ≤ R)
  let shell : ℕ → Finset (CubeVertex d) := fun i => Finset.univ.filter (fun u =>
    _root_.hammingDist u x = i ∧ _root_.hammingDist u y ≤ R)
  have hcover : I ⊆ (Finset.range (R + 1)).biUnion shell := by
    intro u hu
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine Finset.mem_biUnion.mpr ⟨_root_.hammingDist u x,
      Finset.mem_range.mpr (by omega), ?_⟩
    simp [shell, hu.1, hu.2]
  have hCRpos : 0 < (Nat.choose d R : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : R ≤ d)
  have hdPos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hbase0 : 0 ≤ (2 * (R : ℝ)) / (d : ℝ) := by positivity
  have hbase1 : (2 * (R : ℝ)) / (d : ℝ) ≤ 1 := by
    rw [div_le_one₀ hdPos]
    exact_mod_cast hRhalf
  have hchooseMono (i : ℕ) (hi : i ≤ R) :
      (Nat.choose d i : ℝ) ≤ Nat.choose d R := by
    have hratio := choose_lower_layer_ratio9 d R i hi hRpos hRhalf
    have hpow : ((2 * (R : ℝ)) / (d : ℝ)) ^ (R - i) ≤ 1 :=
      pow_le_one₀ hbase0 hbase1
    exact (div_le_one₀ hCRpos).1 (hratio.trans hpow)
  have hShellBound (i : ℕ) (hi : i ≤ R) :
      (shell i).card ≤
        (Nat.choose d R : ℝ) *
          ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k +
            ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) := by
    by_cases hhigh : 2 * (R - i) ≤ D
    · have hneed : R - i + 2 * k ≤ D := by omega
      by_cases hki : k ≤ i
      · have hcount := height_vertex_shell_intersection_count9
          (d := d) (R := R) (D := D) (i := i) (k := k) x y hD
          (by omega) (by omega) hk hki (by
            intro u hux huy
            exact height_diff_intersection_lower9 x y u hD hux huy hneed)
        have hchoose := hchooseMono i hi
        have hiratio : (i : ℝ) / (d : ℝ) ≤ (R : ℝ) / (d : ℝ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hi) hdPos.le
        have hpowratio : ((i : ℝ) / (d : ℝ)) ^ k ≤
            ((R : ℝ) / (d : ℝ)) ^ k := by gcongr
        have hcountCast : ((shell i).card : ℝ) ≤
            (Nat.choose d R : ℝ) *
              ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k) := by
          have hcount' : ((shell i).card : ℝ) ≤
              (Nat.choose d i : ℝ) *
                ((2 : ℝ) ^ D * ((i : ℝ) / (d : ℝ)) ^ k) := by
            simpa [shell] using hcount
          calc
            ((shell i).card : ℝ) ≤ (Nat.choose d i : ℝ) *
                ((2 : ℝ) ^ D * ((i : ℝ) / (d : ℝ)) ^ k) := hcount'
            _ ≤ (Nat.choose d R : ℝ) *
                ((2 : ℝ) ^ D * ((i : ℝ) / (d : ℝ)) ^ k) :=
              mul_le_mul_of_nonneg_right hchoose (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hpowratio (by positivity))
              (Nat.cast_nonneg _)
        calc
          ((shell i).card : ℝ) ≤ (Nat.choose d R : ℝ) *
              ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k) := hcountCast
          _ ≤ (Nat.choose d R : ℝ) *
              ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k +
                ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) := by
            have hterm : (0 : ℝ) ≤ ((Nat.choose d R : ℝ) *
                ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) := by positivity
            calc
              _ = (Nat.choose d R : ℝ) *
                  ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k) + 0 := by ring
              _ ≤ (Nat.choose d R : ℝ) *
                    ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k) +
                    ((Nat.choose d R : ℝ) *
                      ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) :=
                add_le_add_right hterm _
              _ = _ := by ring
      · have hempty : shell i = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro u hu
          simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          have hq := height_diff_intersection_lower9 x y u hD hu.1 hu.2 hneed
          have hqle : (heightDiffSet9 x u ∩ heightDiffSet9 x y).card ≤ i := by
            calc
              _ ≤ (heightDiffSet9 x u).card := Finset.card_le_card Finset.inter_subset_left
              _ = i := by rw [heightDiffSet_card9]; simpa [_root_.hammingDist_comm] using hu.1
          omega
        simp only [hempty, Finset.card_empty, Nat.cast_zero]
        positivity
    · have hlow : D / 2 ≤ R - i := by omega
      have hratio := choose_lower_layer_ratio9 d R i hi hRpos hRhalf
      have hbasePow : ((2 * (R : ℝ)) / (d : ℝ)) ^ (R - i) ≤
          ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2) :=
        pow_le_pow_of_le_one hbase0 hbase1 hlow
      have hchooseLe : (Nat.choose d i : ℝ) ≤
          (Nat.choose d R : ℝ) *
            ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2) := by
        have hratio' := hratio.trans hbasePow
        have hchooseLe' : (Nat.choose d i : ℝ) ≤
            (((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) *
              (Nat.choose d R : ℝ) := (div_le_iff₀ hCRpos).1 hratio'
        calc
          (Nat.choose d i : ℝ) ≤
              (((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) *
                (Nat.choose d R : ℝ) := hchooseLe'
          _ = (Nat.choose d R : ℝ) *
              (((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) := by ring
      have hcardLe : (shell i).card ≤ Nat.choose d i := by
        have hsphere : (Finset.univ.filter (fun u : CubeVertex d =>
            _root_.hammingDist u x = i)).card = Nat.choose d i :=
          height_hamming_sphere_card9 (d := d) i x
        have hsubSphere : shell i ⊆ Finset.univ.filter
            (fun u : CubeVertex d => _root_.hammingDist u x = i) := by
          intro u hu
          simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.1⟩
        calc
          (shell i).card ≤ (Finset.univ.filter (fun u : CubeVertex d =>
              _root_.hammingDist u x = i)).card := Finset.card_le_card hsubSphere
          _ = Nat.choose d i := hsphere
      have hcountCast : ((shell i).card : ℝ) ≤
          (Nat.choose d R : ℝ) * ((2 * (R : ℝ) / (d : ℝ)) ^ (D / 2)) := by
        exact (Nat.cast_le.mpr hcardLe).trans hchooseLe
      calc
        ((shell i).card : ℝ) ≤
            (Nat.choose d R : ℝ) * (((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) := hcountCast
        _ ≤ (Nat.choose d R : ℝ) *
            ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k +
              ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) := by
          have hterm : (0 : ℝ) ≤ ((Nat.choose d R : ℝ) *
              ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k)) := by positivity
          calc
            _ = (Nat.choose d R : ℝ) *
                ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2) + 0 := by ring
            _ ≤ (Nat.choose d R : ℝ) *
                  ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2) +
                  (Nat.choose d R : ℝ) *
                    ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k) :=
              add_le_add_right hterm _
            _ = _ := by ring
  have hsumNat : I.card ≤
      ∑ i ∈ Finset.range (R + 1), (shell i).card := by
    calc
      I.card ≤ ((Finset.range (R + 1)).biUnion shell).card :=
        Finset.card_le_card hcover
      _ ≤ _ := Finset.card_biUnion_le
  have hsumReal : (I.card : ℝ) ≤
      ((R + 1 : ℕ) : ℝ) * (Nat.choose d R : ℝ) *
        ((2 : ℝ) ^ D * ((R : ℝ) / (d : ℝ)) ^ k +
          ((2 * (R : ℝ)) / (d : ℝ)) ^ (D / 2)) := by
    calc
      _ ≤ (∑ i ∈ Finset.range (R + 1), (shell i).card : ℝ) := by exact_mod_cast hsumNat
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hiR : i ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact_mod_cast hShellBound i hiR
      _ = _ := by simp; ring
  simpa [I] using hsumReal

theorem height_overlap_shell_decay9 {n R' D k : ℕ} (q : ℝ)
    (hn : 2 ≤ n) (hR : 1 ≤ R')
    (hpow40 : 2 ≤ (n : ℝ) ^ (1 / 40 : ℝ))
    (hpow8 : 2 ≤ (n : ℝ) ^ (1 / 8 : ℝ))
    (hq0 : 0 ≤ q) (hq : q ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)))
    (hk : D ≤ 5 * k) (hD : 1018 * R' ≤ D) :
    (n : ℝ) ^ ((11 * R' : ℕ) : ℝ) *
      ((2 : ℝ) ^ D * q ^ k + (2 * q) ^ (D / 2)) ≤
      Real.exp (-(Real.log 2 * (R' : ℝ))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hRcast : (1 : ℝ) ≤ (R' : ℝ) := by exact_mod_cast hR
  have hDcast : (1018 : ℝ) * (R' : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hkcast : (D : ℝ) ≤ 5 * (k : ℝ) := by exact_mod_cast hk
  have hfirstExp : (D : ℝ) / 40 - (k : ℝ) / 4 ≤ -(25 * (R' : ℝ)) := by
    nlinarith
  have hsecondExp : -((D / 2 : ℕ) : ℝ) / 8 ≤ -(25 * (R' : ℝ)) := by
    have hfloorNat : 2 * D ≤ 5 * (D / 2) := by omega
    have hfloor : (2 : ℝ) * (D : ℝ) ≤ 5 * ((D / 2 : ℕ) : ℝ) := by
      exact_mod_cast hfloorNat
    nlinarith
  have htwoD : (2 : ℝ) ^ D ≤
      (n : ℝ) ^ ((D : ℝ) / 40) := by
    calc
      (2 : ℝ) ^ D ≤ ((n : ℝ) ^ (1 / 40 : ℝ)) ^ D :=
        pow_le_pow_left₀ (by norm_num) hpow40 D
      _ = (n : ℝ) ^ ((D : ℝ) / 40) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
        congr 1
        push_cast
        ring
  have hqk : q ^ k ≤
      (n : ℝ) ^ (-(k : ℝ) / 4) := by
    calc
      q ^ k ≤ ((n : ℝ) ^ (-(1 / 4 : ℝ))) ^ k :=
        pow_le_pow_left₀ hq0 hq k
      _ = (n : ℝ) ^ (-(k : ℝ) / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
        congr 1
        push_cast
        ring
  have hfirst : (2 : ℝ) ^ D * q ^ k ≤
      (n : ℝ) ^ (-(25 * (R' : ℝ))) := by
    calc
      (2 : ℝ) ^ D * q ^ k ≤
          (n : ℝ) ^ ((D : ℝ) / 40) * (n : ℝ) ^ (-(k : ℝ) / 4) :=
        mul_le_mul htwoD hqk (by positivity) (by positivity)
      _ = (n : ℝ) ^ ((D : ℝ) / 40 - (k : ℝ) / 4) := by
        rw [← Real.rpow_add hnR]
        congr 1
        ring
      _ ≤ (n : ℝ) ^ (-(25 * (R' : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le hnR1 hfirstExp
  have htwoq : 2 * q ≤ (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
    calc
      2 * q ≤ 2 * (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
      _ ≤ (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hpow8 (by positivity)
      _ = (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
        rw [← Real.rpow_add hnR]
        congr 1
        norm_num
  have hsecondPow : (2 * q) ^ (D / 2) ≤
      (n : ℝ) ^ (-((D / 2 : ℕ) : ℝ) / 8) := by
    calc
      (2 * q) ^ (D / 2) ≤
          ((n : ℝ) ^ (-(1 / 8 : ℝ))) ^ (D / 2) :=
        pow_le_pow_left₀ (by positivity) htwoq (D / 2)
      _ = (n : ℝ) ^ (-((D / 2 : ℕ) : ℝ) / 8) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
        congr 1
        push_cast
        ring
  have hsecond : (2 * q) ^ (D / 2) ≤
      (n : ℝ) ^ (-(25 * (R' : ℝ))) := by
    exact hsecondPow.trans (Real.rpow_le_rpow_of_exponent_le hnR1 hsecondExp)
  have hsum : (2 : ℝ) ^ D * q ^ k + (2 * q) ^ (D / 2) ≤
      2 * (n : ℝ) ^ (-(25 * (R' : ℝ))) := by
    calc
      _ ≤ (n : ℝ) ^ (-(25 * (R' : ℝ))) +
          (n : ℝ) ^ (-(25 * (R' : ℝ))) := add_le_add hfirst hsecond
      _ = _ := by ring
  have htwoR : 2 ≤ (2 : ℝ) ^ ((R' : ℕ) : ℝ) := by
    have htwoNat : 2 ≤ (2 : ℝ) ^ R' := by
      calc
        2 = (2 : ℝ) ^ 1 := by norm_num
        _ ≤ (2 : ℝ) ^ R' := pow_le_pow_right₀ (by norm_num) hR
    simpa [Real.rpow_natCast] using htwoNat
  have hpowR : (2 : ℝ) ^ ((R' : ℕ) : ℝ) ≤ (n : ℝ) ^ ((R' : ℕ) : ℝ) := by
    have hpowNat : (2 : ℝ) ^ R' ≤ (n : ℝ) ^ R' :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hn) R'
    simpa [Real.rpow_natCast] using hpowNat
  have hpowRtwo : 2 ≤ (n : ℝ) ^ ((R' : ℕ) : ℝ) := htwoR.trans hpowR
  have hsumOne : 2 * (n : ℝ) ^ (-(25 * (R' : ℝ))) ≤
      (n : ℝ) ^ (-(24 * (R' : ℝ))) := by
    calc
      _ ≤ (n : ℝ) ^ (R' : ℝ) * (n : ℝ) ^ (-(25 * (R' : ℝ))) :=
        mul_le_mul_of_nonneg_right hpowRtwo (by positivity)
      _ = (n : ℝ) ^ (-(24 * (R' : ℝ))) := by
        rw [← Real.rpow_add hnR]
        congr 1
        ring
  have hsumFinal : (2 : ℝ) ^ D * q ^ k + (2 * q) ^ (D / 2) ≤
      (n : ℝ) ^ (-(24 * (R' : ℝ))) := hsum.trans hsumOne
  have hproduct : (n : ℝ) ^ ((11 * R' : ℕ) : ℝ) *
      ((2 : ℝ) ^ D * q ^ k + (2 * q) ^ (D / 2)) ≤
      (n : ℝ) ^ (-(13 * (R' : ℝ))) := by
    rw [show ((11 * R' : ℕ) : ℝ) = 11 * (R' : ℝ) by norm_num]
    calc
      _ ≤ (n : ℝ) ^ (11 * (R' : ℝ)) *
          (n : ℝ) ^ (-(24 * (R' : ℝ))) :=
        mul_le_mul_of_nonneg_left hsumFinal (by positivity)
      _ = (n : ℝ) ^ (-(13 * (R' : ℝ))) := by
        rw [← Real.rpow_add hnR]
        congr 1
        push_cast
        ring
  have hweak : (n : ℝ) ^ (-(13 * (R' : ℝ))) ≤
      (n : ℝ) ^ (-(R' : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hnR1
    nlinarith [hRcast]
  have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hfinal : (n : ℝ) ^ (-(R' : ℝ)) ≤
      Real.exp (-(Real.log 2 * (R' : ℝ))) := by
    rw [Real.rpow_def_of_pos hnR]
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hproduct.trans (hweak.trans hfinal)



end HypercubeRamsey.Lane_q_s09_map
