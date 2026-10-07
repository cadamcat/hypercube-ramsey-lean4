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
open scoped BigOperators

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

end HypercubeRamsey.Lane_q_s09_map
