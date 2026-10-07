import HypercubeRamsey.S09.Map.Device
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2
import HypercubeRamsey.Framework.FinProbLemmas
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

end HypercubeRamsey.Lane_q_s09_map
