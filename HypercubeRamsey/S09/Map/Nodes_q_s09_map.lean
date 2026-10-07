import HypercubeRamsey.S09.Map.Device
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2
import HypercubeRamsey.Framework.FinProbLemmas

/-!
Private support for lane `q-s09-map`.  This file contains translations from the
slice-indexed Section 9 experiment to the generic Section 3 height estimates.
-/

namespace HypercubeRamsey.Lane_q_s09_map

open OAI.HypercubeRamsey Classical
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

private theorem crowdSame_le_univ (C : Finset (Pos9 P hc n))
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) (R : ℕ) :
    crowdSame9 C Pp A v j R ≤ crowdSame9 Finset.univ Pp A v j R := by
  unfold crowdSame9
  apply Finset.card_mono
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨Finset.mem_univ _, hc.2⟩

private theorem crowdAdj_le_univ (C : Finset (Pos9 P hc n))
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) :
    crowdAdj9 C Pp A v j ≤ crowdAdj9 Finset.univ Pp A v j := by
  unfold crowdAdj9
  apply Finset.card_mono
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨Finset.mem_univ _, hc.2⟩

private theorem bad_crowd_mono_univ
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

private theorem sharedConsulted_local_bounds
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
