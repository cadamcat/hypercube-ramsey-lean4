import HypercubeRamsey.S05.Even_load_centre_sol_s05_even
import HypercubeRamsey.S05.Even_setup_local_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

variable {γ K' χ : ℝ}

def canonicalHeightAdmissible (p : Params5 γ K' χ) :
    HDAdmissible 10 (p.alpha / 10000) (p.alpha / 2000) (p.alpha / 1000000)
      (p.alpha / 100000) (1 - p.alpha / 100000) (p.alpha / 20000) (1 / 2) 2 8 where
  hJ := by norm_num
  hb := by
    rcases p.halpha with ⟨h0, h1⟩
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  hD := by decide
  hsz := by
    rcases p.halpha with ⟨h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  ha := by
    rcases p.halpha with ⟨h0, h1⟩
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  hd := by norm_num

def canonicalHeightRegime (p : Params5 γ K' χ) : HDRegime (p.alpha / 10000) (p.alpha / 2000) 8 :=
  .lin (p.rho / 4) ⟨div_pos p.hrho.1 (by norm_num), by linarith [p.hrho.2]⟩

theorem selectionAt_some_mem_level (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (τ : p.Ties) (R : ℕ) (v : CubeVertex p.d) (l : p.Loc)
    (hselect : p.selectionAt Sites P A E τ R v = some l) :
    ∃ j : Fin (p.H + 1), l ∈ E v j ∧ j.val = p.height Sites P A E R v := by
  let j := p.height Sites P A E R v
  have hEq : p.height Sites P A E R v = j := rfl
  by_cases hj : j < p.H
  · simp [HDParams.selectionAt, hEq, hj] at hselect
    rcases hselect with ⟨_, ⟨hne, hchosen⟩⟩
    let j' : Fin (p.H + 1) := ⟨j, by omega⟩
    let active := (E v j').filter fun l => A l = true
    let priorities := active.image (p.priority τ (v, j'))
    have hneP : priorities.Nonempty := by
      obtain ⟨l, hl⟩ := hne
      exact ⟨p.priority τ (v, j') l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
    let q := priorities.min' hneP
    have hmem : ∃ l, l ∈ active ∧ p.priority τ (v, j') l = q :=
      Finset.mem_image.mp (Finset.min'_mem priorities hneP)
    have hc : Classical.choose hmem = l := by
      simpa [active, priorities, q, j'] using hchosen
    have hl := (Classical.choose_spec hmem).1
    rw [hc] at hl
    exact ⟨j', (Finset.mem_filter.mp hl).1, rfl⟩
  · simp [HDParams.selectionAt, hEq, hj] at hselect

theorem selection_level_eq_height (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (l : p.Loc)
    (hshape : ∀ j l, l ∈ E v j → l.2 = j)
    (hselect : p.selection Sites P A E τ v = some l) :
    l.2.val = p.height Sites P A E p.Rlong v := by
  obtain ⟨j, hl, hj⟩ := selectionAt_some_mem_level p Sites P A E τ p.Rlong v l hselect
  exact (congrArg Fin.val (hshape j l hl)).trans hj

theorem probability_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A B : Ω → Prop)
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · simp [hA, hAB ω hA]
  · simp only [if_neg hA]
    split_ifs
    · exact P.nonneg ω
    · rfl

theorem level_zero_selection_bound (p : HDParams) (hlam : 0 < p.lam) (P : p.Loc → Bool)
    (E : p.EligMap) (Sites : p.Sites) (v : CubeVertex p.d) (hv : v ∈ Sites) (l : p.Loc)
    (hl0 : l.2.val = 0) (hshape : ∀ j l, l ∈ E v j → l.2 = j) :
    (p.actLaw.prod p.tieLaw).pr (fun ω =>
      p.Legal P E (p.domBall Sites v p.Rlong) ∧ p.selection Sites P ω.1 E ω.2 v = some l) ≤ 3 / p.lam := by
  let j0 : Fin (p.H + 1) := ⟨0, by omega⟩
  have hdom : v ∈ p.domBall Sites v p.Rlong := by
    exact Finset.mem_filter.mpr ⟨hv, by simp⟩
  have hheight (A : p.Loc → Bool) (τ : p.Ties)
      (hs : p.selection Sites P A E τ v = some l) : p.height Sites P A E p.Rlong v = 0 := by
    exact (selection_level_eq_height p Sites P A E τ v l hshape hs).symm.trans hl0
  have hmem (A : p.Loc → Bool) (τ : p.Ties)
      (hs : p.selection Sites P A E τ v = some l) : l ∈ E v j0 := by
    obtain ⟨j, hl, hj⟩ := selectionAt_some_mem_level p Sites P A E τ p.Rlong v l hs
    have heq : j = j0 := Fin.ext (hj.trans (hheight A τ hs))
    exact heq ▸ hl
  by_cases hlegal : p.LegalAt P E v j0
  · by_cases hl : l ∈ E v j0
    · have hmono := probability_mono (p.actLaw.prod p.tieLaw)
        (fun ω => p.Legal P E (p.domBall Sites v p.Rlong) ∧ p.selection Sites P ω.1 E ω.2 v = some l)
        (fun ω => p.height Sites P ω.1 E p.Rlong v = 0 ∧ p.selection Sites P ω.1 E ω.2 v = some l)
        (by intro ω hω; exact ⟨hheight ω.1 ω.2 hω.2, hω.2⟩)
      exact hmono.trans (height_selection_tie p hlam P E Sites v l hlegal hl)
    · have hzero : (p.actLaw.prod p.tieLaw).pr (fun ω =>
          p.Legal P E (p.domBall Sites v p.Rlong) ∧ p.selection Sites P ω.1 E ω.2 v = some l) = 0 := by
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro ω _
        exact if_neg (fun hω => hl (hmem ω.1 ω.2 hω.2))
      rw [hzero]
      positivity
  · have hzero : (p.actLaw.prod p.tieLaw).pr (fun ω =>
        p.Legal P E (p.domBall Sites v p.Rlong) ∧ p.selection Sites P ω.1 E ω.2 v = some l) = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro ω _
      exact if_neg (fun hω => hlegal (hω.1 v hdom j0))
    rw [hzero]
    positivity

def forcedPresenceLaw {I : Type*} [Fintype I] [DecidableEq I] (q : ℝ) (l : I) : FinProb (I → Bool) :=
  FinProb.pi fun i => if i = l then FinProb.bernoulli 1 else FinProb.bernoulli q

theorem forced_presence_weight {I : Type*} [Fintype I] [DecidableEq I] (q : ℝ) (l : I) (P : I → Bool) :
    (FinProb.pi (fun _ : I => FinProb.bernoulli q)).w P * (if P l then (1 : ℝ) else 0) =
      max 0 (min q 1) * (forcedPresenceLaw q l).w P := by
  classical
  let raw := fun i : I => (FinProb.bernoulli q).w (P i)
  let forced := fun i : I => (if i = l then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P i)
  have hother : ∏ i ∈ Finset.univ.erase l, forced i = ∏ i ∈ Finset.univ.erase l, raw i := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [forced, raw, (Finset.mem_erase.mp hi).1]
  change (∏ i, raw i) * (if P l then (1 : ℝ) else 0) = max 0 (min q 1) * ∏ i, forced i
  cases hPl : P l with
  | false =>
    have hz : ∏ i, forced i = 0 := Finset.prod_eq_zero (Finset.mem_univ l) (by
      simp [forced, hPl, FinProb.bernoulli])
    simp [hPl, hz]
  | true =>
    rw [← Finset.mul_prod_erase Finset.univ raw (Finset.mem_univ l),
      ← Finset.mul_prod_erase Finset.univ forced (Finset.mem_univ l), hother]
    simp [raw, forced, hPl, FinProb.bernoulli]

theorem forced_presence_expect {I : Type*} [Fintype I] [DecidableEq I] (q : ℝ) (l : I) (f : (I → Bool) → ℝ) :
    (FinProb.pi (fun _ : I => FinProb.bernoulli q)).expect (fun P => if P l then f P else 0) =
      max 0 (min q 1) * (forcedPresenceLaw q l).expect f := by
  unfold FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  have he : (FinProb.pi (fun _ : I => FinProb.bernoulli q)).w P * (if P l then f P else 0) =
      ((FinProb.pi (fun _ : I => FinProb.bernoulli q)).w P * (if P l then (1 : ℝ) else 0)) * f P := by
    cases h : P l <;> simp [h]
  rw [he, forced_presence_weight]
  ring

end
end HypercubeRamsey.Lane_sol_s05_even
