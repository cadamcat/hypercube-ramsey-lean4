import HypercubeRamsey.Framework.OneShot

/-!
# Tested patch properties and regime predicates

Blueprint part B §1.5 (`research/blueprint/PART-B.md`, lines 174–231): the properties tested in Sections 4 and
6–11, the countable family `FamB` stabilized once, and Definition 9.1's limiting exponents as availability
predicates.
-/

namespace HypercubeRamsey

open Filter

/-- Absolute bias at least `n^{-h}` within width budgets (Lemma 4.1(i) is the power case). -/
def PBias (wX wY : ℝ → ℝ) (h : ℝ) : PairProp := fun n _N E μ ν =>
  μ.WidthLE (wX n) ∧ ν.WidthLE (wY n) ∧ (n : ℝ) ^ (-h) ≤ |dens E true μ ν - 1 / 2|

/-- Purity at the doubled power budgets (Lemma 4.1(ii)): defect at most `exp(-n^h)` in some colour. -/
def PPure (β γ h : ℝ) : PairProp := fun n _N E μ ν =>
  μ.WidthLE (2 * (n : ℝ) ^ β) ∧ ν.WidthLE (2 * (n : ℝ) ^ γ) ∧
    ∃ c : Colour, dens E (!c) μ ν ≤ Real.exp (-(n : ℝ) ^ h)

/-- Violation of (7.1): `N max σ ≤ n^{D₀}`, `width τ ≤ n^{1/4}`, some colour of density `≤ n^{-c}`. -/
def PViol (D₀ c : ℝ) : PairProp := fun n _N E σ τ =>
  σ.CapLE ((n : ℝ) ^ D₀) ∧ τ.WidthLE ((n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    ∃ col : Colour, dens E col σ τ ≤ (n : ℝ) ^ (-c)

/-- One-colour grid purity (Lemma 7.1's hypothesis). -/
def PGridPure (G : Colour) (d p : ℝ) : PairProp := fun n _N E μ ν =>
  μ.WidthLE ((n : ℝ) ^ (d / 2)) ∧ ν.WidthLE ((n : ℝ) ^ (d / 2)) ∧
    ∀ y, 0 < ν.w y → 1 - Real.exp (-(n : ℝ) ^ p) ≤ colDeg E G μ y

/-- Full-dimensional cluster witness in colour `G` (Proposition 10.1). -/
def PCluster (G : Colour) (ζ δ : ℝ) : PatchProp := fun n N E => {AB |
  ∃ (μ : Law N) (K : ℕ) (lam : Fin K → ℝ) (D : Fin K → Law N),
    μ.SupportedIn AB.1 ∧ (∀ j, (D j).SupportedIn AB.2) ∧
    (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧
    μ.WidthLE ((n : ℝ) ^ δ) ∧
    (∀ y, ∑ j, lam j * (D j).w y ≤ Real.exp ((n : ℝ) ^ δ) / N) ∧
    (∀ j y, (D j).w y ≤ Real.exp (-(n : ℝ) ^ ζ)) ∧
    (∀ j, 0 < lam j → ∀ y y', 0 < (D j).w y → 0 < (D j).w y' →
       1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ y y')}

/-- The countable family of properties tested in Sections 6–11 (closed under `swap`). -/
def FamB : Set PatchProp :=
  {P | ∃ D₀ c : ℚ, P = (PViol D₀ c).toPatch ∨ P = (PViol D₀ c).toPatch.swap} ∪
  {P | ∃ β γ h : ℚ, P = (PPure β γ h).toPatch ∨ P = (PPure β γ h).toPatch.swap} ∪
  {P | ∃ x y h : ℚ, P = (PBias (pw x) (pw y) h).toPatch ∨ P = (PBias (pw x) (pw y) h).toPatch.swap} ∪
  {P | ∃ x α h : ℚ, P = (PBias (pw x) (lw α) h).toPatch ∨ P = (PBias (pw x) (lw α) h).toPatch.swap} ∪
  {P | ∃ (G : Colour) (ζ δ : ℚ), P = PCluster G ζ δ ∨ P = (PCluster G ζ δ).swap}

theorem FamB_countable : FamB.Countable := by
  have countable_pair {α : Type} [Countable α] (f g : α → PatchProp) :
      {P : PatchProp | ∃ a, P = f a ∨ P = g a}.Countable := by
    let encode : α × Bool → PatchProp := fun p => if p.2 then g p.1 else f p.1
    apply (Set.countable_range encode).mono
    rintro P ⟨a, hP⟩
    rcases hP with hP | hP
    · exact ⟨(a, false), by simpa [encode] using hP.symm⟩
    · exact ⟨(a, true), by simpa [encode] using hP.symm⟩
  have hViol : {P : PatchProp | ∃ D₀ c : ℚ,
      P = (PViol D₀ c).toPatch ∨ P = (PViol D₀ c).toPatch.swap}.Countable := by
    apply (countable_pair
      (fun p : ℚ × ℚ => (PViol p.1 p.2).toPatch)
      (fun p : ℚ × ℚ => (PViol p.1 p.2).toPatch.swap)).mono
    rintro P ⟨D₀, c, hP⟩
    exact ⟨(D₀, c), hP⟩
  have hPure : {P : PatchProp | ∃ β γ h : ℚ,
      P = (PPure β γ h).toPatch ∨ P = (PPure β γ h).toPatch.swap}.Countable := by
    apply (countable_pair
      (fun p : ℚ × ℚ × ℚ => (PPure p.1 p.2.1 p.2.2).toPatch)
      (fun p : ℚ × ℚ × ℚ => (PPure p.1 p.2.1 p.2.2).toPatch.swap)).mono
    rintro P ⟨β, γ, h, hP⟩
    exact ⟨(β, γ, h), hP⟩
  have hBiasPP : {P : PatchProp | ∃ x y h : ℚ,
      P = (PBias (pw x) (pw y) h).toPatch ∨ P = (PBias (pw x) (pw y) h).toPatch.swap}.Countable := by
    apply (countable_pair
      (fun p : ℚ × ℚ × ℚ => (PBias (pw p.1) (pw p.2.1) p.2.2).toPatch)
      (fun p : ℚ × ℚ × ℚ => (PBias (pw p.1) (pw p.2.1) p.2.2).toPatch.swap)).mono
    rintro P ⟨x, y, h, hP⟩
    exact ⟨(x, y, h), hP⟩
  have hBiasPL : {P : PatchProp | ∃ x α h : ℚ,
      P = (PBias (pw x) (lw α) h).toPatch ∨ P = (PBias (pw x) (lw α) h).toPatch.swap}.Countable := by
    apply (countable_pair
      (fun p : ℚ × ℚ × ℚ => (PBias (pw p.1) (lw p.2.1) p.2.2).toPatch)
      (fun p : ℚ × ℚ × ℚ => (PBias (pw p.1) (lw p.2.1) p.2.2).toPatch.swap)).mono
    rintro P ⟨x, α, h, hP⟩
    exact ⟨(x, α, h), hP⟩
  have hCluster : {P : PatchProp | ∃ (G : Colour) (ζ δ : ℚ),
      P = PCluster G ζ δ ∨ P = (PCluster G ζ δ).swap}.Countable := by
    apply (countable_pair
      (fun p : Colour × ℚ × ℚ => PCluster p.1 p.2.1 p.2.2)
      (fun p : Colour × ℚ × ℚ => (PCluster p.1 p.2.1 p.2.2).swap)).mono
    rintro P ⟨G, ζ, δ, hP⟩
    exact ⟨(G, ζ, δ), hP⟩
  unfold FamB
  exact (((hViol.union hPure).union hBiasPP).union hBiasPL).union hCluster

theorem FamB_swap : ∀ P ∈ FamB, P.swap ∈ FamB := by
  have swap_swap (P : PatchProp) : P.swap.swap = P := by
    funext n N E
    ext AB
    rfl
  have hViol : ∀ P ∈ {P : PatchProp | ∃ D₀ c : ℚ,
      P = (PViol D₀ c).toPatch ∨ P = (PViol D₀ c).toPatch.swap},
      P.swap ∈ {P : PatchProp | ∃ D₀ c : ℚ,
        P = (PViol D₀ c).toPatch ∨ P = (PViol D₀ c).toPatch.swap} := by
    intro P hP
    rcases hP with ⟨D₀, c, hP⟩
    rcases hP with hP | hP
    · subst P
      exact ⟨D₀, c, Or.inr rfl⟩
    · subst P
      exact ⟨D₀, c, Or.inl (swap_swap _ )⟩
  have hPure : ∀ P ∈ {P : PatchProp | ∃ β γ h : ℚ,
      P = (PPure β γ h).toPatch ∨ P = (PPure β γ h).toPatch.swap},
      P.swap ∈ {P : PatchProp | ∃ β γ h : ℚ,
        P = (PPure β γ h).toPatch ∨ P = (PPure β γ h).toPatch.swap} := by
    intro P hP
    rcases hP with ⟨β, γ, h, hP⟩
    rcases hP with hP | hP
    · subst P
      exact ⟨β, γ, h, Or.inr rfl⟩
    · subst P
      exact ⟨β, γ, h, Or.inl (swap_swap _)⟩
  have hBiasPP : ∀ P ∈ {P : PatchProp | ∃ x y h : ℚ,
      P = (PBias (pw x) (pw y) h).toPatch ∨ P = (PBias (pw x) (pw y) h).toPatch.swap},
      P.swap ∈ {P : PatchProp | ∃ x y h : ℚ,
        P = (PBias (pw x) (pw y) h).toPatch ∨ P = (PBias (pw x) (pw y) h).toPatch.swap} := by
    intro P hP
    rcases hP with ⟨x, y, h, hP⟩
    rcases hP with hP | hP
    · subst P
      exact ⟨x, y, h, Or.inr rfl⟩
    · subst P
      exact ⟨x, y, h, Or.inl (swap_swap _)⟩
  have hBiasPL : ∀ P ∈ {P : PatchProp | ∃ x α h : ℚ,
      P = (PBias (pw x) (lw α) h).toPatch ∨ P = (PBias (pw x) (lw α) h).toPatch.swap},
      P.swap ∈ {P : PatchProp | ∃ x α h : ℚ,
        P = (PBias (pw x) (lw α) h).toPatch ∨ P = (PBias (pw x) (lw α) h).toPatch.swap} := by
    intro P hP
    rcases hP with ⟨x, α, h, hP⟩
    rcases hP with hP | hP
    · subst P
      exact ⟨x, α, h, Or.inr rfl⟩
    · subst P
      exact ⟨x, α, h, Or.inl (swap_swap _)⟩
  have hCluster : ∀ P ∈ {P : PatchProp | ∃ (G : Colour) (ζ δ : ℚ),
      P = PCluster G ζ δ ∨ P = (PCluster G ζ δ).swap},
      P.swap ∈ {P : PatchProp | ∃ (G : Colour) (ζ δ : ℚ),
        P = PCluster G ζ δ ∨ P = (PCluster G ζ δ).swap} := by
    intro P hP
    rcases hP with ⟨G, ζ, δ, hP⟩
    rcases hP with hP | hP
    · subst P
      exact ⟨G, ζ, δ, Or.inr rfl⟩
    · subst P
      exact ⟨G, ζ, δ, Or.inl (swap_swap _)⟩
  intro P hP
  simp only [FamB, Set.mem_union] at hP ⊢
  rcases hP with hP | hP
  · rcases hP with hP | hP
    · rcases hP with hP | hP
      · rcases hP with hP | hP
        · exact Or.inl (Or.inl (Or.inl (Or.inl (hViol P hP))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr (hPure P hP))))
      · exact Or.inl (Or.inl (Or.inr (hBiasPP P hP)))
    · exact Or.inl (Or.inr (hBiasPL P hP))
  · exact Or.inr (hCluster P hP)

/-! ## Regime predicates (Definition 9.1 without limits) -/

def AvP (T : Stage) (x y h : ℝ) : Prop := Available T (PBias (pw x) (pw y) h).toPatch
def AvL (T : Stage) (x α h : ℝ) : Prop := Available T (PBias (pw x) (lw α) h).toPatch

/-- `H† < 1`. -/
def HdagLtOne (T : Stage) : Prop :=
  ∃ h₁ : ℚ, h₁ < 1 ∧ ∀ x : ℚ, 0 < x → x < 1 → ∃ y : ℚ, 0 < y ∧ y < 1 ∧ AvP T x y h₁

/-- `H_L† < 1`. -/
def HLdagLtOne (T : Stage) : Prop :=
  ∃ h₁ : ℚ, h₁ < 1 ∧ ∀ x α : ℚ, 0 < x → x < 1 → 0 < α → AvL T x α h₁

/-- `H_L† = 0`. -/
def HLdagZero (T : Stage) : Prop :=
  ∀ x α h : ℚ, 0 < x → x < 1 → 0 < α → 0 < h → AvL T x α h

/-- The capped limiting-exponent function `min(H(x,y), 2)` used for parameter selection. -/
noncomputable def Hpow (T : Stage) (x y : ℝ) : ℝ :=
  sInf ({h : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = h ∧ AvP T x y q} ∪ {2})

noncomputable def Hlin (T : Stage) (x α : ℝ) : ℝ :=
  sInf ({h : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = h ∧ AvL T x α q} ∪ {2})

/-- `τ(η₀) = min(η₀/2, .04)/4` of Section 8. -/
noncomputable def tau8 (η₀ : ℝ) : ℝ := min (η₀ / 2) (4 / 100) / 4

end HypercubeRamsey
