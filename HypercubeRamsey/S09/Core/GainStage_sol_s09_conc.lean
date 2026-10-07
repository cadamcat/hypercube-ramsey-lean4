import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.S09.Core.GainStage_q_s09_gain2
import HypercubeRamsey.S03.Clock.Steps_p_clock_r4
import HypercubeRamsey.Tools.Finner
import HypercubeRamsey.Tools.Concentration

namespace HypercubeRamsey.Lane_sol_s09_conc

open HypercubeRamsey OAI.HypercubeRamsey Classical
open scoped BigOperators

set_option maxHeartbeats 600000

/-- A lower tail for bounded functions whose scopes read each product coordinate at most `d` times. -/
theorem scoped_lower_tail {ι B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype B] [DecidableEq B] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (Q : ∀ i, FinProb (Ω i)) (scope : B → Finset ι) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ i, (Finset.univ.filter (fun b => i ∈ scope b)).card ≤ d)
    (X : B → (∀ i, Ω i) → ℝ) (hscope : ∀ b, FinProb.DependsOn (X b) (scope b))
    (lo hi t : ℝ) (hlohi : lo < hi) (hX : ∀ b ω, lo ≤ X b ω ∧ X b ω ≤ hi)
    (hB : 0 < Fintype.card B) (ht : 0 < t) :
    (FinProb.pi Q).pr (fun ω => ∑ b, X b ω ≤
      ∑ b, (FinProb.pi Q).expect (X b) - t) ≤
      Real.exp (-(2 * t ^ 2 / ((d : ℝ) * Fintype.card B * (hi - lo) ^ 2))) := by
  let R := FinProb.pi Q
  let V : ℝ := (d : ℝ) * Fintype.card B * (hi - lo) ^ 2
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hBR : 0 < (Fintype.card B : ℝ) := by exact_mod_cast hB
  have hV : 0 < V := by dsimp [V]; positivity
  let Z : (∀ i, Ω i) → ℝ := fun ω => ∑ b, (R.expect (X b) - X b ω)
  have hmgf (r : ℝ) : R.expect (fun ω => Real.exp (r * Z ω)) ≤
      Real.exp (r ^ 2 * V / 8) := by
    let f : B → (∀ i, Ω i) → ℝ := fun b ω => Real.exp (r * (R.expect (X b) - X b ω))
    have hf := xFinner Q scope d hd hdegree f
      (fun b ω => Real.exp_nonneg _) (by
        intro b ω ω' h
        dsimp [f]
        rw [hscope b ω ω' h])
    have hlocal (b : B) : Real.rpow (R.expect (fun ω => (f b ω) ^ d)) (d : ℝ)⁻¹ ≤
        Real.exp (r ^ 2 * (d : ℝ) * (hi - lo) ^ 2 / 8) := by
      have hh := xHoeffdingLemma R (X b) lo hi (-((d : ℝ) * r)) hlohi.le (hX b)
      have hpow : R.expect (fun ω => (f b ω) ^ d) ≤
          Real.exp (((d : ℝ) * r) ^ 2 * (hi - lo) ^ 2 / 8) := by
        convert hh using 1
        · congr 1
          funext ω
          dsimp [f]
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        · congr 1
          ring
      have hnonneg : 0 ≤ R.expect (fun ω => (f b ω) ^ d) := by
        apply Finset.sum_nonneg
        intro ω hω
        exact mul_nonneg (R.nonneg ω) (pow_nonneg (Real.exp_nonneg _) _)
      calc
        _ ≤ Real.rpow (Real.exp (((d : ℝ) * r) ^ 2 * (hi - lo) ^ 2 / 8)) (d : ℝ)⁻¹ :=
          Real.rpow_le_rpow hnonneg hpow (by positivity)
        _ = _ := by
          rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1
          field_simp [ne_of_gt hdR]
    calc
      R.expect (fun ω => Real.exp (r * Z ω)) = R.expect (fun ω => ∏ b, f b ω) := by
        congr 1
        funext ω
        dsimp [Z, f]
        rw [Finset.mul_sum, Real.exp_sum]
      _ ≤ ∏ b, Real.rpow (R.expect (fun ω => (f b ω) ^ d)) (d : ℝ)⁻¹ := hf
      _ ≤ ∏ _b : B, Real.exp (r ^ 2 * (d : ℝ) * (hi - lo) ^ 2 / 8) := by
        apply Finset.prod_le_prod₀
        · intro b hb
          exact Real.rpow_nonneg (by
            apply Finset.sum_nonneg
            intro ω hω
            exact mul_nonneg (R.nonneg ω) (pow_nonneg (Real.exp_nonneg _) _)) _
        · intro b hb
          exact hlocal b
      _ = Real.exp (r ^ 2 * V / 8) := by
        rw [← Real.exp_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        congr 1
        dsimp [V]
        ring
  let r : ℝ := 4 * t / V
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hevent : (fun ω => ∑ b, X b ω ≤ ∑ b, R.expect (X b) - t) =
      (fun ω => t ≤ Z ω) := by
    funext ω
    apply propext
    dsimp [Z]
    rw [Finset.sum_sub_distrib]
    constructor <;> intro h <;> linarith
  rw [hevent]
  calc
    R.pr (fun ω => t ≤ Z ω) ≤ Real.exp (-r * t) * R.expect (fun ω => Real.exp (r * Z ω)) :=
      FinProb.pr_exp_markov R Z r t hr
    _ ≤ Real.exp (-r * t) * Real.exp (r ^ 2 * V / 8) :=
      mul_le_mul_of_nonneg_left (hmgf r) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      change -r * t + r ^ 2 * V / 8 = -(2 * t ^ 2 / V)
      dsimp only [r]
      field_simp [ne_of_gt hV]
      ring

private theorem pi_condExp_fiber_set9 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (ω₀ : ∀ i, Ω i) (f : (∀ i, Ω i) → ℝ) (A : (∀ i, Ω i) → Prop)
    (hA : ∀ ω, A ω ↔ ∀ j : {j // j ∈ s}, ω j.1 = ω₀ j.1)
    (hpos : 0 < (FinProb.pi P).pr A) :
    (FinProb.pi P).condExp f A =
      ∑ b : ∀ j : {j // j ∉ s}, Ω j.1,
        (FinProb.pi (fun j : {j // j ∉ s} => P j.1)).w b *
          f ((Equiv.piEquivPiSubtypeProd (fun j => j ∈ s) Ω).symm
            ((fun j : {j // j ∈ s} => ω₀ j.1), b)) := by
  classical
  let J := {j // j ∈ s}
  let K := {j // j ∉ s}
  let a₀ : ∀ j : J, Ω j.1 := fun j => ω₀ j.1
  let Ps : FinProb (∀ j : J, Ω j.1) := FinProb.pi (fun j : J => P j.1)
  let Pc : FinProb (∀ j : K, Ω j.1) := FinProb.pi (fun j : K => P j.1)
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ s) Ω
  have heval (a : ∀ j : J, Ω j.1) (b : ∀ j : K, Ω j.1) (j : J) :
      e.symm (a, b) j.1 = a j := by
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply]
  have heval₀ (b : ∀ j : K, Ω j.1) (j : J) :
      e.symm (a₀, b) j.1 = ω₀ j.1 := by
    simpa [a₀] using heval a₀ b j
  have hFiber (a : ∀ j : J, Ω j.1) (b : ∀ j : K, Ω j.1) :
      (∀ j : J, e.symm (a, b) j.1 = ω₀ j.1) ↔ a = a₀ := by
    constructor
    · intro h
      funext j
      calc
        a j = e.symm (a, b) j.1 := (heval a b j).symm
        _ = ω₀ j.1 := h j
        _ = a₀ j := rfl
    · intro h j
      calc
        e.symm (a, b) j.1 = a j := heval a b j
        _ = a₀ j := congrFun h j
        _ = ω₀ j.1 := rfl
  have hind (a : ∀ j : J, Ω j.1) (b : ∀ j : K, Ω j.1) :
      (if A (e.symm (a, b)) then 1 else 0) = if a = a₀ then 1 else 0 := by
    have hiff : A (e.symm (a, b)) ↔ a = a₀ := (hA _).trans (hFiber a b)
    by_cases h : a = a₀
    · subst a
      have htrue : A (e.symm (a₀, b)) := (hA _).2 (fun j => heval₀ b j)
      simp [htrue]
    · have hfalse : ¬ A (e.symm (a, b)) := fun h' => h (hiff.mp h')
      simp [h, hfalse]
  have hden : (FinProb.pi P).pr A = Ps.w a₀ := by
    calc
      (FinProb.pi P).pr A = (FinProb.pi P).expect (fun ω => if A ω then 1 else 0) := by
        simp [FinProb.pr, FinProb.expect]
      _ = ∑ a : ∀ j : J, Ω j.1, ∑ b : ∀ j : K, Ω j.1,
            Ps.w a * Pc.w b * (if A (e.symm (a, b)) then 1 else 0) :=
          Clock.pi_expect_split_p_clock_r4 P s (fun ω => if A ω then 1 else 0)
      _ = Ps.w a₀ := by
        rw [Finset.sum_comm]
        calc
          (∑ b : ∀ j : K, Ω j.1, ∑ a : ∀ j : J, Ω j.1,
              Ps.w a * Pc.w b * (if A (e.symm (a, b)) then 1 else 0)) =
              ∑ b, Ps.w a₀ * Pc.w b := by
            apply Finset.sum_congr rfl
            intro b hb
            calc
              (∑ a : ∀ j : J, Ω j.1,
                  Ps.w a * Pc.w b * (if A (e.symm (a, b)) then 1 else 0)) =
                  ∑ a, Ps.w a * Pc.w b * (if a = a₀ then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro a ha
                by_cases h : a = a₀
                · subst a
                  have htrue : A (e.symm (a₀, b)) := (hA _).2 (fun j => heval₀ b j)
                  simp [htrue]
                · have hfalse : ¬ A (e.symm (a, b)) := fun h' => h ((hA _).1 h' |> fun hcoords => by
                    funext j
                    exact (heval a b j).symm.trans (hcoords j))
                  simp [hfalse, h]
              _ = Ps.w a₀ * Pc.w b := by
                rw [Finset.sum_eq_single_of_mem a₀ (Finset.mem_univ _) (by
                  intro a ha hne
                  simp [hne])]
                simp
          _ = Ps.w a₀ := by rw [← Finset.mul_sum, Pc.sum_eq_one, mul_one]
  have hnum :
      (FinProb.pi P).expect (fun ω => (if A ω then 1 else 0) * f ω) =
        Ps.w a₀ * ∑ b : ∀ j : K, Ω j.1, Pc.w b * f (e.symm (a₀, b)) := by
    calc
      (FinProb.pi P).expect (fun ω => (if A ω then 1 else 0) * f ω) =
          ∑ a : ∀ j : J, Ω j.1, ∑ b : ∀ j : K, Ω j.1,
            Ps.w a * Pc.w b * ((if A (e.symm (a, b)) then 1 else 0) * f (e.symm (a, b))) :=
        Clock.pi_expect_split_p_clock_r4 P s
          (fun ω => (if A ω then 1 else 0) * f ω)
      _ = Ps.w a₀ * ∑ b : ∀ j : K, Ω j.1, Pc.w b * f (e.symm (a₀, b)) := by
        rw [Finset.sum_comm]
        calc
          (∑ b : ∀ j : K, Ω j.1, ∑ a : ∀ j : J, Ω j.1,
              Ps.w a * Pc.w b * ((if A (e.symm (a, b)) then 1 else 0) * f (e.symm (a, b)))) =
              ∑ b, Ps.w a₀ * (Pc.w b * f (e.symm (a₀, b))) := by
            apply Finset.sum_congr rfl
            intro b hb
            calc
              (∑ a : ∀ j : J, Ω j.1,
                  Ps.w a * Pc.w b * ((if A (e.symm (a, b)) then 1 else 0) * f (e.symm (a, b)))) =
                  ∑ a, Ps.w a * Pc.w b * ((if a = a₀ then 1 else 0) * f (e.symm (a, b))) := by
                apply Finset.sum_congr rfl
                intro a ha
                by_cases h : a = a₀
                · subst a
                  have htrue : A (e.symm (a₀, b)) := (hA _).2 (fun j => heval₀ b j)
                  simp [htrue]
                · have hfalse : ¬ A (e.symm (a, b)) := fun h' => h ((hA _).1 h' |> fun hcoords => by
                    funext j
                    exact (heval a b j).symm.trans (hcoords j))
                  simp [hfalse, h]
              _ = Ps.w a₀ * (Pc.w b * f (e.symm (a₀, b))) := by
                rw [Finset.sum_eq_single_of_mem a₀ (Finset.mem_univ _) (by
                  intro a ha hne
                  simp [hne])]
                simp
                ring
          _ = Ps.w a₀ * ∑ b : ∀ j : K, Ω j.1, Pc.w b * f (e.symm (a₀, b)) := by
            rw [← Finset.mul_sum]
  have hPs : 0 < Ps.w a₀ := by rw [← hden]; exact hpos
  rw [FinProb.condExp, hnum, hden]
  calc
    Ps.w a₀ * (∑ b, Pc.w b * f (e.symm (a₀, b))) / Ps.w a₀ =
        ∑ b, Pc.w b * f (e.symm (a₀, b)) := by field_simp [ne_of_gt hPs]
    _ = ∑ b : ∀ j : {j // j ∉ s}, Ω j.1,
          (FinProb.pi (fun j : {j // j ∉ s} => P j.1)).w b *
            f ((Equiv.piEquivPiSubtypeProd (fun j => j ∈ s) Ω).symm
              ((fun j : {j // j ∈ s} => ω₀ j.1), b)) := by
        rfl


noncomputable def coreCoords9 {P : Params9} {n : ℕ} (I : IDMap9 P n) (v : EvenSites9 n) :
    Finset (I.ID ⊕ OddSites9 n) := (I.core v.1).image Sum.inl

abbrev FreeCoord9 {P : Params9} {n : ℕ} (I : IDMap9 P n) (v : EvenSites9 n) :=
  {j : I.ID ⊕ OddSites9 n // j ∉ coreCoords9 I v}

noncomputable def splice9 {P : Params9} {n N : ℕ} (I : IDMap9 P n) (v : EvenSites9 n)
    (ω₀ : Outcome9 I N) (ξ : ∀ j : FreeCoord9 I v, Val9 I N j.1) : Outcome9 I N :=
  (Equiv.piEquivPiSubtypeProd (fun j => j ∈ coreCoords9 I v) (Val9 I N)).symm
    ((fun j => ω₀ j.1), ξ)

theorem splice_core9 {P : Params9} {n N : ℕ} (I : IDMap9 P n) (v : EvenSites9 n)
    (ω₀ : Outcome9 I N) (ξ : ∀ j : FreeCoord9 I v, Val9 I N j.1)
    (c : I.ID) (hc : c ∈ I.core v.1) : anc9 (splice9 I v ω₀ ξ) c = anc9 ω₀ c := by
  have hj : (Sum.inl c : I.ID ⊕ OddSites9 n) ∈ coreCoords9 I v := by
    simp [coreCoords9, hc]
  simp [anc9, splice9, Equiv.piEquivPiSubtypeProd_symm_apply, hj]
  rfl

theorem splice_free9 {P : Params9} {n N : ℕ} (I : IDMap9 P n) (v : EvenSites9 n)
    (ω₀ : Outcome9 I N) (ξ : ∀ j : FreeCoord9 I v, Val9 I N j.1) (j : FreeCoord9 I v) :
    splice9 I v ω₀ ξ j.1 = ξ j := by
  simp [splice9, Equiv.piEquivPiSubtypeProd_symm_apply, j.2]

/-- Conditioning on a positive core fiber leaves the complementary inputs independent. -/
theorem core_condExp9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n) (ω₀ : Outcome9 I N)
    (hpos : 0 < (rawLaw9 S I).pr (sameCore9 I v ω₀)) (f : Outcome9 I N → ℝ) :
    (rawLaw9 S I).condExp f (sameCore9 I v ω₀) =
      (FinProb.pi (fun j : FreeCoord9 I v => inputLaw9 S I j.1)).expect
        (fun ξ => f (splice9 I v ω₀ ξ)) := by
  have hA (ω : Outcome9 I N) : sameCore9 I v ω₀ ω ↔
      ∀ j : {j // j ∈ coreCoords9 I v}, ω j.1 = ω₀ j.1 := by
    constructor
    · intro h j
      rcases Finset.mem_image.mp j.2 with ⟨c, hc, hcoord⟩
      have j' : j = ⟨Sum.inl c, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩ :=
        Subtype.ext hcoord.symm
      rw [j']
      exact h c hc
    · intro h c hc
      exact h ⟨Sum.inl c, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  exact pi_condExp_fiber_set9 (inputLaw9 S I) (coreCoords9 I v) ω₀ f
    (sameCore9 I v ω₀) hA hpos

noncomputable def rowScope9 {P : Params9} {n : ℕ} (I : IDMap9 P n) (v : EvenSites9 n)
    (b : StarOdd9 v) : Finset (FreeCoord9 I v) :=
  Finset.univ.filter (fun j => match j.1 with
    | .inl c => c ∈ I.seen b.1.1
    | .inr b' => b' = b.1)

theorem rowScope_degree9 {P : Params9} {n : ℕ} (I : IDMap9 P n) (v : EvenSites9 n)
    (j : FreeCoord9 I v) :
    (Finset.univ.filter (fun b : StarOdd9 v => j ∈ rowScope9 I v b)).card ≤ P.radius n + 3 := by
  rcases j with ⟨j, hj⟩
  cases j with
  | inl c =>
    have hc : c ∉ I.core v.1 := by simpa [coreCoords9] using hj
    have hcount :
        (Finset.univ.filter (fun b : StarOdd9 v =>
          (⟨Sum.inl c, hj⟩ : FreeCoord9 I v) ∈ rowScope9 I v b)).card ≤
        (Finset.univ.filter (fun b : CubeVertex n =>
          (cube n).Adj v.1 b ∧ c ∈ seenIDs9 I.center b)).card := by
      apply Finset.card_le_card_of_injOn (fun b : StarOdd9 v => b.1.1)
      · intro b hb
        have hseen : c ∈ I.seen b.1.1 := by simpa [rowScope9] using hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2, hseen⟩
      · intro b hb b' hb' he
        exact Subtype.ext (Subtype.ext he)
    exact hcount.trans (I.read_bound v.1 v.2 c hc)
  | inr b₀ =>
    have hcount :
        (Finset.univ.filter (fun b : StarOdd9 v =>
          (⟨Sum.inr b₀, hj⟩ : FreeCoord9 I v) ∈ rowScope9 I v b)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro b hb b' hb'
      have h : b₀ = b.1 := by simpa [rowScope9] using hb
      have h' : b₀ = b'.1 := by simpa [rowScope9] using hb'
      exact Subtype.ext (h.symm.trans h')
    omega

theorem clipped_scope9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (ω₀ : Outcome9 I N) (b : StarOdd9 v) :
    FinProb.DependsOn (fun ξ => clippedFrac9 S E G (splice9 I v ω₀ ξ) v b.1)
      (rowScope9 I v b) := by
  intro ξ ξ' h
  have hAnc (c : I.ID) (hc : c ∈ I.seen b.1.1) :
      anc9 (splice9 I v ω₀ ξ) c = anc9 (splice9 I v ω₀ ξ') c := by
    by_cases hcore : c ∈ I.core v.1
    · rw [splice_core9 I v ω₀ ξ c hcore, splice_core9 I v ω₀ ξ' c hcore]
    · have hj : (Sum.inl c : I.ID ⊕ OddSites9 n) ∉ coreCoords9 I v := by
        simpa [coreCoords9] using hcore
      change splice9 I v ω₀ ξ (Sum.inl c) = splice9 I v ω₀ ξ' (Sum.inl c)
      rw [splice_free9 I v ω₀ ξ ⟨Sum.inl c, hj⟩,
        splice_free9 I v ω₀ ξ' ⟨Sum.inl c, hj⟩]
      exact h ⟨Sum.inl c, hj⟩ (by simp [rowScope9, hc])
  have hMask : msk9 (splice9 I v ω₀ ξ) b.1 = msk9 (splice9 I v ω₀ ξ') b.1 := by
    have hj : (Sum.inr b.1 : I.ID ⊕ OddSites9 n) ∉ coreCoords9 I v := by
      simp [coreCoords9]
    change splice9 I v ω₀ ξ (Sum.inr b.1) = splice9 I v ω₀ ξ' (Sum.inr b.1)
    rw [splice_free9 I v ω₀ ξ ⟨Sum.inr b.1, hj⟩,
      splice_free9 I v ω₀ ξ' ⟨Sum.inr b.1, hj⟩]
    exact h ⟨Sum.inr b.1, hj⟩ (by simp [rowScope9])
  have hTarget : anc9 (splice9 I v ω₀ ξ) (I.center v.1) =
      anc9 (splice9 I v ω₀ ξ') (I.center v.1) := by
    rw [splice_core9 I v ω₀ ξ _ (I.center_mem_core v.1 v.2),
      splice_core9 I v ω₀ ξ' _ (I.center_mem_core v.1 v.2)]
  have hHits : hitSet9 E G (splice9 I v ω₀ ξ) ((I.seen b.1.1).erase (I.center v.1)) =
      hitSet9 E G (splice9 I v ω₀ ξ') ((I.seen b.1.1).erase (I.center v.1)) := by
    ext y
    simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro hy c hc
    · rw [← hAnc c (Finset.mem_of_mem_erase hc)]
      exact hy c hc
    · rw [hAnc c (Finset.mem_of_mem_erase hc)]
      exact hy c hc
  simp only [clippedFrac9, targetFrac9, delLaw9, maskedLaw9, hTarget, hMask, hHits]

theorem gain_concentration9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (hn : 1 ≤ n) (v : EvenSites9 n) (ω₀ : Outcome9 I N) :
    condCorePr9 S I v ω₀ (fun ω =>
      ∑ b : StarOdd9 v, clippedFrac9 S E G ω v b.1 ≤
        ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω₀ - (n : ℝ) * P.aStar n / 10) ≤
      Real.exp (-((n : ℝ) * P.aStar n ^ 2 /
        (800 * ((P.radius n : ℝ) + 3) * P.bStar n ^ 2))) := by
  by_cases hpos : 0 < (rawLaw9 S I).pr (sameCore9 I v ω₀)
  · let Q := fun j : FreeCoord9 I v => inputLaw9 S I j.1
    let R := FinProb.pi Q
    let X : StarOdd9 v → (∀ j : FreeCoord9 I v, Val9 I N j.1) → ℝ :=
      fun b ξ => clippedFrac9 S E G (splice9 I v ω₀ ξ) v b.1
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hb : 0 < P.bStar n := Real.rpow_pos_of_pos hnR _
    have ha : 0 < P.aStar n := by
      dsimp [Params9.aStar]
      positivity
    have hcard : Fintype.card (StarOdd9 v) = n := by
      rw [← Fintype.card_congr (Lane_q_s09_gain2.starCoordEquiv9 v), Fintype.card_fin]
    have hmeans : (∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω₀) =
        ∑ b : StarOdd9 v, R.expect (X b) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact core_condExp9 S I v ω₀ hpos _
    have hprob : condCorePr9 S I v ω₀ (fun ω =>
        ∑ b : StarOdd9 v, clippedFrac9 S E G ω v b.1 ≤
          ∑ b : StarOdd9 v, condCoreMean9 S I E G v b.1 ω₀ - (n : ℝ) * P.aStar n / 10) =
        R.pr (fun ξ => ∑ b, X b ξ ≤ ∑ b, R.expect (X b) - (n : ℝ) * P.aStar n / 10) := by
      unfold condCorePr9
      rw [core_condExp9 S I v ω₀ hpos, hmeans]
      simp [FinProb.expect, FinProb.pr, X, R, Q]
    have htail := scoped_lower_tail Q (rowScope9 I v) (P.radius n + 3) (by omega)
      (rowScope_degree9 I v) X (clipped_scope9 S I E G v ω₀)
      (1 / 2 - 2 * P.bStar n) (1 / 2 + 2 * P.bStar n)
      ((n : ℝ) * P.aStar n / 10) (by linarith)
      (fun b ξ => Lane_q_s09_gain2.clippedFrac9_bounds (splice9 I v ω₀ ξ) v b.1 hb.le)
      (by rw [hcard]; omega) (by positivity)
    rw [hprob]
    calc
      _ ≤ _ := htail
      _ = _ := by
        congr 1
        rw [hcard]
        push_cast
        field_simp [ne_of_gt hnR, ne_of_gt hb,
          show (P.radius n : ℝ) + 3 ≠ 0 from by positivity]
        ring
  · have hz : (rawLaw9 S I).pr (sameCore9 I v ω₀) = 0 :=
      le_antisymm (le_of_not_gt hpos) (FinProb.pr_nonneg _ _)
    simp [condCorePr9, FinProb.condExp, hz, Real.exp_nonneg]

end HypercubeRamsey.Lane_sol_s09_conc
