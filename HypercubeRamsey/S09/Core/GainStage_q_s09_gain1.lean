import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.S03.Clock.Steps_p_clock_r4
import HypercubeRamsey.S05.Clock_q_s05_even
import HypercubeRamsey.S05.Stages_p_s05_h
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Tools.SignedTest
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_q_s09_gain1

open HypercubeRamsey OAI.HypercubeRamsey Classical
open Filter
open scoped BigOperators
open scoped Topology

private theorem nonempty_of_probability {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  classical
  have hpos : 0 < ∑ a, P.w a := by rw [P.sum_eq_one]; norm_num
  obtain ⟨a, ha, hap⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := P.w)
      (by intro a ha; exact P.nonneg a)).mp hpos
  exact ⟨a⟩

private theorem pi_pr_slice_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (i : ι) (F : (∀ i, Ω i) → Prop) (B : ℝ)
    (hbound : ∀ (b : ∀ j : {j // j ≠ i}, Ω j.1),
      (FinProb.pi (fun j : {j // j ∉ ({i} : Finset ι)} => P j.1)).w
        (fun j => b ⟨j.1, by simpa using j.2⟩) ≠ 0 →
      (P i).pr (fun o => F (Function.update (fun j => if h : j = i then
        cast (congrArg Ω h.symm) (Classical.choice (nonempty_of_probability (P i))) else b ⟨j, h⟩)
        i o)) ≤ B) :
    (FinProb.pi P).pr F ≤ B := by
  classical
  let S : Finset ι := {i}
  let J := {j // j ∈ S}
  letI : Unique J := ⟨⟨i, by simp [S]⟩, fun j => by
    apply Subtype.ext
    exact Finset.mem_singleton.mp (by simpa [S] using j.2)⟩
  let j₀ : J := default
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ S) Ω
  let base : ∀ j, Ω j := fun j => Classical.choice (nonempty_of_probability (P j))
  let ωb : (∀ j : {j // j ∉ S}, Ω j.1) → ∀ j, Ω j := fun b j =>
    if h : j = i then cast (congrArg Ω h.symm) (base i)
    else b ⟨j, by simpa [S] using h⟩
  let Ps : FinProb (∀ j : J, Ω j.1) := FinProb.pi (fun j : J => P j.1)
  let Pc : FinProb (∀ j : {j // j ∉ S}, Ω j.1) :=
    FinProb.pi (fun j : {j // j ∉ S} => P j.1)
  have hsplice (a : ∀ j : J, Ω j.1) (b : ∀ j : {j // j ∉ S}, Ω j.1) :
      e.symm (a, b) = Function.update (ωb b) i (a j₀) := by
    funext j
    by_cases hj : j = i
    · subst j
      have hsub : (⟨i, by simp [S]⟩ : J) = j₀ := Subsingleton.elim _ _
      simp [e, S, ωb, Equiv.piEquivPiSubtypeProd]
      change a (⟨i, by simp [S]⟩ : J) = a j₀
      cases hsub
      rfl
    · simp [Function.update, hj, e, S, ωb, Equiv.piEquivPiSubtypeProd_symm_apply]
  have hweight (a : ∀ j : J, Ω j.1) : Ps.w a = (P i).w (a j₀) := by
    change (∏ j : J, (P j.1).w (a j)) = _
    simp [J, j₀, S]
  have hinner (b : ∀ j : {j // j ∉ S}, Ω j.1) :
      Pc.w b *
          (∑ a : ∀ j : J, Ω j.1, Ps.w a *
            (if F (Function.update (ωb b) i (a j₀)) then 1 else 0)) ≤ Pc.w b * B := by
    let ea : (∀ j : J, Ω j.1) ≃ Ω i := Equiv.piUnique (fun j : J => Ω j.1)
    have heval (o : Ω i) : (ea.symm o) j₀ = o := by
      simp [ea, j₀]
    have hsum :
        (∑ a : ∀ j : J, Ω j.1, Ps.w a * (if F (Function.update (ωb b) i (a j₀)) then 1 else 0)) =
          (P i).pr (fun o => F (Function.update (ωb b) i o)) := by
      rw [← Equiv.sum_comp ea.symm]
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro o ho
      rw [hweight (ea.symm o), heval o]
      by_cases hF : F (Function.update (ωb b) i o) <;> simp [hF]
    let b' : ∀ j : {j // j ≠ i}, Ω j.1 := fun j => b ⟨j.1, by simpa [S] using j.2⟩
    by_cases hb : Pc.w b = 0
    · simp [hb]
    · have hb' :
          (FinProb.pi (fun j : {j // j ∉ ({i} : Finset ι)} => P j.1)).w
            (fun j => b' ⟨j.1, by simpa using j.2⟩) ≠ 0 := by
        simpa [Pc, S, b'] using hb
      have hbnd := hbound b' hb'
      rw [hsum]
      have hPc : Pc.w b =
          (FinProb.pi (fun j : {j // j ∉ ({i} : Finset ι)} => P j.1)).w
            (fun j => b' ⟨j.1, by simpa using j.2⟩) := by
        simp [Pc, S, b']
      rw [hPc]
      simpa [ωb, base, b', S] using mul_le_mul_of_nonneg_left hbnd (Pc.nonneg b)
  have hsplit := Clock.pi_expect_split_p_clock_r4 P S (fun ω => if F ω then 1 else 0)
  have hprob : (FinProb.pi P).pr F =
      ∑ a : ∀ j : J, Ω j.1, ∑ b : ∀ j : {j // j ∉ S}, Ω j.1,
        Ps.w a * Pc.w b * (if F (e.symm (a, b)) then 1 else 0) := by
    calc
      (FinProb.pi P).pr F = (FinProb.pi P).expect (fun ω => if F ω then 1 else 0) := by
        simp [FinProb.pr, FinProb.expect]
      _ = _ := hsplit
  rw [hprob]
  calc
    (∑ a, ∑ b, Ps.w a * Pc.w b * (if F (e.symm (a, b)) then 1 else 0)) =
        ∑ b, Pc.w b * ∑ a, Ps.w a * (if F (Function.update (ωb b) i (a j₀)) then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [hsplice]
          ring
    _ ≤ ∑ b, Pc.w b * B := by
          apply Finset.sum_le_sum
          intro b hb
          exact hinner b
    _ = B := by simp [← Finset.sum_mul, Pc.sum_eq_one]

private theorem condExp_eq_condLaw_expect9 {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (hA : 0 < P.pr A) (f : Ω → ℝ) :
    P.condExp f A = (P.cond A hA).expect f := by
  unfold FinProb.condExp FinProb.expect FinProb.cond
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h] <;> ring

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

private theorem condCoreMean_fiber_formula9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (b : OddSites9 n) (ω₀ : Outcome9 I N)
    (hpos : 0 < (rawLaw9 S I).pr (sameCore9 I v ω₀)) :
    condCoreMean9 S I E G v b ω₀ =
      ∑ ξ : ∀ j : {j // j ∉ (I.core v.1).image Sum.inl}, Val9 I N j.1,
        (FinProb.pi (fun j : {j // j ∉ (I.core v.1).image Sum.inl} => inputLaw9 S I j.1)).w ξ *
          clippedFrac9 S E G
            ((Equiv.piEquivPiSubtypeProd
              (fun j => j ∈ (I.core v.1).image Sum.inl)
              (fun j => Val9 I N j)).symm
              ((fun j : {j // j ∈ (I.core v.1).image Sum.inl} => ω₀ j.1), ξ)) v b := by
  classical
  let s : Finset (I.ID ⊕ OddSites9 n) := (I.core v.1).image Sum.inl
  have hA (ω : Outcome9 I N) :
      sameCore9 I v ω₀ ω ↔ ∀ j : {j // j ∈ s}, ω j.1 = ω₀ j.1 := by
    constructor
    · intro h j
      rcases Finset.mem_image.mp j.2 with ⟨c, hc, hcoord⟩
      have j' : j = ⟨Sum.inl c, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩ :=
        Subtype.ext hcoord.symm
      rw [j']
      change ω (Sum.inl c) = ω₀ (Sum.inl c)
      exact h c hc
    · intro h c hc
      have hj : (Sum.inl c : I.ID ⊕ OddSites9 n) ∈ s := by
        exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
      have := h ⟨Sum.inl c, hj⟩
      change anc9 ω c = anc9 ω₀ c at this
      exact this
  have hformula := pi_condExp_fiber_set9 (inputLaw9 S I) s ω₀
    (fun ω => clippedFrac9 S E G ω v b) (sameCore9 I v ω₀) hA hpos
  simpa [condCoreMean9, rawLaw9, s] using hformula

private theorem raw_anchor_hit_probability9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ids : Finset I.ID) (y : Fin N) :
    (rawLaw9 S I).pr (fun ω => ∀ c ∈ ids, Hits E G (anc9 ω c) y) =
      ∏ i : I.ID ⊕ OddSites9 n,
        (inputLaw9 S I i).pr (fun x =>
          match i with
          | Sum.inl c => if c ∈ ids then Hits E G x y else True
          | Sum.inr _ => True) := by
  classical
  let C : ∀ i : I.ID ⊕ OddSites9 n, Val9 I N i → Prop
    | Sum.inl c, x => if c ∈ ids then Hits E G x y else True
    | Sum.inr _, _ => True
  have hevent :
      (fun ω : Outcome9 I N => ∀ c ∈ ids, Hits E G (anc9 ω c) y) =
        fun ω => ∀ i, C i (ω i) := by
    funext ω
    apply propext
    constructor
    · intro h i
      cases i with
      | inl c =>
          by_cases hc : c ∈ ids
          · simpa [C, hc, anc9] using h c hc
          · simp [C, hc]
      | inr b => simp [C]
    · intro h c hc
      have h' := h (Sum.inl c)
      simpa [C, hc, anc9] using h'
  rw [hevent, rawLaw9]
  exact FinProb.pi_pr_forall (inputLaw9 S I) C

theorem conditional_history_markov9 {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] (P : FinProb Ω) (history : Ω → ι) (A : Ω → Prop)
    (t : ℝ) (ht : 0 < t) :
    P.pr (fun ω₀ => t < P.condExp (fun ω => if A ω then 1 else 0)
      (fun ω => history ω = history ω₀)) ≤ P.pr A / t := by
  classical
  let Q : FinProb ι := FinProb.map P history
  let fiber : ι → Ω → Prop := fun a ω => history ω = a
  let fiberInd : ι → Ω → ℝ := fun a ω =>
    @ite ℝ (fiber a ω) (Classical.propDecidable (fiber a ω)) 1 0
  let q : ι → ℝ := fun a => P.condExp (fun ω => if A ω then 1 else 0) (fiber a)
  have hQw (a : ι) : Q.w a = P.pr (fun ω => history ω = a) := by
    change (∑ ω, if history ω = a then P.w ω else 0) = _
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro ω _
    simp
  have hmapPr (B : ι → Prop) :
      P.pr (fun ω => B (history ω)) = Q.pr B := by
    change (∑ ω, if B (history ω) then P.w ω else 0) =
      ∑ a, if B a then ∑ ω, if history ω = a then P.w ω else 0 else 0
    calc
      (∑ ω, if B (history ω) then P.w ω else 0) =
          ∑ ω, ∑ a, if B a ∧ history ω = a then P.w ω else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [Finset.sum_eq_single_of_mem (history ω) (Finset.mem_univ _) (by
          intro a _ hne
          have hne' : history ω ≠ a := fun he => hne he.symm
          simp [hne'])]
        simp
      _ = ∑ a, ∑ ω, if B a ∧ history ω = a then P.w ω else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ a, if B a then ∑ ω, if history ω = a then P.w ω else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hB : B a <;> simp [hB]
  have hpr_nonneg (B : Ω → Prop) : 0 ≤ P.pr B := by
    unfold FinProb.pr
    apply Finset.sum_nonneg
    intro ω _
    split_ifs <;> positivity [P.nonneg ω]
  have hqnonneg (a : ι) : 0 ≤ q a := by
    dsimp [q, FinProb.condExp, FinProb.expect]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro ω _
      exact mul_nonneg (P.nonneg ω) (by split_ifs <;> norm_num)
    · exact hpr_nonneg _
  have hfiber (a : ι) : Q.w a * q a = P.pr (fun ω => history ω = a ∧ A ω) := by
    rw [hQw a]
    simp only [q, FinProb.condExp]
    change P.pr (fiber a) *
      (P.expect (fun ω => fiberInd a ω * (if A ω then 1 else 0)) / P.pr (fiber a)) =
        P.pr (fun ω => fiber a ω ∧ A ω)
    have hnum :
        P.expect (fun ω => fiberInd a ω * (if A ω then 1 else 0)) =
          P.pr (fun ω => fiber a ω ∧ A ω) := by
      unfold FinProb.expect FinProb.pr
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hh : history ω = a <;> by_cases ha : A ω <;>
        simp [fiberInd, fiber, hh, ha]
    have hquot : P.pr (fiber a) *
        (P.pr (fun ω => fiber a ω ∧ A ω) / P.pr (fiber a)) =
        P.pr (fun ω => fiber a ω ∧ A ω) := by
      by_cases hp : P.pr (fiber a) = 0
      ·
        have hhit : P.pr (fun ω => fiber a ω ∧ A ω) = 0 := by
          have hle : P.pr (fun ω => fiber a ω ∧ A ω) ≤ P.pr (fiber a) := by
            unfold FinProb.pr
            apply Finset.sum_le_sum
            intro ω _
            by_cases hh : history ω = a <;> by_cases ha : A ω <;>
              simp [fiber, hh, ha, P.nonneg]
          have hnonneg := hpr_nonneg (fun ω => fiber a ω ∧ A ω)
          rw [hp] at hle
          linarith
        rw [hp, hhit]
        norm_num
      ·
        have hp' : 0 < P.pr (fiber a) := lt_of_le_of_ne
          (hpr_nonneg _) (Ne.symm hp)
        field_simp [ne_of_gt hp'] <;> ring
    calc
      P.pr (fiber a) *
          (P.expect (fun ω => fiberInd a ω * (if A ω then 1 else 0)) / P.pr (fiber a)) =
          P.pr (fiber a) *
            (P.pr (fun ω => fiber a ω ∧ A ω) / P.pr (fiber a)) := by
              exact congrArg (fun z => P.pr (fiber a) * (z / P.pr (fiber a))) hnum
      _ = P.pr (fun ω => fiber a ω ∧ A ω) := hquot
  have hexpect : Q.expect q = P.pr A := by
    calc
      (∑ a, Q.w a * q a) = ∑ a, P.pr (fun ω => history ω = a ∧ A ω) := by
        apply Finset.sum_congr rfl
        intro a _
        exact hfiber a
      _ = P.pr A := by
        unfold FinProb.pr
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ω _
        by_cases ha : A ω
        · rw [Finset.sum_eq_single_of_mem (history ω) (Finset.mem_univ _) (by
            intro a _ hne
            have hne' : history ω ≠ a := fun he => hne he.symm
            simp [ha, hne'])]
          simp [ha]
        · simp [ha]
  have hmarkov : Q.pr (fun a => t < q a) ≤ Q.expect q / t := by
    unfold FinProb.pr FinProb.expect
    calc
      (∑ a, if t < q a then Q.w a else 0) ≤
          ∑ a, Q.w a * q a / t := by
        apply Finset.sum_le_sum
        intro a _
        by_cases h : t < q a
        · rw [if_pos h]
          have hq : 0 ≤ q a := hqnonneg a
          have hpnt : Q.w a ≤ Q.w a * q a / t := by
            rw [le_div_iff₀ ht]
            nlinarith [Q.nonneg a, h]
          exact hpnt
        · rw [if_neg h]
          exact div_nonneg (mul_nonneg (Q.nonneg a) (hqnonneg a)) ht.le
      _ = (∑ a, Q.w a * q a) / t := by rw [← Finset.sum_div]
  have hprob : P.pr (fun ω₀ => t < P.condExp (fun ω => if A ω then 1 else 0)
      (fun ω => history ω = history ω₀)) = Q.pr (fun a => t < q a) := by
    change P.pr (fun ω₀ => t < q (history ω₀)) = _
    exact hmapPr (fun a => t < q a)
  calc
    P.pr (fun ω₀ => t < P.condExp (fun ω => if A ω then 1 else 0)
        (fun ω => history ω = history ω₀)) = Q.pr (fun a => t < q a) := hprob
    _ ≤ Q.expect q / t := hmarkov
    _ = P.pr A / t := by rw [hexpect]

theorem core_history_markov9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n)
    (v : EvenSites9 n) (A : Outcome9 I N → Prop) (t : ℝ) (ht : 0 < t) :
    (rawLaw9 S I).pr (fun ω₀ => t < condCorePr9 S I v ω₀ A) ≤
      (rawLaw9 S I).pr A / t := by
  classical
  let hist : Outcome9 I N →
      (∀ c : {c : I.ID // c ∈ I.core v.1}, Fin N) :=
    fun ω c => anc9 ω c.1
  have hrel (ω₀ ω : Outcome9 I N) :
      sameCore9 I v ω₀ ω ↔ hist ω = hist ω₀ := by
    constructor
    · intro h
      funext c
      exact h c.1 c.2
    · intro h c hc
      exact congrFun h ⟨c, hc⟩
  have hpred (ω₀ : Outcome9 I N) :
      sameCore9 I v ω₀ = (fun ω => hist ω = hist ω₀) := by
    funext ω
    exact propext (hrel ω₀ ω)
  have hcond (ω₀ : Outcome9 I N) :
      condCorePr9 S I v ω₀ A =
        (rawLaw9 S I).condExp (fun ω => if A ω then 1 else 0)
          (fun ω => hist ω = hist ω₀) := by
    unfold condCorePr9
    rw [hpred ω₀]
  have hmarkov := conditional_history_markov9 (rawLaw9 S I) hist A t ht
  calc
    (rawLaw9 S I).pr (fun ω₀ => t < condCorePr9 S I v ω₀ A) =
        (rawLaw9 S I).pr (fun ω₀ => t <
          (rawLaw9 S I).condExp (fun ω => if A ω then 1 else 0)
            (fun ω => hist ω = hist ω₀)) := by
              apply congrArg (fun f => (rawLaw9 S I).pr f)
              funext ω₀
              exact congrArg (fun z => t < z) (hcond ω₀)
    _ ≤ (rawLaw9 S I).pr A / t := hmarkov

theorem regularity_core_exception9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hreg : RegularityCert9 S I E G c₀) :
    (rawLaw9 S I).pr (fun ω₀ => P.tail (c₀ / 2) n <
      condCorePr9 S I v ω₀ (fun ω => ¬ starRegular9 S E G ω v)) ≤ P.tail (c₀ / 2) n := by
  let t : ℝ := P.tail (c₀ / 2) n
  have ht : 0 < t := by
    simp [t, Params9.tail]
    exact Real.exp_pos _
  have hmk := core_history_markov9 S I v (fun ω => ¬ starRegular9 S E G ω v) t ht
  have hregular := hreg v
  have hquot : P.tail c₀ n / t = P.tail (c₀ / 2) n := by
    dsimp [t, Params9.tail]
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    (rawLaw9 S I).pr (fun ω₀ => t <
        condCorePr9 S I v ω₀ (fun ω => ¬ starRegular9 S E G ω v)) ≤
        (rawLaw9 S I).pr (fun ω => ¬ starRegular9 S E G ω v) / t := hmk
    _ ≤ P.tail c₀ n / t := div_le_div_of_nonneg_right hregular ht.le
    _ = P.tail (c₀ / 2) n := hquot

private theorem expect_indicator9 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.expect (fun ω => if A ω then 1 else 0) = P.pr A := by
  classical
  unfold FinProb.expect FinProb.pr
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : A ω <;> simp [h]

private theorem expect_const9 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (c : ℝ) :
    P.expect (fun _ => c) = c := by
  unfold FinProb.expect
  calc
    (∑ ω, P.w ω * c) = (∑ ω, P.w ω) * c := by rw [← Finset.sum_mul]
    _ = c := by rw [P.sum_eq_one]; ring

private theorem expect_mono9 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f g : Ω → ℝ)
    (h : ∀ ω, f ω ≤ g ω) : P.expect f ≤ P.expect g := by
  unfold FinProb.expect
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω)

private theorem expect_bad_const9 {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) (c : ℝ) :
    P.expect (fun ω => if A ω then c else 0) = c * P.pr A := by
  classical
  calc
    P.expect (fun ω => if A ω then c else 0) =
        P.expect (fun ω => c * (if A ω then 1 else 0)) := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro ω _
          by_cases h : A ω <;> simp [h]
    _ = c * P.expect (fun ω => if A ω then 1 else 0) := by
          unfold FinProb.expect
          calc
            (∑ ω, P.w ω * (c * (if A ω then 1 else 0))) =
                ∑ ω, c * (P.w ω * (if A ω then 1 else 0)) := by
                  apply Finset.sum_congr rfl
                  intro ω _
                  ring
            _ = c * ∑ ω, P.w ω * (if A ω then 1 else 0) := by
                  rw [← Finset.mul_sum]
    _ = c * P.pr A := by rw [expect_indicator9]

private theorem pr_complement9 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A + P.pr (fun ω => ¬ A ω) = 1 := by
  classical
  unfold FinProb.pr
  calc
    (∑ ω, (@ite ℝ (A ω) (Classical.propDecidable (A ω)) (P.w ω) 0)) +
        ∑ ω, (@ite ℝ (¬ A ω) (Classical.propDecidable (¬ A ω)) (P.w ω) 0) =
        ∑ ω, ((@ite ℝ (A ω) (Classical.propDecidable (A ω)) (P.w ω) 0) +
          (@ite ℝ (¬ A ω) (Classical.propDecidable (¬ A ω)) (P.w ω) 0)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ ω, P.w ω := by
          apply Finset.sum_congr rfl
          intro ω _
          by_cases h : A ω <;> simp [h]
    _ = 1 := P.sum_eq_one

private theorem expect_add9 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f g : Ω → ℝ) :
    P.expect (fun ω => f ω + g ω) = P.expect f + P.expect g := by
  unfold FinProb.expect
  calc
    (∑ ω, P.w ω * (f ω + g ω)) =
        ∑ ω, (P.w ω * f ω + P.w ω * g ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          ring
    _ = (∑ ω, P.w ω * f ω) + ∑ ω, P.w ω * g ω := by
          rw [Finset.sum_add_distrib]

private theorem expect_complement_const9 {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (good : Ω → Prop) (c : ℝ) :
    P.expect (fun ω => if good ω then 0 else c) = c * P.pr (fun ω => ¬ good ω) := by
  classical
  calc
    P.expect (fun ω => if good ω then 0 else c) =
        P.expect (fun ω => @ite ℝ (¬ good ω) (Classical.propDecidable (¬ good ω)) c 0) := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro ω _
          by_cases h : good ω <;> simp [h]
    _ = c * P.pr (fun ω => ¬ good ω) := by
      simpa only [FinProb.pr] using
        (expect_bad_const9 P (fun ω => ¬ good ω) c)

private theorem expect_const_plus_complement9 {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (good : Ω → Prop) (a b : ℝ) :
    P.expect (fun ω => a + (if good ω then 0 else b)) =
      a + b * P.pr (fun ω => ¬ good ω) := by
  rw [expect_add9, expect_const9, expect_complement_const9]

private theorem expect_sub_const9 {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (f : Ω → ℝ) (c : ℝ) :
    P.expect (fun ω => f ω - c) = P.expect f - c := by
  unfold FinProb.expect
  calc
    (∑ ω, P.w ω * (f ω - c)) =
        ∑ ω, (P.w ω * f ω - P.w ω * c) := by
          apply Finset.sum_congr rfl
          intro ω _
          ring
    _ = (∑ ω, P.w ω * f ω) - ∑ ω, P.w ω * c := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ ω, P.w ω * f ω) - c := by
          rw [← Finset.sum_mul, P.sum_eq_one]
          ring

private theorem weighted_expectation_close9 {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (good : Ω → Prop) (z q : Ω → ℝ)
    (z₀ β δ ε : ℝ)
    (hz : ∀ ω, 0 ≤ z ω ∧ z ω ≤ 1) (hq : ∀ ω, 0 ≤ q ω ∧ q ω ≤ 1)
    (hz₀ : 0 < z₀) (hz₀le : z₀ ≤ 1)
    (hβ : 0 ≤ β) (hβle : β ≤ 1 / 2)
    (hδ : 0 ≤ δ) (hδle : δ ≤ 1 / 2)
    (hε : 0 ≤ ε) (hεle : ε ≤ 1 / 2)
    (hbad : P.pr (fun ω => ¬ good ω) ≤ ε)
    (hzgood : ∀ ω, good ω → |z ω - z₀| ≤ δ * z₀)
    (hqclose : ∀ ω, |q ω - 1 / 2| ≤ β) :
    |P.expect q - P.expect (fun ω => z ω * q ω) / P.expect z| ≤
      8 * δ * β + 8 * ε / z₀ := by
  classical
  let ez : ℝ := P.expect z
  let eq : ℝ := P.expect q
  let ezq : ℝ := P.expect (fun ω => z ω * q ω)
  have hbadNonneg : 0 ≤ P.pr (fun ω => ¬ good ω) := by
    unfold FinProb.pr
    apply Finset.sum_nonneg
    intro ω _
    split_ifs <;> positivity [P.nonneg ω]
  have hbadLeOne : P.pr (fun ω => ¬ good ω) ≤ 1 := by
    have hsplit := pr_complement9 P good
    have hgood : 0 ≤ P.pr good := by
      unfold FinProb.pr
      apply Finset.sum_nonneg
      intro ω _
      split_ifs <;> positivity [P.nonneg ω]
    linarith
  have hz0bound (ω : Ω) : |z ω - z₀| ≤ 1 := by
    have hzw := hz ω
    rw [abs_le]
    constructor <;> linarith [hz₀, hz₀le]
  have hpointZ (ω : Ω) : |z ω - z₀| ≤ δ * z₀ + (if good ω then 0 else 1) := by
    by_cases hg : good ω
    · simpa [hg] using hzgood ω hg
    · rw [if_neg hg]
      have := hz0bound ω
      have hδz₀ : 0 ≤ δ * z₀ := mul_nonneg hδ hz₀.le
      linarith
  have hexpZ : P.expect (fun ω => |z ω - z₀|) ≤ δ * z₀ + ε := by
    have hmono := expect_mono9 P (fun ω => |z ω - z₀|)
      (fun ω => δ * z₀ + (if good ω then 0 else 1)) hpointZ
    have hbound : P.expect (fun ω => δ * z₀ + (if good ω then 0 else 1)) =
        δ * z₀ + P.pr (fun ω => ¬ good ω) := by
      simpa using expect_const_plus_complement9 P good (δ * z₀) 1
    rw [hbound] at hmono
    linarith [hbad]
  have hpointC (ω : Ω) :
      |(z ω - z₀) * (q ω - 1 / 2)| ≤ δ * z₀ * β + (if good ω then 0 else β) := by
    by_cases hg : good ω
    · rw [if_pos hg]
      rw [abs_mul]
      simpa using mul_le_mul (hzgood ω hg) (hqclose ω) (abs_nonneg _) (by positivity)
    · rw [if_neg hg]
      rw [abs_mul]
      have hq' : |q ω - 1 / 2| ≤ β := hqclose ω
      have hprod : |z ω - z₀| * |q ω - 1 / 2| ≤ β := by
        calc
          |z ω - z₀| * |q ω - 1 / 2| ≤ 1 * β :=
            mul_le_mul (hz0bound ω) hq' (abs_nonneg _) (by norm_num)
          _ = β := by ring
      linarith [mul_nonneg (mul_nonneg hδ hz₀.le) hβ]
  have hcentProd :
      P.expect (fun ω => |(z ω - z₀) * (q ω - 1 / 2)|) ≤ δ * z₀ * β + ε * β := by
    have hmono := expect_mono9 P
      (fun ω => |(z ω - z₀) * (q ω - 1 / 2)|)
      (fun ω => δ * z₀ * β + (if good ω then 0 else β)) hpointC
    have hbound : P.expect (fun ω => δ * z₀ * β + (if good ω then 0 else β)) =
        δ * z₀ * β + β * P.pr (fun ω => ¬ good ω) := by
      exact expect_const_plus_complement9 P good (δ * z₀ * β) β
    rw [hbound] at hmono
    calc
      P.expect (fun ω => |(z ω - z₀) * (q ω - 1 / 2)|) ≤
          δ * z₀ * β + β * P.pr (fun ω => ¬ good ω) := hmono
      _ ≤ δ * z₀ * β + ε * β := by
            calc
              δ * z₀ * β + β * P.pr (fun ω => ¬ good ω) =
                  β * P.pr (fun ω => ¬ good ω) + δ * z₀ * β := by ring
              _ ≤ β * ε + δ * z₀ * β := add_le_add_left
                    (mul_le_mul_of_nonneg_left hbad hβ) _
              _ = δ * z₀ * β + ε * β := by ring
  have hdenPoint (ω : Ω) : z₀ / 2 * (if good ω then 1 else 0) ≤ z ω := by
    by_cases hg : good ω
    · rw [if_pos hg]
      have h := hzgood ω hg
      have hzlower : z₀ - δ * z₀ ≤ z ω := by
        have := (abs_le.mp h).1
        linarith
      nlinarith [hδle, hzlower]
    · rw [if_neg hg]
      simpa using (hz ω).1
  have hden : z₀ / 4 ≤ ez := by
    have hmono := expect_mono9 P (fun ω => z₀ / 2 * (if good ω then 1 else 0)) z hdenPoint
    have hbase : P.expect (fun ω => z₀ / 2 * (if good ω then 1 else 0)) =
        z₀ / 2 * P.pr good := by
      calc
        P.expect (fun ω => z₀ / 2 * (if good ω then 1 else 0)) =
            z₀ / 2 * P.expect (fun ω => if good ω then 1 else 0) := by
              unfold FinProb.expect
              calc
                (∑ ω, P.w ω * (z₀ / 2 * (if good ω then 1 else 0))) =
                    ∑ ω, z₀ / 2 * (P.w ω * (if good ω then 1 else 0)) := by
                      apply Finset.sum_congr rfl
                      intro ω _
                      ring
                _ = z₀ / 2 * ∑ ω, P.w ω * (if good ω then 1 else 0) := by
                      rw [← Finset.mul_sum]
        _ = z₀ / 2 * P.pr good := by rw [expect_indicator9]
    have hprob : 1 / 2 ≤ P.pr good := by
      have hsplit := pr_complement9 P good
      linarith [hbad, hεle]
    rw [hbase] at hmono
    dsimp [ez]
    nlinarith [hmono, hprob, hz₀]
  have hdenpos : 0 < ez := lt_of_lt_of_le (by positivity) hden
  have hEZcenter : P.expect (fun ω => z ω - z₀) = ez - z₀ := by
    dsimp [ez]
    exact expect_sub_const9 P z z₀
  have hEQcenter : P.expect (fun ω => q ω - 1 / 2) = eq - 1 / 2 := by
    dsimp [eq]
    exact expect_sub_const9 P q (1 / 2)
  have hEcenterProd :
      P.expect (fun ω => (z ω - z₀) * (q ω - 1 / 2)) =
        ezq - z₀ * eq - (1 / 2) * ez + z₀ / 2 := by
    dsimp [ezq, eq, ez]
    unfold FinProb.expect
    calc
      (∑ ω, P.w ω * ((z ω - z₀) * (q ω - 1 / 2))) =
          ∑ ω, (P.w ω * (z ω * q ω) - z₀ * (P.w ω * q ω) -
            (1 / 2) * (P.w ω * z ω) + (z₀ / 2) * P.w ω) := by
              apply Finset.sum_congr rfl
              intro ω _
              ring
      _ = (∑ ω, P.w ω * (z ω * q ω)) - z₀ * (∑ ω, P.w ω * q ω) -
            (1 / 2) * (∑ ω, P.w ω * z ω) + (z₀ / 2) * (∑ ω, P.w ω) := by
              simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = P.expect (fun ω => z ω * q ω) - z₀ * P.expect q -
            (1 / 2) * P.expect z + z₀ / 2 := by
              rw [P.sum_eq_one]
              simp only [FinProb.expect]
              ring
  have hcov : ezq - ez * eq =
      P.expect (fun ω => (z ω - z₀) * (q ω - 1 / 2)) -
        P.expect (fun ω => z ω - z₀) * P.expect (fun ω => q ω - 1 / 2) := by
    rw [hEcenterProd, hEZcenter, hEQcenter]
    ring
  have hcovBound : |ezq - ez * eq| ≤ 2 * δ * z₀ * β + 2 * ε := by
    rw [hcov]
    calc
      |P.expect (fun ω => (z ω - z₀) * (q ω - 1 / 2)) -
          P.expect (fun ω => z ω - z₀) * P.expect (fun ω => q ω - 1 / 2)| ≤
          |P.expect (fun ω => (z ω - z₀) * (q ω - 1 / 2))| +
            |P.expect (fun ω => z ω - z₀) * P.expect (fun ω => q ω - 1 / 2)| := abs_sub _ _
      _ ≤ (δ * z₀ * β + ε * β) + (δ * z₀ + ε) * β := by
          have hA : |P.expect (fun ω => (z ω - z₀) * (q ω - 1 / 2))| ≤
              P.expect (fun ω => |(z ω - z₀) * (q ω - 1 / 2)|) := by
                calc
                  |P.expect (fun ω => (z ω - z₀) * (q ω - 1 / 2))| ≤
                      ∑ ω, |P.w ω * ((z ω - z₀) * (q ω - 1 / 2))| := by
                        simpa [FinProb.expect] using Finset.abs_sum_le_sum_abs
                          (fun ω => P.w ω * ((z ω - z₀) * (q ω - 1 / 2))) Finset.univ
                  _ = P.expect (fun ω => |(z ω - z₀) * (q ω - 1 / 2)|) := by
                        unfold FinProb.expect
                        apply Finset.sum_congr rfl
                        intro ω _
                        rw [abs_mul, abs_of_nonneg (P.nonneg ω)]
          have hB : |P.expect (fun ω => z ω - z₀)| ≤ δ * z₀ + ε := by
            calc
              |P.expect (fun ω => z ω - z₀)| ≤
                  P.expect (fun ω => |z ω - z₀|) := by
                    calc
                      |P.expect (fun ω => z ω - z₀)| ≤
                          ∑ ω, |P.w ω * (z ω - z₀)| := by
                            simpa [FinProb.expect] using Finset.abs_sum_le_sum_abs
                              (fun ω => P.w ω * (z ω - z₀)) Finset.univ
                      _ = P.expect (fun ω => |z ω - z₀|) := by
                            unfold FinProb.expect
                            apply Finset.sum_congr rfl
                            intro ω _
                            rw [abs_mul, abs_of_nonneg (P.nonneg ω)]
              _ ≤ δ * z₀ + ε := hexpZ
          have hC : |P.expect (fun ω => q ω - 1 / 2)| ≤ β := by
            calc
              |P.expect (fun ω => q ω - 1 / 2)| ≤
                  P.expect (fun ω => |q ω - 1 / 2|) := by
                    calc
                      |P.expect (fun ω => q ω - 1 / 2)| ≤
                          ∑ ω, |P.w ω * (q ω - 1 / 2)| := by
                            simpa [FinProb.expect] using Finset.abs_sum_le_sum_abs
                              (fun ω => P.w ω * (q ω - 1 / 2)) Finset.univ
                      _ = P.expect (fun ω => |q ω - 1 / 2|) := by
                            unfold FinProb.expect
                            apply Finset.sum_congr rfl
                            intro ω _
                            rw [abs_mul, abs_of_nonneg (P.nonneg ω)]
              _ ≤ P.expect (fun _ => β) := expect_mono9 P _ _ hqclose
              _ = β := expect_const9 P β
          rw [abs_mul]
          refine add_le_add (hA.trans hcentProd) ?_
          exact mul_le_mul hB hC (abs_nonneg _) (by positivity)
      _ ≤ 2 * δ * z₀ * β + 2 * ε := by
          have hεβ : ε * β ≤ ε := by nlinarith [hε, hβ, hβle]
          nlinarith [hcentProd, hεβ, hδ, hz₀, hβ]
  have hratio : |eq - ezq / ez| = |ezq - ez * eq| / ez := by
    have hnum : eq - ezq / ez = (ez * eq - ezq) / ez := by
      field_simp [ne_of_gt hdenpos]
      
    rw [hnum, abs_div, abs_of_pos hdenpos]
    rw [show ez * eq - ezq = -(ezq - ez * eq) by ring, abs_neg]
  calc
    |P.expect q - P.expect (fun ω => z ω * q ω) / P.expect z| = |eq - ezq / ez| := by
      simp [eq, ezq, ez]
    _ = |ezq - ez * eq| / ez := hratio
    _ ≤ (2 * δ * z₀ * β + 2 * ε) / ez :=
      div_le_div_of_nonneg_right hcovBound hdenpos.le
    _ ≤ (2 * δ * z₀ * β + 2 * ε) / (z₀ / 4) := by
      apply (div_le_div_iff₀ hdenpos (by positivity : 0 < z₀ / 4)).2
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ 8 * δ * β + 8 * ε / z₀ := by
      have hcalc : (2 * δ * z₀ * β + 2 * ε) / (z₀ / 4) =
          8 * δ * β + 8 * ε / z₀ := by
        field_simp [ne_of_gt hz₀]
        ring
      rw [hcalc]

private theorem pi_expect_prod9 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (f : ∀ i, Ω i → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).expect (f i) :=
  FinProb.expect_pi_prod P f

private theorem pi_expect_core_factor9 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (g : (∀ i, Ω i) → ℝ)
    (f : ∀ i : {i // i ∈ s}, Ω i.1 → ℝ)
    (hdep : ∀ ω ω', (∀ i, i ∉ s → ω i = ω' i) → g ω = g ω') :
    (FinProb.pi P).expect (fun ω => g ω * ∏ i : {i // i ∈ s}, f i (ω i.1)) =
      (FinProb.pi P).expect g * ∏ i : {i // i ∈ s}, (P i.1).expect (f i) := by
  classical
  let F : (∀ i, Ω i) → ℝ := fun ω => ∏ i : {i // i ∈ s}, f i (ω i.1)
  have hg : FinProb.DependsOn g (Finset.univ \ s) := by
    intro ω ω' hω
    apply hdep ω ω'
    intro i hi
    exact hω i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)
  have hF : FinProb.DependsOn F s := by
    intro ω ω' hω
    unfold F
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (f i) (hω i.1 i.2)
  have hdis : Disjoint s (Finset.univ \ s) := by
    rw [Finset.disjoint_left]
    intro i hi hnot
    exact (Finset.mem_sdiff.mp hnot).2 hi
  have hmul := FinProb.pi_expect_mul_of_disjoint P F g s (Finset.univ \ s) hF hg hdis
  have hMarginal := FinProb.pi_marginal_expect P s
    (fun a : ∀ i : {i // i ∈ s}, Ω i.1 => ∏ i, f i (a i))
  have hprod : (FinProb.pi P).expect F =
      ∏ i : {i // i ∈ s}, (P i.1).expect (f i) := by
    calc
      (FinProb.pi P).expect F =
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect
            (fun a => ∏ i, f i (a i)) := by
              simpa [F] using hMarginal
      _ = ∏ i : {i // i ∈ s}, (P i.1).expect (f i) :=
            FinProb.expect_pi_prod (fun i : {i // i ∈ s} => P i.1) f
  calc
    (FinProb.pi P).expect (fun ω => g ω * F ω) =
        (FinProb.pi P).expect (fun ω => F ω * g ω) := by
          congr 1
          funext ω
          ring
    _ = (FinProb.pi P).expect F * (FinProb.pi P).expect g := hmul
    _ = (FinProb.pi P).expect g * ∏ i : {i // i ∈ s}, (P i.1).expect (f i) := by
          rw [hprod]
          ring

private theorem outer_filter_core_hit_factor9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (b : OddSites9 n) (y : Fin N) :
    ∃ (s : Finset (I.ID ⊕ OddSites9 n))
      (f : ∀ i : {i // i ∈ s}, Val9 I N i.1 → ℝ),
      s = ((I.seen b.1 ∩ I.core v.1).image Sum.inl) ∧
      (rawLaw9 S I).expect (fun ω => (outerFilter9 S E G ω v b).w y *
        ∏ i : {i // i ∈ s}, f i (ω i.1)) =
        (outerMean9 S I E G v b).w y *
          ∏ i : {i // i ∈ s}, (inputLaw9 S I i.1).expect (f i) := by
  classical
  let D : Finset I.ID := I.seen b.1 ∩ I.core v.1
  let s : Finset (I.ID ⊕ OddSites9 n) := D.image Sum.inl
  let f : ∀ i : {i // i ∈ s}, Val9 I N i.1 → ℝ := fun i x =>
    match i.1, x with
    | Sum.inl _, x => if Hits E G x y then 1 else 0
    | Sum.inr _, _ => 1
  let g : Outcome9 I N → ℝ := fun ω => (outerFilter9 S E G ω v b).w y
  have hmaskNot : Sum.inr b ∉ s := by
    intro hs
    rcases Finset.mem_image.mp hs with ⟨c, hc, hEq⟩
    cases hEq
  have houterNot (c : I.ID) (hc : c ∈ outerIDs9 I v b) : Sum.inl c ∉ s := by
    intro hs
    rcases Finset.mem_image.mp hs with ⟨d, hd, hEq⟩
    have hcd : d = c := by injection hEq
    subst d
    have hcCore : c ∈ I.core v.1 := (Finset.mem_inter.mp hd).2
    have hcNotCore : c ∉ I.core v.1 := (Finset.mem_sdiff.mp hc).2
    exact hcNotCore hcCore
  have hdep : ∀ ω ω', (∀ i, i ∉ s → ω i = ω' i) → g ω = g ω' := by
    intro ω ω' heq
    have hmask : msk9 ω b = msk9 ω' b := by
      exact heq (Sum.inr b) hmaskNot
    have hanc (c : I.ID) (hc : c ∈ outerIDs9 I v b) :
        anc9 ω c = anc9 ω' c := by
      exact heq (Sum.inl c) (houterNot c hc)
    have hset : hitSet9 E G ω (outerIDs9 I v b) =
        hitSet9 E G ω' (outerIDs9 I v b) := by
      ext z
      simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hz c hc
        rw [← hanc c hc]
        exact hz c hc
      · intro hz c hc
        rw [hanc c hc]
        exact hz c hc
    have hmasked : maskedLaw9 S ω b = maskedLaw9 S ω' b := by
      unfold maskedLaw9
      rw [hmask]
    change (outerFilter9 S E G ω v b).w y =
      (outerFilter9 S E G ω' v b).w y
    unfold outerFilter9
    rw [hmasked, hset]
  have hfactor := pi_expect_core_factor9 (inputLaw9 S I) s g f hdep
  refine ⟨s, f, ?_, ?_⟩
  · simp [s, D]
  · calc
      (rawLaw9 S I).expect (fun ω => (outerFilter9 S E G ω v b).w y *
          ∏ i : {i // i ∈ s}, f i (ω i.1)) =
          (FinProb.pi (inputLaw9 S I)).expect (fun ω => g ω *
            ∏ i : {i // i ∈ s}, f i (ω i.1)) := by
              simp [rawLaw9, g]
      _ = (FinProb.pi (inputLaw9 S I)).expect g *
            ∏ i : {i // i ∈ s}, (inputLaw9 S I i.1).expect (f i) := hfactor
      _ = (outerMean9 S I E G v b).w y *
            ∏ i : {i // i ∈ s}, (inputLaw9 S I i.1).expect (f i) := by
              rfl

private noncomputable def regularityOrder9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n)
    (t : Fin 3) : List I.ID :=
  if t.val = 2 then coreOrder9 I v b else fullOrder9 I v b

private noncomputable def regularityBase9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (b : OddSites9 n)
    (ω : Outcome9 I N) (t : Fin 3) : Law N :=
  if t.val = 0 then maskedLaw9 S ω b else siteSecond9 S b.1

private theorem fullOrder_nodup9 {P : Params9} {n : ℕ}
    (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n) : (fullOrder9 I v b).Nodup := by
  classical
  let O := outerIDs9 I v b
  let K := coreIDs9 I v b
  have hdis : Disjoint O K := by
    rw [Finset.disjoint_left]
    intro x hxO hxK
    have hxO' := (Finset.mem_sdiff.mp hxO).2
    have hxK' := (Finset.mem_erase.mp hxK).2
    exact hxO' (Finset.mem_inter.mp hxK').2
  have hO : O.toList.Nodup := Finset.nodup_toList O
  have hK : K.toList.Nodup := Finset.nodup_toList K
  have hcross : ∀ x ∈ O.toList, ∀ y ∈ K.toList, x ≠ y := by
    intro x hx y hy hxy
    subst y
    exact (Finset.disjoint_left.mp hdis) (by simpa using hx) (by simpa using hy)
  have hOK : (O.toList ++ K.toList).Nodup := List.nodup_append.mpr ⟨hO, hK, hcross⟩
  have hcenterCore : I.center v.1 ∈ I.core v.1 := I.center_mem_core v.1 v.2
  have hcenterO : I.center v.1 ∉ O := by
    intro h
    exact (Finset.mem_sdiff.mp h).2 hcenterCore
  have hcenterK : I.center v.1 ∉ K := by
    intro h
    exact (Finset.mem_erase.mp h).1 rfl
  have hlast : ∀ x ∈ O.toList ++ K.toList, x ≠ I.center v.1 := by
    intro x hx hxeq
    have hx' : x ∈ O.toList ∨ x ∈ K.toList := List.mem_append.mp hx
    rcases hx' with hx' | hx'
    · have hxCenter : I.center v.1 ∈ O.toList := by simpa [hxeq] using hx'
      exact hcenterO (by simpa using hxCenter)
    · have hxCenter : I.center v.1 ∈ K.toList := by simpa [hxeq] using hx'
      exact hcenterK (by simpa using hxCenter)
  change (O.toList ++ K.toList ++ [I.center v.1]).Nodup
  apply List.nodup_append.mpr
  refine ⟨hOK, by simp, ?_⟩
  intro x hx y hy
  simp at hy
  subst y
  exact hlast x hx

private theorem regularityOrder_nodup9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n)
    (t : Fin 3) : (regularityOrder9 S I v b t).Nodup := by
  classical
  by_cases ht : t.val = 2
  · simp [regularityOrder9, ht]
    exact Finset.nodup_toList _
  · simp [regularityOrder9, ht]
    exact fullOrder_nodup9 I v b

private theorem nodup_getElem_not_mem_take {α : Type*} [DecidableEq α] {l : List α}
    (hl : l.Nodup) (k : Fin l.length) : l[k.val] ∉ (l.take k.val).toFinset := by
  intro hmem
  have hmem' : l[k.val] ∈ l.take k.val := List.mem_toFinset.mp hmem
  have hself : l[k.val] ∈ l := by
    exact List.mem_iff_getElem.mpr ⟨k.val, k.isLt, rfl⟩
  have hidx : l.idxOf l[k.val] = k.val := hl.idxOf_getElem k.val k.isLt
  have hlt := (List.mem_take_iff_idxOf_lt hself).mp hmem'
  rw [hidx] at hlt
  omega

private def RegularityTestIndex9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n) :=
  Σ b : StarOdd9 v, Σ t : Fin 3, Fin (regularityOrder9 S I v b.1 t).length

private abbrev BoundedRegularityTestIndex9 {P : Params9} {n : ℕ}
    (I : IDMap9 P n) (v : EvenSites9 n) :=
  ((StarOdd9 v × Fin 3) × Fin (2 * n + 1))

private noncomputable def prefixRegularBefore9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (b : StarOdd9 v) (t : Fin 3)
    (k : Fin (regularityOrder9 S I v b.1 t).length) (ω : Outcome9 I N) : Prop :=
  let ord := regularityOrder9 S I v b.1 t
  let base := regularityBase9 S I b.1 ω t
  (∀ j c', j < k.val → ord[j]? = some c' →
    (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j))

private noncomputable def badPrefixTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (b : StarOdd9 v) (t : Fin 3)
    (k : Fin (regularityOrder9 S I v b.1 t).length) (ω : Outcome9 I N) : Prop :=
  let ord := regularityOrder9 S I v b.1 t
  let base := regularityBase9 S I b.1 ω t
  prefixRegularBefore9 S I E G v b t k ω ∧
  2 * P.bStar n < |rowDeg E G (anc9 ω ord[k.val])
    (prefixLaw9 E G ω base ord k.val) - 1 / 2|

private def badBoundedRegularityTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (q : BoundedRegularityTestIndex9 I v) (ω : Outcome9 I N) : Prop :=
  ∃ k : Fin (regularityOrder9 S I v q.1.1.1 q.1.2).length,
    k.val = q.2.val ∧ badPrefixTest9 S I E G v q.1.1 q.1.2 k ω

private theorem hitSet_update_anchor9 {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} {E : Fin N → Fin N → Prop} {G : Colour}
    (ω : Outcome9 I N) (c : I.ID) (x : Fin N) (ids : Finset I.ID)
    (hnot : c ∉ ids) :
    hitSet9 E G (Function.update ω (Sum.inl c) x) ids = hitSet9 E G ω ids := by
  classical
  ext y
  simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h d hd
  · have hdne : d ≠ c := by
      intro hdc
      subst d
      exact hnot hd
    have hanc : anc9 (Function.update ω (Sum.inl c) x) d = anc9 ω d := by
      simp [anc9, Function.update, Sum.inl.injEq, hdne]
      rfl
    simpa only [hanc] using h d hd
  · have hdne : d ≠ c := by
      intro hdc
      subst d
      exact hnot hd
    have hanc : anc9 (Function.update ω (Sum.inl c) x) d = anc9 ω d := by
      simp [anc9, Function.update, Sum.inl.injEq, hdne]
      rfl
    simpa only [hanc] using h d hd

private theorem regularityBase_update9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (b : OddSites9 n)
    (ω : Outcome9 I N) (c : I.ID) (x : Fin N) (t : Fin 3) :
    regularityBase9 S I b (Function.update ω (Sum.inl c) x) t = regularityBase9 S I b ω t := by
  classical
  by_cases ht : t.val = 0
  · simp only [regularityBase9, if_pos ht]
    unfold maskedLaw9
    apply congrArg (restrictOr9 (siteSecond9 S b.1))
    change Function.update ω (Sum.inl c) x (Sum.inr b) = ω (Sum.inr b)
    simp [Function.update, Sum.inr_ne_inl]
  · simp only [regularityBase9, if_neg ht]

private theorem prefixLaw_update_anchor9 {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} {E : Fin N → Fin N → Prop} {G : Colour}
    (ω : Outcome9 I N) (c : I.ID) (x : Fin N) (base : Law N) (ord : List I.ID)
    (k : ℕ) (hnot : c ∉ (ord.take k).toFinset) :
    prefixLaw9 E G (Function.update ω (Sum.inl c) x) base ord k =
      prefixLaw9 E G ω base ord k := by
  unfold prefixLaw9
  rw [@hitSet_update_anchor9 P n N M I E G ω c x (ord.take k).toFinset hnot]

private theorem prefixRegularBefore_update9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (b : StarOdd9 v) (t : Fin 3)
    (k : Fin (regularityOrder9 S I v b.1 t).length) (ω : Outcome9 I N)
    (hnodup : (regularityOrder9 S I v b.1 t).Nodup) (x : Fin N) :
    prefixRegularBefore9 S I E G v b t k (Function.update ω (Sum.inl
      (regularityOrder9 S I v b.1 t)[k.val]) x) ↔ prefixRegularBefore9 S I E G v b t k ω := by
  classical
  let ord := regularityOrder9 S I v b.1 t
  let c : I.ID := ord[k.val]
  have hbase : regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t =
      regularityBase9 S I b.1 ω t := @regularityBase_update9 P n N M S I b.1 ω c x t
  have hidxc : ord.idxOf c = k.val := hnodup.idxOf_getElem k.val k.isLt
  have hnotTake (j : ℕ) (hj : j < k.val) : c ∉ (ord.take j).toFinset := by
    intro hc
    have hc' : c ∈ ord.take j := List.mem_toFinset.mp hc
    have hcIn : c ∈ ord := by
      change ord[k.val] ∈ ord
      exact List.mem_iff_getElem.mpr ⟨k.val, k.isLt, rfl⟩
    have hlt := (List.mem_take_iff_idxOf_lt hcIn).mp hc'
    rw [hidxc] at hlt
    omega
  have hdegreeEq (j : ℕ) (c' : I.ID) (hj : j < k.val)
      (hget : ord[j]? = some c') :
      rowDeg E G (anc9 (Function.update ω (Sum.inl c) x) c')
          (prefixLaw9 E G (Function.update ω (Sum.inl c) x)
            (regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t) ord j) =
        rowDeg E G (anc9 ω c') (prefixLaw9 E G ω (regularityBase9 S I b.1 ω t) ord j) := by
    have hget' : j < ord.length ∧ ord[j] = c' := by
      rcases List.getElem?_eq_some_iff.mp hget with ⟨hj', hval⟩
      exact ⟨hj', hval⟩
    have hidxj : ord.idxOf c' = j := by
      rw [← hget'.2]
      exact hnodup.idxOf_getElem j hget'.1
    have hcne : c' ≠ c := by
      intro heq
      rw [heq, hidxc] at hidxj
      omega
    have hanc : anc9 (Function.update ω (Sum.inl c) x) c' = anc9 ω c' := by
      simp [anc9, Function.update, Sum.inl.injEq, hcne]
      rfl
    rw [hbase]
    rw [@prefixLaw_update_anchor9 P n N M I E G ω c x
      (regularityBase9 S I b.1 ω t) ord j (hnotTake j hj)]
    rw [hanc]
  change
    (∀ j c', j < k.val → ord[j]? = some c' →
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 (Function.update ω (Sum.inl c) x) c')
        (prefixLaw9 E G (Function.update ω (Sum.inl c) x)
          (regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t) ord j)) ↔
    (∀ j c', j < k.val → ord[j]? = some c' →
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c')
        (prefixLaw9 E G ω (regularityBase9 S I b.1 ω t) ord j))
  rw [hbase]
  constructor
  · intro h j c' hj hget
    calc
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 (Function.update ω (Sum.inl c) x) c')
          (prefixLaw9 E G (Function.update ω (Sum.inl c) x)
            (regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t) ord j) :=
        h j c' hj hget
      _ = rowDeg E G (anc9 ω c')
          (prefixLaw9 E G ω (regularityBase9 S I b.1 ω t) ord j) := hdegreeEq j c' hj hget
  · intro h j c' hj hget
    calc
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c')
          (prefixLaw9 E G ω (regularityBase9 S I b.1 ω t) ord j) := h j c' hj hget
      _ = rowDeg E G (anc9 (Function.update ω (Sum.inl c) x) c')
          (prefixLaw9 E G (Function.update ω (Sum.inl c) x)
            (regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t) ord j) :=
        (hdegreeEq j c' hj hget).symm

private noncomputable def badRegularityTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (q : RegularityTestIndex9 S I v) (ω : Outcome9 I N) : Prop :=
  badPrefixTest9 S I E G v q.1 q.2.1 q.2.2 ω

private theorem law_restrict_degree_mass9 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (A : Finset (Fin N)) (x : Fin N)
    (hm : 0 < ∑ y ∈ A, μ.w y) :
    (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) =
      (∑ y ∈ A, μ.w y) * rowDeg E G x (μ.restrict A hm) := by
  classical
  let m : ℝ := ∑ y ∈ A, μ.w y
  have hm' : 0 < m := hm
  have hdegree : rowDeg E G x (μ.restrict A hm) =
      (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) / m := by
    unfold rowDeg
    simp only [Law.restrict]
    have hfilter : Finset.univ.filter (fun y : Fin N => y ∈ A ∧ Hits E G x y) =
        A.filter (fun y => Hits E G x y) := by
      ext y
      simp
    calc
      (∑ y, (if y ∈ A then μ.w y / m else 0) *
          (if Hits E G x y then 1 else 0)) =
          ∑ y, if y ∈ A ∧ Hits E G x y then μ.w y / m else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hA : y ∈ A <;> by_cases hHit : Hits E G x y <;> simp [hA, hHit]
      _ = ∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y / m := by
            rw [← Finset.sum_filter, hfilter]
      _ = (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) / m := by
            rw [Finset.sum_div]
  calc
    (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) =
        m * ((∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) / m) := by
          rw [mul_div_cancel₀ _ (ne_of_gt hm')]
    _ = (∑ y ∈ A, μ.w y) * rowDeg E G x (μ.restrict A hm) := by
          rw [hdegree]

private noncomputable def prefixMass9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID) (k : ℕ) : ℝ :=
  ∑ y ∈ hitSet9 E G ω (ord.take k).toFinset, base.w y

private theorem prefixMass_lower9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID) :
    ∀ k : ℕ, k ≤ ord.length →
      (∀ j c', j < k → ord[j]? = some c' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j)) →
      (49 / 100 : ℝ) ^ k ≤ prefixMass9 E G ω base ord k := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk hprev
      have hmass : prefixMass9 E G ω base ord 0 = 1 := by
        simp [prefixMass9, hitSet9, base.sum_eq_one]
      rw [hmass]
      norm_num
  | succ k ih =>
      intro hk hprev
      have hklen : k < ord.length := by omega
      let c : I.ID := ord[k]
      have hkc : ord[k]? = some c := by simp [c]
      have hcurrent := hprev k c (by omega) hkc
      have hprev' : ∀ j c', j < k → ord[j]? = some c' →
          (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j) := by
        intro j c' hj hget
        exact hprev j c' (by omega) hget
      have hmassPrev := ih (by omega) hprev'
      have hmassPrevPos : 0 < prefixMass9 E G ω base ord k := by
        exact lt_of_lt_of_le (by positivity : 0 < (49 / 100 : ℝ) ^ k) hmassPrev
      let A := hitSet9 E G ω (ord.take k).toFinset
      have hmassA : 0 < ∑ y ∈ A, base.w y := by
        change 0 < prefixMass9 E G ω base ord k at hmassPrevPos
        simpa [prefixMass9, A] using hmassPrevPos
      have hprefix : prefixLaw9 E G ω base ord k = base.restrict A hmassPrevPos := by
        change restrictOr9 base A = base.restrict A hmassPrevPos
        unfold restrictOr9
        rw [dif_pos hmassA]
      have htake : ord.take k ++ [ord[k]] = ord.take (k + 1) :=
        List.take_concat_get' ord k hklen
      have hids : (ord.take (k + 1)).toFinset = insert c (ord.take k).toFinset := by
        calc
          (ord.take (k + 1)).toFinset = (ord.take k ++ [ord[k]]).toFinset := by rw [← htake]
          _ = insert c (ord.take k).toFinset := by
            rw [List.toFinset_append]
            simp [c, Finset.union_comm]
      have hset : hitSet9 E G ω (insert c (ord.take k).toFinset) =
          (hitSet9 E G ω (ord.take k).toFinset).filter
            (fun y => Hits E G (anc9 ω c) y) := by
        ext y
        simp [hitSet9, c, Finset.mem_insert, and_left_comm, and_comm, and_assoc]
      have hrec : prefixMass9 E G ω base ord (k + 1) =
          prefixMass9 E G ω base ord k * rowDeg E G (anc9 ω c) (base.restrict A hmassPrevPos) := by
        unfold prefixMass9
        rw [hids]
        rw [hset]
        exact law_restrict_degree_mass9 E G base A (anc9 ω c) hmassA
      rw [hprefix] at hcurrent
      rw [hrec]
      have hdegree_nonneg : 0 ≤ rowDeg E G (anc9 ω c) (base.restrict A hmassPrevPos) :=
        le_trans (by norm_num) hcurrent
      calc
        (49 / 100 : ℝ) ^ (k + 1) = (49 / 100 : ℝ) ^ k * (49 / 100 : ℝ) := by rw [pow_succ]
        _ ≤ prefixMass9 E G ω base ord k *
            rowDeg E G (anc9 ω c) (base.restrict A hmassPrevPos) :=
          mul_le_mul hmassPrev hcurrent (by norm_num) (le_trans (by positivity) hmassPrev)

private theorem orderRegular_prefix_degrees9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID)
    (hord : orderRegular9 E G ω base ord) (hbstar : P.bStar n ≤ 1 / 200) :
    ∀ m : ℕ, m ≤ ord.length → ∀ j c', j < m → ord[j]? = some c' →
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j) := by
  classical
  intro m
  induction m with
  | zero =>
      intro hm j c' hj hget
      omega
  | succ m ih =>
      intro hm j c' hj hget
      by_cases hjm : j < m
      · exact ih (by omega) j c' hjm hget
      · have hjEq : j = m := by omega
        subst j
        have hprev : ∀ l d, l < m → ord[l]? = some d →
            (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω d) (prefixLaw9 E G ω base ord l) := by
          intro l d hlt hget'
          exact ih (by omega) l d hlt hget'
        have hregular := hord m c' hget hprev
        have hlow := (abs_le.mp hregular).1
        have hbstarBound : 2 * P.bStar n ≤ 1 / 100 := by nlinarith
        linarith

private theorem coreHit_mass_lower_regular9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (b : OddSites9 n)
    (hcore : orderRegular9 E G ω (siteSecond9 S b.1) (coreOrder9 I v b))
    (hbstar : P.bStar n ≤ 1 / 200) :
    (49 / 100 : ℝ) ^ coreCount9 I v b ≤
      ∑ y ∈ coreHitSet9 E G ω v b, (siteSecond9 S b.1).w y := by
  classical
  let ord := coreOrder9 I v b
  have hdegrees := orderRegular_prefix_degrees9 S I E G ω (siteSecond9 S b.1)
    ord hcore hbstar
  have hlen : ord.length ≤ coreCount9 I v b := by
    simp [ord, coreOrder9, coreCount9]
    exact Finset.card_erase_le
  have hmassLen : (49 / 100 : ℝ) ^ ord.length ≤
      prefixMass9 E G ω (siteSecond9 S b.1) ord ord.length := by
    exact prefixMass_lower9 S I E G ω (siteSecond9 S b.1) ord ord.length le_rfl (hdegrees ord.length le_rfl)
  have hpow : (49 / 100 : ℝ) ^ coreCount9 I v b ≤ (49 / 100 : ℝ) ^ ord.length :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hlen
  have hset : (ord.take ord.length).toFinset = coreIDs9 I v b := by
    have htake : (coreIDs9 I v b).toList.take (coreIDs9 I v b).card =
        (coreIDs9 I v b).toList := by
      simpa using List.take_length (coreIDs9 I v b).toList
    simpa [ord, coreOrder9] using congrArg List.toFinset htake
  have hmassEq : prefixMass9 E G ω (siteSecond9 S b.1) ord ord.length =
      ∑ y ∈ coreHitSet9 E G ω v b, (siteSecond9 S b.1).w y := by
    unfold prefixMass9
    rw [hset]
    rfl
  calc
    (49 / 100 : ℝ) ^ coreCount9 I v b ≤ (49 / 100 : ℝ) ^ ord.length := hpow
    _ ≤ prefixMass9 E G ω (siteSecond9 S b.1) ord ord.length := hmassLen
    _ = ∑ y ∈ coreHitSet9 E G ω v b, (siteSecond9 S b.1).w y := hmassEq

private theorem orderRegular_update_anchor9 {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} {E : Fin N → Fin N → Prop} {G : Colour}
    (ω : Outcome9 I N) (c : I.ID) (x : Fin N) (base : Law N) (ord : List I.ID)
    (hnot : c ∉ ord.toFinset) :
    orderRegular9 E G (Function.update ω (Sum.inl c) x) base ord ↔
      orderRegular9 E G ω base ord := by
  classical
  have hnotTake (j : ℕ) (hj : j ≤ ord.length) : c ∉ (ord.take j).toFinset := by
    intro hc
    have hmem : c ∈ ord.take j := List.mem_toFinset.mp hc
    rcases List.mem_take_iff_getElem.mp hmem with ⟨i, hi, hget⟩
    have hmemOrd : c ∈ ord := by
      exact List.mem_iff_getElem.mpr ⟨i, lt_of_lt_of_le hi (Nat.min_le_right _ _), hget⟩
    exact hnot (List.mem_toFinset.mpr hmemOrd)
  have hanchor (d : I.ID) (hd : d ∈ ord) :
      anc9 (Function.update ω (Sum.inl c) x) d = anc9 ω d := by
    have hne : d ≠ c := by
      intro heq
      subst d
      exact hnot (List.mem_toFinset.mpr hd)
    simp [anc9, Function.update, Sum.inl.injEq, hne]
    rfl
  constructor
  · intro h k d hget hprev
    have hklt : k < ord.length := (List.getElem?_eq_some_iff.mp hget).choose
    have hdmem : d ∈ ord := by
      rcases List.getElem?_eq_some_iff.mp hget with ⟨hk, heq⟩
      exact List.mem_iff_getElem.mpr ⟨k, hk, heq⟩
    have hprev' : ∀ j d', j < k → ord[j]? = some d' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 (Function.update ω (Sum.inl c) x) d')
          (prefixLaw9 E G (Function.update ω (Sum.inl c) x) base ord j) := by
      intro j d' hj hget'
      have hd'mem : d' ∈ ord := by
        rcases List.getElem?_eq_some_iff.mp hget' with ⟨hj', heq⟩
        exact List.mem_iff_getElem.mpr ⟨j, hj', heq⟩
      have hAnc := hanchor d' hd'mem
      have hLaw := @prefixLaw_update_anchor9 P n N M I E G ω c x base ord j
        (hnotTake j (by omega))
      rw [hAnc, hLaw]
      exact hprev j d' hj hget'
    have hAnc := hanchor d hdmem
    have hLaw := @prefixLaw_update_anchor9 P n N M I E G ω c x base ord k
      (hnotTake k (Nat.le_of_lt hklt))
    have h := h k d hget hprev'
    rw [hAnc, hLaw] at h
    exact h
  · intro h k d hget hprev
    have hklt : k < ord.length := (List.getElem?_eq_some_iff.mp hget).choose
    have hdmem : d ∈ ord := by
      rcases List.getElem?_eq_some_iff.mp hget with ⟨hk, heq⟩
      exact List.mem_iff_getElem.mpr ⟨k, hk, heq⟩
    have hprev' : ∀ j d', j < k → ord[j]? = some d' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω d') (prefixLaw9 E G ω base ord j) := by
      intro j d' hj hget'
      have hd'mem : d' ∈ ord := by
        rcases List.getElem?_eq_some_iff.mp hget' with ⟨hj', heq⟩
        exact List.mem_iff_getElem.mpr ⟨j, hj', heq⟩
      have hAnc := hanchor d' hd'mem
      have hLaw := @prefixLaw_update_anchor9 P n N M I E G ω c x base ord j
        (hnotTake j (by omega))
      rw [← hAnc, ← hLaw]
      exact hprev j d' hj hget'
    have hAnc := hanchor d hdmem
    have hLaw := @prefixLaw_update_anchor9 P n N M I E G ω c x base ord k
      (hnotTake k (Nat.le_of_lt hklt))
    have h := h k d hget hprev'
    rw [← hAnc, ← hLaw] at h
    exact h

private theorem exists_badPrefix_of_not_orderRegular9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID)
    (hn : ¬ orderRegular9 E G ω base ord) :
    ∃ k : Fin ord.length,
      (∀ j c', j < k.val → ord[j]? = some c' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j)) ∧
      2 * P.bStar n < |rowDeg E G (anc9 ω ord[k.val])
        (prefixLaw9 E G ω base ord k.val) - 1 / 2| := by
  classical
  unfold orderRegular9 at hn
  push_neg at hn
  rcases hn with ⟨k, c, hkc, hprev, hfail⟩
  rcases List.getElem?_eq_some_iff.mp hkc with ⟨hk, hval⟩
  let kFin : Fin ord.length := ⟨k, hk⟩
  have hfail' : 2 * P.bStar n <
      |rowDeg E G (anc9 ω ord[kFin.val]) (prefixLaw9 E G ω base ord k) - 1 / 2| := by
    have hfail'' := hfail
    rw [← hval] at hfail''
    simpa [kFin] using hfail''
  refine ⟨kFin, ?_, ?_⟩
  · simpa using hprev
  · simpa using hfail'

private theorem exists_badRegularityTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (hbad : ¬ starRegular9 S E G ω v) :
    ∃ q : RegularityTestIndex9 S I v, badRegularityTest9 S I E G v q ω := by
  classical
  unfold starRegular9 at hbad
  push_neg at hbad
  rcases hbad with ⟨b, hadj, horders⟩
  by_cases hmasked : orderRegular9 E G ω (maskedLaw9 S ω b) (fullOrder9 I v b)
  · by_cases hunmasked : orderRegular9 E G ω (siteSecond9 S b.1) (fullOrder9 I v b)
    · have hcore : ¬ orderRegular9 E G ω (siteSecond9 S b.1) (coreOrder9 I v b) :=
        horders hmasked hunmasked
      obtain ⟨k, hprev, htail⟩ := exists_badPrefix_of_not_orderRegular9 S I E G ω
        (siteSecond9 S b.1) (coreOrder9 I v b) hcore
      let b' : StarOdd9 v := ⟨b, hadj⟩
      let t : Fin 3 := ⟨2, by omega⟩
      refine ⟨⟨b', ⟨t, k⟩⟩, ?_⟩
      simpa [badRegularityTest9, badPrefixTest9, prefixRegularBefore9, regularityOrder9,
        regularityBase9, t, b'] using
        And.intro hprev htail
    · obtain ⟨k, hprev, htail⟩ := exists_badPrefix_of_not_orderRegular9 S I E G ω
        (siteSecond9 S b.1) (fullOrder9 I v b) hunmasked
      let b' : StarOdd9 v := ⟨b, hadj⟩
      let t : Fin 3 := ⟨1, by omega⟩
      refine ⟨⟨b', ⟨t, k⟩⟩, ?_⟩
      simpa [badRegularityTest9, badPrefixTest9, prefixRegularBefore9, regularityOrder9,
        regularityBase9, t, b'] using
        And.intro hprev htail
  · obtain ⟨k, hprev, htail⟩ := exists_badPrefix_of_not_orderRegular9 S I E G ω
      (maskedLaw9 S ω b) (fullOrder9 I v b) hmasked
    let b' : StarOdd9 v := ⟨b, hadj⟩
    let t : Fin 3 := ⟨0, by omega⟩
    refine ⟨⟨b', ⟨t, k⟩⟩, ?_⟩
    simpa [badRegularityTest9, badPrefixTest9, prefixRegularBefore9, regularityOrder9,
      regularityBase9, t, b'] using
      And.intro hprev htail

private theorem regularityOrder_length_le_seen_add_one9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n) (b : StarOdd9 v)
    (t : Fin 3) :
    (regularityOrder9 S I v b t).length ≤ (I.seen b.1).card + 1 := by
  classical
  let O := outerIDs9 I v b.1
  let K := coreIDs9 I v b.1
  have hO : O ⊆ I.seen b.1 := by
    intro x hx
    exact (Finset.mem_sdiff.mp (by simpa [O, outerIDs9] using hx)).1
  have hK : K ⊆ I.seen b.1 := by
    intro x hx
    rcases (by simpa [K, coreIDs9] using hx) with ⟨_, hxSeen, _⟩
    exact hxSeen
  have hdis : Disjoint O K := by
    rw [Finset.disjoint_left]
    intro x hxO hxK
    rcases (by simpa [O, outerIDs9] using hxO) with ⟨_, hxNotCore⟩
    rcases (by simpa [K, coreIDs9] using hxK) with ⟨_, _, hxCore⟩
    exact hxNotCore hxCore
  have hcard : O.card + K.card ≤ (I.seen b.1).card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset hO hK)
  by_cases ht : t.val = 2
  · simp [regularityOrder9, ht, coreOrder9, K]
    exact Nat.le_trans (Finset.card_le_card hK) (Nat.le_add_right _ _)
  · have hfull : (regularityOrder9 S I v b t).length = O.card + K.card + 1 := by
      simp [regularityOrder9, ht, fullOrder9, O, K, List.length_append]
      omega
    rw [hfull]
    omega

private theorem starOdd_card_le9 {n : ℕ} (v : EvenSites9 n) : Fintype.card (StarOdd9 v) ≤ n := by
  classical
  let Adj : CubeVertex n → Prop := fun b => (cube n).Adj v.1 b
  let e : StarOdd9 v → {b : CubeVertex n // Adj b} := fun b => ⟨b.1.1, b.2⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    change a.1.1 = b.1.1
    exact congrArg (fun z : {y : CubeVertex n // Adj y} => z.1) hab
  have hcard : Fintype.card {b : CubeVertex n // Adj b} =
      (Finset.univ.filter Adj).card := by
    simpa [Adj] using (Fintype.card_subtype (fun b : CubeVertex n => Adj b))
  calc
    Fintype.card (StarOdd9 v) ≤ Fintype.card {b : CubeVertex n // Adj b} :=
      Fintype.card_le_of_injective e he
    _ = (Finset.univ.filter Adj).card := hcard
    _ ≤ n := by simpa [Adj] using cube_adj_neighbors_card_le n v.1

private theorem boundedRegularityTestIndex_card_le9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n)
    (hscale : ScaleExps9 P) (hAt : ScalesAt9 P n) :
    Fintype.card (BoundedRegularityTestIndex9 I v) ≤ 9 * n ^ 2 := by
  classical
  rcases hscale with ⟨_, hepsσ, _, _, _⟩
  rcases hAt with ⟨hn, hm, _, _, _, _, _, _⟩
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hexpT : 1 - (P.σ : ℝ) + P.eps ≤ 1 := by linarith
  have hT : P.idBudget n ≤ (n : ℝ) := by
    unfold Params9.idBudget
    simpa using Real.rpow_le_rpow_of_exponent_le hnR hexpT
  have hmR : (P.m n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
  have hseenR (b : StarOdd9 v) :
      ((I.seen b.1).card : ℝ) ≤ 2 * (n : ℝ) := by
    have hodd := I.odd_ids b.1.1 b.1.2
    have hodd' : ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := by
      simpa [IDMap9.seen] using hodd
    calc
      ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := hodd'
      _ ≤ (n : ℝ) + (n : ℝ) := add_le_add hT hmR
      _ = 2 * (n : ℝ) := by ring
  have hlen (b : StarOdd9 v) (t : Fin 3) :
      (regularityOrder9 S I v b.1 t).length ≤ 2 * n + 1 := by
    have h := regularityOrder_length_le_seen_add_one9 S I v b t
    have hseen : (I.seen b.1).card ≤ 2 * n := by exact_mod_cast hseenR b
    omega
  have hstar := starOdd_card_le9 v
  have hcard : Fintype.card (BoundedRegularityTestIndex9 I v) ≤ 9 * n ^ 2 := by
    have hcardEq : Fintype.card (BoundedRegularityTestIndex9 I v) =
        Fintype.card (StarOdd9 v) * 3 * (2 * n + 1) := by
      dsimp [BoundedRegularityTestIndex9]
      rw [Fintype.card_prod, Fintype.card_prod]
      simp [Nat.mul_assoc]
    rw [hcardEq]
    calc
      _ ≤ n * 3 * (2 * n + 1) := Nat.mul_le_mul_right (2 * n + 1)
        (Nat.mul_le_mul_right 3 hstar)
      _ ≤ 9 * n ^ 2 := by nlinarith [hn]
  exact hcard

private theorem exists_badBoundedRegularityTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (hscale : ScaleExps9 P) (hAt : ScalesAt9 P n)
    (hbad : ¬ starRegular9 S E G ω v) :
    ∃ q : BoundedRegularityTestIndex9 I v, badBoundedRegularityTest9 S I E G v q ω := by
  classical
  obtain ⟨q, hq⟩ := exists_badRegularityTest9 S I E G ω v hbad
  rcases q with ⟨b, ⟨t, k⟩⟩
  have hlen : (regularityOrder9 S I v b.1 t).length ≤ 2 * n + 1 := by
    have h := regularityOrder_length_le_seen_add_one9 S I v b t
    have hT : P.idBudget n ≤ (n : ℝ) := by
      rcases hscale with ⟨_, hepsσ, _, _, _⟩
      rcases hAt with ⟨hn, _, _, _, _, _, _, _⟩
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hexpT : 1 - (P.σ : ℝ) + P.eps ≤ 1 := by linarith
      unfold Params9.idBudget
      simpa using Real.rpow_le_rpow_of_exponent_le hnR hexpT
    have hmR : (P.m n : ℝ) ≤ (n : ℝ) := by
      rcases hAt with ⟨_, hm, _, _, _, _, _, _⟩
      exact_mod_cast hm
    have hodd : ((I.seen b.1).card : ℝ) ≤ 2 * (n : ℝ) := by
      have hbound := I.odd_ids b.1.1 b.1.2
      have hbound' : ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := by
        simpa [IDMap9.seen] using hbound
      have hodd2 : ((I.seen b.1).card : ℝ) ≤ 2 * (n : ℝ) := by
        calc
          ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := hbound'
          _ ≤ (n : ℝ) + (n : ℝ) := add_le_add hT hmR
          _ = 2 * (n : ℝ) := by ring
      exact hodd2
    have hseen : (I.seen b.1).card ≤ 2 * n := by exact_mod_cast hodd
    omega
  let k' : Fin (2 * n + 1) := ⟨k.val, lt_of_lt_of_le k.isLt hlen⟩
  let q' : BoundedRegularityTestIndex9 I v := ((b, t), k')
  refine ⟨q', ?_⟩
  refine ⟨k, ?_, ?_⟩
  · rfl
  · simpa [badRegularityTest9] using hq

private theorem regularity_polynomial_tail9 {u χ : ℝ} (hu : 0 < u) (hχ : 0 < χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      18 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (u + 8 * χ))) ≤
          Real.exp (-((n : ℝ) ^ u / 2)) ∧
        Real.log (100 / 49) ≤ (n : ℝ) ^ u := by
  have hlittle : (fun x : ℝ => 16 * Real.log x) =o[atTop] fun x => x ^ u := by
    have h := (isLittleO_log_rpow_rpow_atTop 1 hu).const_mul_left 16
    simpa using h
  have hnat : (fun n : ℕ => 16 * Real.log (n : ℝ)) =o[atTop]
      fun n => (n : ℝ) ^ u := by
    exact (hlittle.comp_tendsto tendsto_natCast_atTop_atTop).congr_left (fun _ => rfl)
  obtain ⟨nL, hL⟩ := Filter.eventually_atTop.mp hnat.eventuallyLE
  have hpowTendsto : Tendsto (fun n : ℕ => (n : ℝ) ^ u) atTop atTop := by
    refine Tendsto.congr' ?_ ((tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop)
    filter_upwards [] with n
    rfl
  obtain ⟨nR, hR⟩ := Filter.eventually_atTop.mp
    (hpowTendsto.eventually_ge_atTop (Real.log (100 / 49)))
  refine ⟨max (max nL 18) nR, ?_⟩
  intro n hn
  have hnLR : max nL 18 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnR : nR ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnL : nL ≤ n := le_trans (Nat.le_max_left _ _) hnLR
  have hn18 : 18 ≤ n := le_trans (Nat.le_max_right _ _) hnLR
  have hnReal : 18 ≤ (n : ℝ) := by exact_mod_cast hn18
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hpowPos : 0 < (n : ℝ) ^ u := Real.rpow_pos_of_pos (by positivity) _
  have hnorm := hL n hnL
  have h16log : 16 * Real.log (n : ℝ) ≤ (n : ℝ) ^ u := by
    have h1 : 0 ≤ 16 * Real.log (n : ℝ) := by positivity
    have h2 : 0 ≤ (n : ℝ) ^ u := le_of_lt hpowPos
    simpa [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2] using hnorm
  have hlog18 : Real.log 18 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hnReal
  have hlogFactor : Real.log (18 * (n : ℝ) ^ 2) ≤ (n : ℝ) ^ u / 2 := by
    have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
    have hlogmul : Real.log (18 * (n : ℝ) ^ 2) = Real.log 18 + 2 * Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hn2), Real.log_pow]
      norm_num
    rw [hlogmul]
    nlinarith
  have hA : (n : ℝ) ^ u ≤ (n : ℝ) ^ (u + 8 * χ) := by
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hfactor :
      18 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (u + 8 * χ))) =
        Real.exp (Real.log (18 * (n : ℝ) ^ 2) - (n : ℝ) ^ (u + 8 * χ)) := by
    have hpos : 0 < 18 * (n : ℝ) ^ 2 := by positivity
    have hM : 18 * (n : ℝ) ^ 2 = Real.exp (Real.log (18 * (n : ℝ) ^ 2)) :=
      (Real.exp_log hpos).symm
    calc
      _ = Real.exp (Real.log (18 * (n : ℝ) ^ 2)) *
          Real.exp (-((n : ℝ) ^ (u + 8 * χ))) :=
            congrArg (fun z : ℝ => z * Real.exp (-((n : ℝ) ^ (u + 8 * χ)))) hM
      _ = Real.exp (Real.log (18 * (n : ℝ) ^ 2) + -((n : ℝ) ^ (u + 8 * χ))) := by
            exact (Real.exp_add _ _).symm
      _ = Real.exp (Real.log (18 * (n : ℝ) ^ 2) - (n : ℝ) ^ (u + 8 * χ)) := by
            congr 1 <;> ring
  constructor
  · calc
      18 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (u + 8 * χ))) =
          Real.exp (Real.log (18 * (n : ℝ) ^ 2) - (n : ℝ) ^ (u + 8 * χ)) := hfactor
      _ ≤ Real.exp (-((n : ℝ) ^ u / 2)) := by
        apply Real.exp_le_exp.mpr
        linarith
  · exact hR n hnR

private theorem mask_log_bound9 {a m : ℝ}
    (hm : (1 / 2 : ℝ) * Real.exp (-a) ≤ m) : -Real.log m ≤ a + Real.log 2 := by
  have hlow : 0 < (1 / 2 : ℝ) * Real.exp (-a) := mul_pos (by norm_num) (Real.exp_pos _)
  have hmpos : 0 < m := lt_of_lt_of_le hlow hm
  have hlog := Real.log_le_log hlow hm
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hexact : Real.log ((1 / 2 : ℝ) * Real.exp (-a)) = -Real.log 2 - a := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), hhalf, Real.log_exp]
    ring
  rw [hexact] at hlog
  linarith

private theorem prefix_log_bound9 {k : ℕ} {m : ℝ}
    (hm : (49 / 100 : ℝ) ^ k ≤ m) :
    -Real.log m ≤ (k : ℝ) * Real.log (100 / 49) := by
  have hbase : (0 : ℝ) < 49 / 100 := by norm_num
  have hpow : 0 < (49 / 100 : ℝ) ^ k := pow_pos hbase _
  have hmpos : 0 < m := lt_of_lt_of_le hpow hm
  have hlog := Real.log_le_log hpow hm
  have hratio : Real.log (49 / 100 : ℝ) = -Real.log (100 / 49) := by
    have hinv : (49 / 100 : ℝ) = (100 / 49)⁻¹ := by norm_num
    rw [hinv, Real.log_inv]
  rw [Real.log_pow, hratio] at hlog
  linarith

private theorem law_restrict_supported9 {N : ℕ} {Y A : Finset (Fin N)} {μ : Law N}
    (hμ : μ.SupportedIn Y) (hm : 0 < ∑ y ∈ A, μ.w y) :
    (μ.restrict A hm).SupportedIn Y := by
  intro y hy
  by_cases hA : y ∈ A
  · simp [Law.restrict, hA, hμ y hy]
  · simp [Law.restrict, hA]

private theorem rowDeg_lipschitz_l1_9 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (x : Fin N) (μ ν : Law N) :
    |rowDeg E G x μ - rowDeg E G x ν| ≤ ∑ y, |μ.w y - ν.w y| := by
  classical
  have hsum : rowDeg E G x μ - rowDeg E G x ν =
      ∑ y, (μ.w y - ν.w y) * (if Hits E G x y then 1 else 0) := by
    rw [rowDeg, rowDeg, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hsum]
  calc
    |∑ y, (μ.w y - ν.w y) * (if Hits E G x y then 1 else 0)| ≤
        ∑ y, |(μ.w y - ν.w y) * (if Hits E G x y then 1 else 0)| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun y => (μ.w y - ν.w y) * (if Hits E G x y then 1 else 0)) Finset.univ
    _ ≤ ∑ y, |μ.w y - ν.w y| := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases h : Hits E G x y <;> simp [h]

private theorem law_restrict_l1_bound9 {N : ℕ} (μ ν : Law N) (A : Finset (Fin N))
    (hμ : 0 < ∑ y ∈ A, μ.w y) (hν : 0 < ∑ y ∈ A, ν.w y)
    (δ : ℝ) (hL1 : ∑ y, |μ.w y - ν.w y| ≤ δ) :
    ∑ y, |(μ.restrict A hμ).w y - (ν.restrict A hν).w y| ≤
      2 * δ / (∑ y ∈ A, μ.w y) := by
  classical
  let a : ℝ := ∑ y ∈ A, μ.w y
  let b : ℝ := ∑ y ∈ A, ν.w y
  have ha : 0 < a := hμ
  have hb : 0 < b := hν
  have hmassDiff : |a - b| ≤ δ := by
    have hdiff : a - b = ∑ y ∈ A, (μ.w y - ν.w y) := by
      dsimp [a, b]
      rw [Finset.sum_sub_distrib]
    calc
      |a - b| = |∑ y ∈ A, (μ.w y - ν.w y)| := by rw [hdiff]
      _ ≤ ∑ y ∈ A, |μ.w y - ν.w y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |μ.w y - ν.w y| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        intro y hy hnot
        positivity
      _ ≤ δ := hL1
  have hpoint (y : Fin N) :
      |(μ.restrict A hμ).w y - (ν.restrict A hν).w y| ≤
        if y ∈ A then |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) else 0 := by
    by_cases hy : y ∈ A
    · simp [Law.restrict, hy, a, b]
      have hfrac : μ.w y / a - ν.w y / b =
          (μ.w y - ν.w y) / a + ν.w y * (b - a) / (a * b) := by
        field_simp [ne_of_gt ha, ne_of_gt hb]
        ring
      rw [hfrac]
      calc
        |(μ.w y - ν.w y) / a + ν.w y * (b - a) / (a * b)| ≤
            |(μ.w y - ν.w y) / a| + |ν.w y * (b - a) / (a * b)| := abs_add_le _ _
        _ = |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) := by
          simp [abs_div, abs_mul, abs_of_nonneg (ν.nonneg y), abs_of_pos ha,
            abs_of_pos hb, abs_sub_comm]
    · simp [Law.restrict, hy]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y hy => hpoint y)
  have hsumBound :
      (∑ y, if y ∈ A then |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) else 0) ≤
        δ / a + δ / a := by
    have hfirstEq : (∑ y ∈ A, |μ.w y - ν.w y| / a) =
        (∑ y ∈ A, |μ.w y - ν.w y|) / a := by rw [Finset.sum_div]
    have hsecondEq : (∑ y ∈ A, ν.w y * |a - b| / (a * b)) =
        (∑ y ∈ A, ν.w y) * |a - b| / (a * b) := by
      calc
        (∑ y ∈ A, ν.w y * |a - b| / (a * b)) =
            ∑ y ∈ A, ν.w y * (|a - b| / (a * b)) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = (∑ y ∈ A, ν.w y) * (|a - b| / (a * b)) := by
          simpa using (Finset.sum_mul (s := A) (f := fun y => ν.w y)
            (a := |a - b| / (a * b))).symm
        _ = (∑ y ∈ A, ν.w y) * |a - b| / (a * b) := by ring
    calc
      (∑ y, if y ∈ A then |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) else 0) =
          (∑ y ∈ A, |μ.w y - ν.w y| / a) +
            (∑ y ∈ A, ν.w y * |a - b| / (a * b)) := by
              simp only [Finset.sum_ite_mem]
              rw [Finset.sum_add_distrib]
              simp
      _ = (∑ y ∈ A, |μ.w y - ν.w y|) / a +
            (∑ y ∈ A, ν.w y) * |a - b| / (a * b) := by rw [hfirstEq, hsecondEq]
      _ ≤ δ / a + δ / a := by
        have hsumErr : (∑ y ∈ A, |μ.w y - ν.w y|) ≤ δ := by
          calc
            (∑ y ∈ A, |μ.w y - ν.w y|) ≤ ∑ y, |μ.w y - ν.w y| := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
              intro y hy hnot
              positivity
            _ ≤ δ := hL1
        have hfirst := div_le_div_of_nonneg_right hsumErr (le_of_lt ha)
        have hsecond : b * |a - b| / (a * b) ≤ δ / a := by
          have habs : |a - b| ≤ δ := hmassDiff
          have hmul := mul_le_mul_of_nonneg_left habs (le_of_lt hb)
          have hquot : b * |a - b| / (a * b) = |a - b| / a := by
            field_simp [ne_of_gt ha, ne_of_gt hb]
          rw [hquot]
          exact div_le_div_of_nonneg_right habs (le_of_lt ha)
        rw [show (∑ y ∈ A, ν.w y) = b by rfl]
        exact add_le_add hfirst hsecond
  calc
    (∑ y, |(μ.restrict A hμ).w y - (ν.restrict A hν).w y|) ≤
        ∑ y, if y ∈ A then |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) else 0 := hsum
    _ ≤ δ / a + δ / a := hsumBound
    _ = 2 * δ / (∑ y ∈ A, μ.w y) := by dsimp [a]; ring

private theorem normalize_l1_perturbation9 {N : ℕ} (Q ν : Law N) (ψ : Fin N → ℝ)
    (B δ : ℝ) (hB : 0 ≤ B) (hBhalf : B ≤ 1 / 2)
    (hψ : ∀ y, |ψ y| ≤ B)
    (herr : ∑ y, |Q.w y - (1 + ψ y) * ν.w y| ≤ δ) :
    ∃ Z > 0, ∃ R : Law N,
      (∀ y, R.w y = (1 + ψ y) * ν.w y / Z) ∧
      ∑ y, |Q.w y - R.w y| ≤ 2 * δ := by
  classical
  let Z : ℝ := ∑ y, (1 + ψ y) * ν.w y
  have hZ : 0 < Z := by
    have hterm (y : Fin N) : (1 / 2 : ℝ) * ν.w y ≤ (1 + ψ y) * ν.w y := by
      have hψlower : 1 / 2 ≤ 1 + ψ y := by
        have := (abs_le.mp (hψ y)).1
        linarith
      exact mul_le_mul_of_nonneg_right hψlower (ν.nonneg y)
    have hsum : (1 / 2 : ℝ) ≤ Z := by
      dsimp [Z]
      calc
        (1 / 2 : ℝ) = (1 / 2 : ℝ) * ∑ y, ν.w y := by rw [ν.sum_eq_one]; ring
        _ = ∑ y, (1 / 2 : ℝ) * ν.w y := by rw [Finset.mul_sum]
        _ ≤ ∑ y, (1 + ψ y) * ν.w y := Finset.sum_le_sum fun y hy => hterm y
    linarith
  let R : Law N :=
    { w := fun y => (1 + ψ y) * ν.w y / Z
      nonneg := by
        intro y
        exact div_nonneg (mul_nonneg (by linarith [(abs_le.mp (hψ y)).1]) (ν.nonneg y)) hZ.le
      sum_eq_one := by
        rw [← Finset.sum_div]
        dsimp [Z]
        exact div_self (ne_of_gt hZ) }
  have hRw (y : Fin N) : R.w y = (1 + ψ y) * ν.w y / Z := rfl
  have hraw (y : Fin N) : (1 + ψ y) * ν.w y = R.w y * Z := by
    rw [hRw]
    field_simp [ne_of_gt hZ]
  have hnormErr : ∑ y, |(1 + ψ y) * ν.w y - R.w y| = |Z - 1| := by
    calc
      (∑ y, |(1 + ψ y) * ν.w y - R.w y|) = ∑ y, R.w y * |Z - 1| := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hraw]
        have hnonneg := R.nonneg y
        rw [show R.w y * Z - R.w y = R.w y * (Z - 1) by ring,
          abs_mul, abs_of_nonneg hnonneg]
      _ = (∑ y, R.w y) * |Z - 1| := by rw [Finset.sum_mul]
      _ = |Z - 1| := by rw [R.sum_eq_one]; ring
  have hmassDiff : |Z - 1| ≤ δ := by
    have hsum : Z - 1 = ∑ y, ((1 + ψ y) * ν.w y - Q.w y) := by
      calc
        Z - 1 = (∑ y, (1 + ψ y) * ν.w y) - ∑ y, Q.w y := by simp [Z, Q.sum_eq_one]
        _ = ∑ y, ((1 + ψ y) * ν.w y - Q.w y) := by rw [Finset.sum_sub_distrib]
    rw [hsum]
    calc
      |∑ y, ((1 + ψ y) * ν.w y - Q.w y)| ≤
          ∑ y, |(1 + ψ y) * ν.w y - Q.w y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, |Q.w y - (1 + ψ y) * ν.w y| := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [abs_sub_comm]
      _ ≤ δ := herr
  have hL1 : ∑ y, |Q.w y - R.w y| ≤ 2 * δ := by
    calc
      (∑ y, |Q.w y - R.w y|) ≤
          ∑ y, (|Q.w y - (1 + ψ y) * ν.w y| + |(1 + ψ y) * ν.w y - R.w y|) := by
            apply Finset.sum_le_sum
            intro y hy
            exact abs_sub_le _ _ _
      _ = (∑ y, |Q.w y - (1 + ψ y) * ν.w y|) +
          ∑ y, |(1 + ψ y) * ν.w y - R.w y| := by rw [Finset.sum_add_distrib]
      _ ≤ δ + δ := add_le_add herr (by rw [hnormErr]; exact hmassDiff)
      _ = 2 * δ := by ring
  exact ⟨Z, hZ, R, hRw, hL1⟩

private theorem restrict_tilt_l1_9 {N : ℕ} (Q ν : Law N) (ψ : Fin N → ℝ)
    (B δ : ℝ) (hB : 0 ≤ B) (hBhalf : B ≤ 1 / 2)
    (hψ : ∀ y, |ψ y| ≤ B)
    (herr : ∑ y, |Q.w y - (1 + ψ y) * ν.w y| ≤ δ)
    (A : Finset (Fin N)) (hm : 0 < ∑ y ∈ A, ν.w y)
    (hδ : δ ≤ (∑ y ∈ A, ν.w y) / 24) :
    ∃ hQ : 0 < ∑ y ∈ A, Q.w y, ∃ lamA ρ : Law N, ∃ s : Fin N → ℝ,
      lamA = ν.restrict A hm ∧
      (∀ y, |s y| ≤ 4 * B) ∧
      (∑ y, lamA.w y * s y = 0) ∧
      (∀ y, ρ.w y = (1 + s y) * lamA.w y) ∧
      (∑ y, |(Q.restrict A hQ).w y - ρ.w y| ≤
        16 * δ / (∑ y ∈ A, ν.w y)) := by
  classical
  let m : ℝ := ∑ y ∈ A, ν.w y
  have hm' : 0 < m := hm
  have hδm : 2 * δ ≤ m / 12 := by dsimp [m] at hδ ⊢; linarith
  obtain ⟨Z, hZ, R, hRw, hQR⟩ := normalize_l1_perturbation9 Q ν ψ B δ hB hBhalf hψ herr
  have hZeq : Z = ∑ y, (1 + ψ y) * ν.w y := by
    have hsum : (∑ y, ((1 + ψ y) * ν.w y / Z)) = 1 := by
      calc
        (∑ y, ((1 + ψ y) * ν.w y / Z)) = ∑ y, R.w y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hRw]
        _ = 1 := R.sum_eq_one
    have hdiv : (∑ y, (1 + ψ y) * ν.w y) / Z = 1 := by
      change (∑ y, ((1 + ψ y) * ν.w y) / Z) = 1 at hsum
      rw [← Finset.sum_div] at hsum
      exact hsum
    have hmul := congrArg (fun x : ℝ => x * Z) hdiv
    field_simp [ne_of_gt hZ] at hmul
    linarith
  have hZupper : Z ≤ 1 + B := by
    have hterm (y : Fin N) : (1 + ψ y) * ν.w y ≤ (1 + B) * ν.w y := by
      have hp : 1 + ψ y ≤ 1 + B := by linarith [(abs_le.mp (hψ y)).2]
      exact mul_le_mul_of_nonneg_right hp (ν.nonneg y)
    calc
      Z = ∑ y, (1 + ψ y) * ν.w y := hZeq
      _ ≤ ∑ y, (1 + B) * ν.w y := Finset.sum_le_sum fun y hy => hterm y
      _ = 1 + B := by rw [← Finset.mul_sum, ν.sum_eq_one]; ring
  let lamA : Law N := ν.restrict A hm
  let mψ : ℝ := ∑ y, lamA.w y * ψ y
  have hmψ : |mψ| ≤ B := by
    calc
      |mψ| = |∑ y, lamA.w y * ψ y| := rfl
      _ ≤ ∑ y, |lamA.w y * ψ y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, lamA.w y * B := by
        apply Finset.sum_le_sum
        intro y hy
        rw [abs_mul, abs_of_nonneg (lamA.nonneg y)]
        exact mul_le_mul_of_nonneg_left (hψ y) (lamA.nonneg y)
      _ = B := by rw [← Finset.sum_mul, lamA.sum_eq_one]; ring
  have hden : 0 < 1 + mψ := by
    have hlow := (abs_le.mp hmψ).1
    linarith
  have hRmass_formula : (∑ y ∈ A, R.w y) = m * (1 + mψ) / Z := by
    have hsum : (∑ y ∈ A, (1 + ψ y) * ν.w y) = m * (1 + mψ) := by
      have hpoint (y : Fin N) (hy : y ∈ A) :
          (1 + ψ y) * ν.w y = m * (lamA.w y * (1 + ψ y)) := by
        have hLamWeight : lamA.w y = ν.w y / m := by simp [lamA, Law.restrict, hy, m]
        rw [hLamWeight]
        field_simp [ne_of_gt hm']
      calc
        (∑ y ∈ A, (1 + ψ y) * ν.w y) =
            ∑ y ∈ A, m * (lamA.w y * (1 + ψ y)) := by
              apply Finset.sum_congr rfl
              intro y hy
              exact hpoint y hy
        _ = m * ∑ y ∈ A, lamA.w y * (1 + ψ y) := by rw [Finset.mul_sum]
        _ = m * ∑ y, lamA.w y * (1 + ψ y) := by
              congr 1
              apply Finset.sum_subset (Finset.subset_univ A)
              intro y hy hnot
              have hz : lamA.w y = 0 := by simp [lamA, Law.restrict, hnot]
              simp [hz]
        _ = m * (1 + mψ) := by
              have hexpand : (∑ y, lamA.w y * (1 + ψ y)) =
                  (∑ y, lamA.w y) + ∑ y, lamA.w y * ψ y := by
                calc
                  (∑ y, lamA.w y * (1 + ψ y)) =
                      ∑ y, (lamA.w y + lamA.w y * ψ y) := by
                        apply Finset.sum_congr rfl
                        intro y hy
                        ring
                  _ = (∑ y, lamA.w y) + ∑ y, lamA.w y * ψ y := Finset.sum_add_distrib
              rw [hexpand, lamA.sum_eq_one]
    calc
      (∑ y ∈ A, R.w y) = (∑ y ∈ A, ((1 + ψ y) * ν.w y / Z)) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hRw]
      _ = (∑ y ∈ A, (1 + ψ y) * ν.w y) / Z := by rw [Finset.sum_div]
      _ = m * (1 + mψ) / Z := by rw [hsum]
  have hRmassLower : (m / 3 : ℝ) ≤ ∑ y ∈ A, R.w y := by
    rw [hRmass_formula]
    have hlow : 1 / 2 ≤ 1 + mψ := by
      have h := (abs_le.mp hmψ).1
      linarith
    have hupper : Z ≤ 3 / 2 := by linarith
    have hfrac : (1 : ℝ) / 3 ≤ (1 + mψ) / Z := by
      rw [le_div_iff₀ hZ]
      nlinarith
    calc
      m / 3 = m * (1 / 3) := by ring
      _ ≤ m * ((1 + mψ) / Z) := mul_le_mul_of_nonneg_left hfrac hm'.le
      _ = m * (1 + mψ) / Z := by ring
  have hRmass : 0 < ∑ y ∈ A, R.w y := lt_of_lt_of_le (div_pos hm' (by norm_num)) hRmassLower
  have hmassdiff : |(∑ y ∈ A, Q.w y) - (∑ y ∈ A, R.w y)| ≤ 2 * δ := by
    have hdiff : (∑ y ∈ A, Q.w y) - (∑ y ∈ A, R.w y) =
        ∑ y ∈ A, (Q.w y - R.w y) := by rw [Finset.sum_sub_distrib]
    rw [hdiff]
    calc
      |∑ y ∈ A, (Q.w y - R.w y)| ≤ ∑ y ∈ A, |Q.w y - R.w y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |Q.w y - R.w y| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        intro y hy hnot
        positivity
      _ ≤ 2 * δ := hQR
  have hQmass : 0 < ∑ y ∈ A, Q.w y := by
    have hgap : m / 4 ≤ ∑ y ∈ A, Q.w y := by
      have := (abs_le.mp hmassdiff).1
      dsimp [m] at hRmassLower hδm ⊢
      linarith
    exact lt_of_lt_of_le (by positivity) hgap
  let ρ : Law N := R.restrict A hRmass
  let s : Fin N → ℝ := fun y => (ψ y - mψ) / (1 + mψ)
  have hsbound (y : Fin N) : |s y| ≤ 4 * B := by
    have hnum : |ψ y - mψ| ≤ 2 * B := by
      rw [abs_sub_comm]
      calc
        |mψ - ψ y| = |mψ + -ψ y| := by congr 1 <;> ring
        _ ≤ |mψ| + |-ψ y| := abs_add_le _ _
        _ = |mψ| + |ψ y| := by simp
        _ ≤ B + B := add_le_add hmψ (hψ y)
        _ = 2 * B := by ring
    have hdenle : 1 / 2 ≤ 1 + mψ := by
      have h := (abs_le.mp hmψ).1
      linarith
    change |(ψ y - mψ) / (1 + mψ)| ≤ 4 * B
    rw [abs_div, abs_of_pos hden]
    exact (div_le_iff₀ hden).2 (by nlinarith [hnum, hdenle])
  have hsmean : ∑ y, lamA.w y * s y = 0 := by
    have hsum : (∑ y, lamA.w y * (ψ y - mψ)) = 0 := by
      calc
        (∑ y, lamA.w y * (ψ y - mψ)) =
            (∑ y, lamA.w y * ψ y) - ∑ y, lamA.w y * mψ := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = mψ - mψ := by
              have hconst : ∑ y, lamA.w y * mψ = mψ := by
                rw [← Finset.sum_mul, lamA.sum_eq_one]
                ring
              change mψ - (∑ y, lamA.w y * mψ) = mψ - mψ
              rw [hconst]
        _ = 0 := by ring
    calc
      (∑ y, lamA.w y * s y) =
          ∑ y, (lamA.w y * (ψ y - mψ)) / (1 + mψ) := by
            apply Finset.sum_congr rfl
            intro y hy
            simp [s]
            ring
      _ = (∑ y, lamA.w y * (ψ y - mψ)) / (1 + mψ) := by rw [Finset.sum_div]
      _ = 0 := by rw [hsum]; simp
  have hTilt (y : Fin N) : ρ.w y = (1 + s y) * lamA.w y := by
    by_cases hy : y ∈ A
    · have hLamWeight : lamA.w y = ν.w y / m := by simp [lamA, Law.restrict, hy, m]
      have hρ : ρ.w y = R.w y / (∑ z ∈ A, R.w z) := by
        simp [ρ, Law.restrict, hy]
      rw [hρ, hRw, hRmass_formula, hLamWeight]
      change ((1 + ψ y) * ν.w y / Z) / (m * (1 + mψ) / Z) =
        (1 + (ψ y - mψ) / (1 + mψ)) * (ν.w y / m)
      field_simp [ne_of_gt hZ, ne_of_gt hm', ne_of_gt hden]
      ring
    · have hLamWeight : lamA.w y = 0 := by simp [lamA, Law.restrict, hy]
      have hρ : ρ.w y = 0 := by simp [ρ, Law.restrict, hy]
      rw [hρ, hLamWeight]
      ring
  have hrestrict := law_restrict_l1_bound9 Q R A hQmass hRmass (2 * δ) hQR
  refine ⟨hQmass, lamA, ρ, s, rfl, hsbound, hsmean, hTilt, ?_⟩
  have hmQ : m / 4 ≤ ∑ y ∈ A, Q.w y := by
    have := (abs_le.mp hmassdiff).1
    dsimp [m] at hRmassLower hδm ⊢
    linarith
  have hbound := hrestrict
  have hdenom : 0 < m / 4 := by positivity
  have hdiv : 2 * (2 * δ) / (∑ y ∈ A, Q.w y) ≤ 16 * δ / m := by
    have hsumNonneg : 0 ≤ ∑ y, |Q.w y - (1 + ψ y) * ν.w y| :=
      Finset.sum_nonneg fun y hy => abs_nonneg _
    have hδnonneg : 0 ≤ δ := le_trans hsumNonneg herr
    have hle := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 4 * δ)
      hdenom hmQ
    have hcalc : (4 * δ) / (m / 4) = 16 * δ / m := by field_simp [ne_of_gt hm']; ring
    calc
      2 * (2 * δ) / (∑ y ∈ A, Q.w y) = (4 * δ) / (∑ y ∈ A, Q.w y) := by ring
      _ ≤ (4 * δ) / (m / 4) := hle
      _ = 16 * δ / m := hcalc
  exact le_trans hbound hdiv

private theorem rowDeg_centered_tilt9 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (x : Fin N) (lam rho : Law N) (s f : Fin N → ℝ) (B : ℝ)
    (hTilt : ∀ y, rho.w y = (1 + s y) * lam.w y)
    (hmean : ∑ y, lam.w y * s y = 0)
    (hscale : ∀ y, s y = 4 * B * f y) :
    rowDeg E G x rho - rowDeg E G x lam =
      4 * B * ∑ y, lam.w y * ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * f y := by
  classical
  let hit : Fin N → ℝ := fun y => if Hits E G x y then 1 else 0
  change rowDeg E G x rho - rowDeg E G x lam =
    4 * B * ∑ y, lam.w y * (hit y - 1 / 2) * f y
  have hraw : rowDeg E G x rho - rowDeg E G x lam =
      ∑ y, lam.w y * s y * hit y := by
    unfold rowDeg
    calc
      (∑ y, rho.w y * hit y) - ∑ y, lam.w y * hit y =
          ∑ y, (rho.w y * hit y - lam.w y * hit y) := by rw [← Finset.sum_sub_distrib]
      _ = ∑ y, lam.w y * s y * hit y := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hTilt y]
        dsimp [hit]
        ring
  have hcenter :
      ∑ y, lam.w y * s y * (hit y - 1 / 2) = ∑ y, lam.w y * s y * hit y := by
    calc
      ∑ y, lam.w y * s y * (hit y - 1 / 2) =
          (∑ y, lam.w y * s y * hit y) - (1 / 2) * (∑ y, lam.w y * s y) := by
            calc
              ∑ y, lam.w y * s y * (hit y - 1 / 2) =
                  ∑ y, (lam.w y * s y * hit y - (1 / 2) * (lam.w y * s y)) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
              _ = (∑ y, lam.w y * s y * hit y) -
                    ∑ y, (1 / 2) * (lam.w y * s y) := by rw [← Finset.sum_sub_distrib]
              _ = (∑ y, lam.w y * s y * hit y) -
                    (1 / 2) * (∑ y, lam.w y * s y) := by rw [← Finset.mul_sum]
      _ = ∑ y, lam.w y * s y * hit y := by rw [hmean]; ring
  calc
    rowDeg E G x rho - rowDeg E G x lam = ∑ y, lam.w y * s y * hit y := hraw
    _ = ∑ y, lam.w y * s y * (hit y - 1 / 2) := hcenter.symm
    _ = ∑ y, (4 * B) * (lam.w y * (hit y - 1 / 2) * f y) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hscale y]
          ring
    _ = 4 * B * ∑ y, lam.w y * (hit y - 1 / 2) * f y := by rw [Finset.mul_sum]

private theorem absorb_subpower9 {u χ H c L : ℝ} (hu : 0 < u) (hχ : χ < u)
    (hH : 0 ≤ H) (hc : 0 < c) (hL : 0 < L) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      L * (n : ℝ) ^ χ + H * Real.log (n : ℝ) ≤ c * (n : ℝ) ^ u := by
  have hlogLittle : (fun x : ℝ => (2 * H / c) * Real.log x) =o[atTop] fun x => x ^ u := by
    have hl := (isLittleO_log_rpow_rpow_atTop 1 hu).const_mul_left (2 * H / c)
    simpa using hl
  have hlogNat : (fun n : ℕ => (2 * H / c) * Real.log (n : ℝ)) =o[atTop]
      fun n => (n : ℝ) ^ u := by
    exact (hlogLittle.comp_tendsto tendsto_natCast_atTop_atTop).congr_left (fun _ => rfl)
  obtain ⟨nL, hLlog⟩ := Filter.eventually_atTop.mp hlogNat.eventuallyLE
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ (χ - u)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ ((tendsto_rpow_neg_atTop (sub_pos.mpr hχ)).comp tendsto_natCast_atTop_atTop)
    filter_upwards [] with n
    rw [show χ - u = -(u - χ) by ring]
    simp only [Function.comp_apply]
  have hratioSmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (χ - u) < c / (2 * L) := by
    have hboundPos : 0 < c / (2 * L) := div_pos hc (mul_pos (by norm_num) hL)
    exact hratio.eventually (Iio_mem_nhds hboundPos)
  obtain ⟨nR, hR⟩ := Filter.eventually_atTop.mp hratioSmall
  refine ⟨max (max nL nR) 2, ?_⟩
  intro n hn
  have hnLR : max nL nR ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnL : nL ≤ n := le_trans (Nat.le_max_left _ _) hnLR
  have hnR : nR ≤ n := le_trans (Nat.le_max_right _ _) hnLR
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hpowPos : 0 < (n : ℝ) ^ u := Real.rpow_pos_of_pos hnPos _
  have hcoef : 0 ≤ 2 * H / c := div_nonneg (mul_nonneg (by norm_num) hH) hc.le
  have hlogBound : (2 * H / c) * Real.log (n : ℝ) ≤ (n : ℝ) ^ u := by
    have h := hLlog n hnL
    have hleft : 0 ≤ (2 * H / c) * Real.log (n : ℝ) := mul_nonneg hcoef hlogNonneg
    simpa [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hpowPos.le] using h
  have hratioN : (n : ℝ) ^ (χ - u) < c / (2 * L) := hR n hnR
  have hratioPow : (n : ℝ) ^ (χ - u) = (n : ℝ) ^ χ / (n : ℝ) ^ u :=
    Real.rpow_sub hnPos χ u
  rw [hratioPow] at hratioN
  have hratioStep := (div_lt_iff₀ hpowPos).mp hratioN
  have hmul := mul_lt_mul_of_pos_left hratioStep hL
  have hright : L * (c / (2 * L) * (n : ℝ) ^ u) = c / 2 * (n : ℝ) ^ u := by
    field_simp [ne_of_gt hL]
  have hpowBound : L * (n : ℝ) ^ χ ≤ c / 2 * (n : ℝ) ^ u := by
    exact le_of_lt (by rw [← hright]; exact hmul)
  calc
    L * (n : ℝ) ^ χ + H * Real.log (n : ℝ) ≤
        c / 2 * (n : ℝ) ^ u + c / 2 * (n : ℝ) ^ u := by
          apply add_le_add hpowBound
          have := hlogBound
          have hfactor : H * Real.log (n : ℝ) = (c / 2) * ((2 * H / c) * Real.log (n : ℝ)) := by
            field_simp [ne_of_gt hc]
          rw [hfactor]
          exact mul_le_mul_of_nonneg_left hlogBound (by positivity)
    _ = c * (n : ℝ) ^ u := by ring

private theorem boundedRegularityTest_probability_le9 {P : Params9} (hP : P.Valid)
    {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n)
    (hCore : CoreInput9 P κ E X Y G M S I) (v : EvenSites9 n)
    (q : BoundedRegularityTestIndex9 I v) (hPoly : Real.log (100 / 49) ≤ (n : ℝ) ^ P.u) :
    (rawLaw9 S I).pr (badBoundedRegularityTest9 S I E G v q) ≤
      2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
  classical
  rcases hP with ⟨_, _, _, _, hChi, _, _⟩
  have hχpos : 0 < (P.χ : ℝ) := by exact_mod_cast hChi.1
  rcases hCore with ⟨hN, hPrep, hDeep, hTags, hMasks, hTools, hScale, hAt⟩
  rcases hPrep with ⟨_, hPrepLaw⟩
  rcases hScale with ⟨_, _, hu, _, _⟩
  rcases hAt with ⟨hn, _, _, _, hfilter, hfirst, _, _⟩
  let edge : StarOdd9 v := q.1.1
  let t : Fin 3 := q.1.2
  let ord := regularityOrder9 S I v edge.1 t
  by_cases hvalid : q.2.val < ord.length
  · let k : Fin ord.length := ⟨q.2.val, hvalid⟩
    let c : I.ID := ord[k.val]
    let w : ℝ := (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1
    have hwd : w ≤ (n : ℝ) ^ (P.xD : ℝ) := by
      dsimp [w]
      have hextra : 0 ≤ (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) := by positivity
      calc
        (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 ≤
            (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 +
              (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) := by linarith
        _ ≤ (n : ℝ) ^ (P.xD : ℝ) := hfirst
    have hgap : w - (n : ℝ) ^ (P.xD : ℝ) ≤ -((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))) := by
      dsimp [w]
      linarith [hfirst]
    let α : Law N := M.μ (S.tag c.slice)
    have htagC := hTags c.slice
    rcases hPrepLaw (S.tag c.slice) htagC with ⟨hαX, _, hαW, _, _⟩
    let ν : Law N := siteSecond9 S edge.1
    let tagEdge := S.tag (specialWord9 (P.m n) edge.1.1)
    have htagEdge := hTags (specialWord9 (P.m n) edge.1.1)
    rcases hPrepLaw tagEdge htagEdge with ⟨_, hνY₀, _, hνW₀, _⟩
    have hνY : ν.SupportedIn Y := by simpa [ν, siteSecond9, tagEdge] using hνY₀
    have hνW : ν.WidthLE (P.Ss (n : ℝ)) := by simpa [ν, siteSecond9, tagEdge] using hνW₀
    have htest : (FinProb.pi (inputLaw9 S I)).pr (badBoundedRegularityTest9 S I E G v q) ≤
        2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
      refine pi_pr_slice_le (inputLaw9 S I) (Sum.inl c)
        (fun ω => badBoundedRegularityTest9 S I E G v q ω)
        (2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))))) ?_
      intro ξ hξ
      let ωbase : Outcome9 I N := fun j =>
        if h : j = Sum.inl c then
          cast (congrArg (Val9 I N) h.symm)
            (Classical.choice (nonempty_of_probability (inputLaw9 S I (Sum.inl c))))
        else ξ ⟨j, h⟩
      change (inputLaw9 S I (Sum.inl c)).pr
        (fun x => badBoundedRegularityTest9 S I E G v q
          (Function.update ωbase (Sum.inl c) x)) ≤
          2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))))
      have hprod :
          ∏ j : {j // j ∉ ({Sum.inl c} : Finset (I.ID ⊕ OddSites9 n))},
              (inputLaw9 S I j.1).w (ξ ⟨j.1, by simpa using j.2⟩) ≠ 0 := by
        simpa [FinProb.pi] using hξ
      let jm : {j // j ∉ ({Sum.inl c} : Finset (I.ID ⊕ OddSites9 n))} :=
        ⟨Sum.inr edge.1, by simp⟩
      have hmaskW : (S.maskLaw edge.1).w (msk9 ωbase edge.1) ≠ 0 := by
        have hfactor := (Finset.prod_ne_zero_iff.mp hprod) jm (Finset.mem_univ jm)
        simpa [inputLaw9, msk9, ωbase, jm, Sum.inr_ne_inl] using hfactor
      have hmaskMass := hMasks.1 edge.1 (msk9 ωbase edge.1) hmaskW
      let mask := msk9 ωbase edge.1
      have hlow : 0 < (1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ P.u)) :=
        mul_pos (by norm_num) (Real.exp_pos (-((n : ℝ) ^ P.u)))
      have hmaskMass' : (1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ P.u)) ≤
          ∑ y ∈ mask, ν.w y := by simpa [ν, mask] using hmaskMass
      have hmaskPos : 0 < ∑ y ∈ mask, ν.w y := by
        exact lt_of_lt_of_le hlow hmaskMass'
      have hmaskLog := mask_log_bound9 hmaskMass'
      have hmaskEq : maskedLaw9 S ωbase edge.1 = ν.restrict mask hmaskPos := by
        unfold maskedLaw9 restrictOr9
        rw [dif_pos hmaskPos]
      let base0 := regularityBase9 S I edge.1 ωbase t
      have hbaseY : base0.SupportedIn Y := by
        intro y hy
        by_cases ht : t.val = 0
        · have hbaseEq : base0 = maskedLaw9 S ωbase edge.1 := by
            simp [base0, regularityBase9, ht]
          rw [hbaseEq, hmaskEq]
          by_cases hmem : y ∈ mask
          · simp [Law.restrict, hmem, hνY y hy]
          · simp [Law.restrict, hmem]
        · simpa [base0, regularityBase9, ht, ν] using hνY y hy
      let baseBudget := P.Ss (n : ℝ) + (n : ℝ) ^ P.u + Real.log 2
      have hbaseW : base0.WidthLE baseBudget := by
        by_cases ht : t.val = 0
        · have hbaseEq : base0 = maskedLaw9 S ωbase edge.1 := by
            simp [base0, regularityBase9, ht]
          rw [hbaseEq, hmaskEq]
          apply Law.WidthLE.mono (Law.WidthLE.restrict hνW hmaskPos)
          dsimp [baseBudget]
          linarith [hmaskLog]
        · have hbaseEq : base0 = ν := by simp [base0, regularityBase9, ht, ν]
          rw [hbaseEq]
          apply Law.WidthLE.mono hνW
          dsimp [baseBudget]
          have hnu : 0 ≤ (n : ℝ) ^ P.u := by positivity
          have hlog2 : 0 ≤ Real.log 2 := by positivity
          linarith
      let lam9 := prefixLaw9 E G ωbase base0 ord k.val
      have hnodup := regularityOrder_nodup9 S I v edge t
      have hprevEquiv (x : Fin N) :
          prefixRegularBefore9 S I E G v edge t k (Function.update ωbase (Sum.inl c) x) ↔
            prefixRegularBefore9 S I E G v edge t k ωbase := by
        exact prefixRegularBefore_update9 S I E G v edge t k ωbase hnodup x
      by_cases hgood : prefixRegularBefore9 S I E G v edge t k ωbase
      · have hprev_update (x : Fin N) :
          prefixRegularBefore9 S I E G v edge t k (Function.update ωbase (Sum.inl c) x) →
            prefixRegularBefore9 S I E G v edge t k ωbase := by
          intro hp
          exact (hprevEquiv x).mp hp
        have hmassLB : (49 / 100 : ℝ) ^ k.val ≤ prefixMass9 E G ωbase base0 ord k.val := by
          exact prefixMass_lower9 S I E G ωbase base0 ord k.val (Nat.le_of_lt k.isLt) hgood
        have hmassPos : 0 < prefixMass9 E G ωbase base0 ord k.val := by
          exact lt_of_lt_of_le (by positivity) hmassLB
        let A := hitSet9 E G ωbase (ord.take k.val).toFinset
        have hmassA : 0 < ∑ y ∈ A, base0.w y := by
          simpa [prefixMass9, A] using hmassPos
        have hprefixEq : lam9 = base0.restrict A hmassPos := by
          change restrictOr9 base0 A = base0.restrict A hmassPos
          unfold restrictOr9
          rw [dif_pos hmassA]
        have hLamY : lam9.SupportedIn Y := by
          rw [hprefixEq]
          exact law_restrict_supported9 hbaseY hmassA
        have hseenR : ((I.seen edge.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := by
          simpa [IDMap9.seen] using I.odd_ids edge.1.1 edge.1.2
        have hlenOrd := regularityOrder_length_le_seen_add_one9 S I v edge t
        have hkR : (k.val : ℝ) ≤ P.idBudget n + (P.m n : ℝ) + 1 := by
          have hkN : k.val ≤ ord.length := Nat.le_of_lt k.isLt
          have hkN' : k.val ≤ (I.seen edge.1).card + 1 := le_trans hkN hlenOrd
          have hkCast : (k.val : ℝ) ≤ (I.seen edge.1).card + 1 := by exact_mod_cast hkN'
          linarith
        have hlogRatioPos : 0 < Real.log (100 / 49) := Real.log_pos (by norm_num)
        have hratioMass := prefix_log_bound9 hmassLB
        have hbudget : baseBudget - Real.log (prefixMass9 E G ωbase base0 ord k.val) ≤
            P.filterBudget n + (n : ℝ) ^ P.u := by
          have hkL := mul_le_mul_of_nonneg_right hkR hlogRatioPos.le
          have hbudgetEq : baseBudget +
              (P.idBudget n + (P.m n : ℝ) + 1) * Real.log (100 / 49) =
                P.filterBudget n + Real.log (100 / 49) := by
            simp [baseBudget, Params9.filterBudget]
            ring
          calc
            baseBudget - Real.log (prefixMass9 E G ωbase base0 ord k.val) ≤
                baseBudget + (k.val : ℝ) * Real.log (100 / 49) := by linarith
            _ ≤ baseBudget + (P.idBudget n + (P.m n : ℝ) + 1) * Real.log (100 / 49) :=
              add_le_add_right hkL baseBudget
            _ = P.filterBudget n + Real.log (100 / 49) := hbudgetEq
            _ ≤ P.filterBudget n + (n : ℝ) ^ P.u := by linarith [hPoly]
        have hLamW : lam9.WidthLE (P.Sd (n : ℝ)) := by
          rw [hprefixEq]
          apply Law.WidthLE.mono (Law.WidthLE.restrict hbaseW hmassPos)
          exact le_trans hbudget hfilter
        let outlier : Fin N → Prop := fun x =>
          2 * P.bStar n < |rowDeg E G x lam9 - 1 / 2|
        have hforward := hTools.1 G lam9 hLamY hLamW α hαX w hαW hwd
        have houtlier : α.pr outlier ≤ 2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
          simpa [outlier, FinProb.pr, Finset.sum_filter] using hforward
        have hsubset (x : Fin N) :
            badBoundedRegularityTest9 S I E G v q (Function.update ωbase (Sum.inl c) x) → outlier x := by
          intro hb
          rcases hb with ⟨k', hval, hp⟩
          have hk' : k' = k := Fin.ext (by simpa [k] using hval)
          rw [hk'] at hp
          rcases hp with ⟨hprev, hout⟩
          have hprev0 := hprev_update x hprev
          have hbaseEq : regularityBase9 S I edge.1 (Function.update ωbase (Sum.inl c) x) t = base0 :=
            regularityBase_update9 S I edge.1 ωbase c x t
          have hnot : c ∉ (ord.take k.val).toFinset := by
            change ord[k.val] ∉ (ord.take k.val).toFinset
            exact nodup_getElem_not_mem_take hnodup k
          have hprefix :
              prefixLaw9 E G (Function.update ωbase (Sum.inl c) x)
                (regularityBase9 S I edge.1 (Function.update ωbase (Sum.inl c) x) t) ord k.val = lam9 := by
            rw [hbaseEq]
            exact @prefixLaw_update_anchor9 P n N M I E G ωbase c x base0 ord k.val hnot
          have hanc : anc9 (Function.update ωbase (Sum.inl c) x) c = x := by
            simp [anc9, Function.update]
          have hout' := hout
          rw [hanc, hprefix] at hout'
          exact hout'
        have hslice := FinProb.pr_mono (inputLaw9 S I (Sum.inl c))
          (fun x => badBoundedRegularityTest9 S I E G v q
            (Function.update ωbase (Sum.inl c) x)) outlier hsubset
        calc
          (inputLaw9 S I (Sum.inl c)).pr
              (fun x => badBoundedRegularityTest9 S I E G v q
                (Function.update ωbase (Sum.inl c) x)) ≤ α.pr outlier := by
                  change (inputLaw9 S I (Sum.inl c)).pr
                    (fun x => badBoundedRegularityTest9 S I E G v q
                      (Function.update ωbase (Sum.inl c) x)) ≤
                    (inputLaw9 S I (Sum.inl c)).pr outlier
                  exact hslice
          _ ≤ 2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := houtlier
          _ ≤ 2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
                exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgap) (by norm_num)
      · have hfalse (x : Fin N) :
            ¬ badBoundedRegularityTest9 S I E G v q (Function.update ωbase (Sum.inl c) x) := by
          intro hb
          rcases hb with ⟨k', hval, hp⟩
          have hk' : k' = k := Fin.ext (by simpa [k] using hval)
          rw [hk'] at hp
          exact hgood ((hprevEquiv x).mp hp.1)
        have hzero : (inputLaw9 S I (Sum.inl c)).pr
            (fun x => badBoundedRegularityTest9 S I E G v q
              (Function.update ωbase (Sum.inl c) x)) = 0 := by
          unfold FinProb.pr
          apply Finset.sum_eq_zero
          intro x hx
          simp [hfalse x]
        rw [hzero]
        positivity
    have htestRaw : (rawLaw9 S I).pr (badBoundedRegularityTest9 S I E G v q) ≤
        2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
      change (FinProb.pi (inputLaw9 S I)).pr (badBoundedRegularityTest9 S I E G v q) ≤ _
      exact htest
    exact htestRaw
  · have hfalse : ∀ ω, ¬ badBoundedRegularityTest9 S I E G v q ω := by
      intro ω hb
      rcases (by simpa [badBoundedRegularityTest9, edge, t, ord] using hb) with ⟨k, hval, _⟩
      exact hvalid (by rw [← hval]; exact k.isLt)
    have hzero : (rawLaw9 S I).pr (badBoundedRegularityTest9 S I E G v q) = 0 := by
      simp [FinProb.pr, hfalse]
    rw [hzero]
    positivity

theorem regularity_certificate9 (P : Params9) (hP : P.Valid) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c := by
  have hPvalid : P.Valid := hP
  have hxS : 0 < (P.xS : ℝ) := by exact_mod_cast hP.1.1
  rcases hP with ⟨_, _, _, _, hChi, _, _⟩
  have hχpos : 0 < (P.χ : ℝ) := by exact_mod_cast hChi.1
  have hu : 0 < P.u := by
    dsimp [Params9.u]
    exact div_pos hxS (by norm_num)
  obtain ⟨n₀, htail⟩ := regularity_polynomial_tail9 hu hχpos
  refine ⟨1 / 2, by norm_num, n₀, ?_⟩
  intro n hn N E X Y κ G M S I hCore
  have hpoly := htail n hn
  rcases hCore with ⟨hN, hPrep, hDeep, hTags, hMasks, hTools, hScale, hAt⟩
  have hCore' : CoreInput9 P κ E X Y G M S I :=
    ⟨hN, hPrep, hDeep, hTags, hMasks, hTools, hScale, hAt⟩
  intro v
  let Ev : Outcome9 I N → Prop := fun ω => ¬ starRegular9 S E G ω v
  let Test : BoundedRegularityTestIndex9 I v → Outcome9 I N → Prop :=
    fun q ω => badBoundedRegularityTest9 S I E G v q ω
  have hcover : ∀ ω, Ev ω → ∃ q, Test q ω := by
    intro ω hω
    simpa [Ev, Test] using
      exists_badBoundedRegularityTest9 S I E G ω v hScale hAt hω
  have hmono := FinProb.pr_mono (rawLaw9 S I) Ev (fun ω => ∃ q, Test q ω) hcover
  have hunion := FinProb.pr_exists_le_sum5 (rawLaw9 S I) Test
  have hcount := boundedRegularityTestIndex_card_le9 S I v hScale hAt
  have hcountR : (Fintype.card (BoundedRegularityTestIndex9 I v) : ℝ) ≤
      9 * (n : ℝ) ^ 2 := by exact_mod_cast hcount
  have hsum :
      ∑ q : BoundedRegularityTestIndex9 I v, (rawLaw9 S I).pr (Test q) ≤
        ∑ q : BoundedRegularityTestIndex9 I v,
          2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
    apply Finset.sum_le_sum
    intro q hq
    exact boundedRegularityTest_probability_le9 hPvalid S I hCore' v q hpoly.2
  calc
    (rawLaw9 S I).pr Ev ≤ (rawLaw9 S I).pr (fun ω => ∃ q, Test q ω) := hmono
    _ ≤ ∑ q, (rawLaw9 S I).pr (Test q) := hunion
    _ ≤ ∑ q, 2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := hsum
    _ = (Fintype.card (BoundedRegularityTestIndex9 I v) : ℝ) *
          (2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))))) := by simp
    _ ≤ (9 * (n : ℝ) ^ 2) *
          (2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))))) :=
      mul_le_mul_of_nonneg_right hcountR (by positivity)
    _ = 18 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by ring
    _ ≤ Real.exp (-((n : ℝ) ^ P.u / 2)) := hpoly.1
    _ = P.tail (1 / 2) n := by
      simp [Params9.tail]
      congr 1
      ring

private theorem one_sign_mass {N : ℕ} {X : Finset (Fin N)}
    {wX err w : ℝ} (α : Law N)
    (hαX : α.SupportedIn X) (hαW : α.WidthLE w)
    (f : Fin N → ℝ)
    (hmean : ∀ ρ : Law N, ρ.SupportedIn X → ρ.WidthLE wX →
      |∑ x, ρ.w x * f x| ≤ err)
    (S : Finset (Fin N)) (hside : ∀ x ∈ S, err < f x) :
    ∑ x ∈ S, α.w x ≤ Real.exp (w - wX) := by
  classical
  by_contra hnot
  have hmass : Real.exp (w - wX) < ∑ x ∈ S, α.w x := lt_of_not_ge hnot
  have hmasspos : 0 < ∑ x ∈ S, α.w x := lt_trans (Real.exp_pos _) hmass
  let ρ : Law N := α.restrict S hmasspos
  have hlog : w - wX < Real.log (∑ x ∈ S, α.w x) := by
    have h := Real.log_lt_log (Real.exp_pos (w - wX)) hmass
    simpa only [Real.log_exp] using h
  have hρwidth : ρ.WidthLE wX := by
    apply Law.WidthLE.mono (Law.WidthLE.restrict hαW hmasspos)
    linarith
  have hρX : ρ.SupportedIn X := by
    intro x hx
    simp [ρ, Law.restrict, hαX x hx]
  have hρS : ρ.SupportedIn S := by
    intro x hx
    simp [ρ, Law.restrict, hx]
  have hρsumpos : 0 < ∑ x, ρ.w x := by
    rw [ρ.sum_eq_one]
    norm_num
  obtain ⟨x₀, hx₀, hx₀pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := ρ.w)
      (by intro x hx; exact ρ.nonneg x)).mp hρsumpos
  have hx₀S : x₀ ∈ S := by
    by_contra hx
    have hzero := hρS x₀ hx
    simp [hzero] at hx₀pos
  have havg : err < ∑ x, ρ.w x * f x := by
    have hconst : (∑ x, ρ.w x * err) = err := by
      rw [← Finset.sum_mul, ρ.sum_eq_one]
      ring
    rw [← hconst]
    apply Finset.sum_lt_sum
    · intro x hx
      by_cases hxS : x ∈ S
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hside x hxS)) (ρ.nonneg x)
      · simp [hρS x hxS]
    · exact ⟨x₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hside x₀ hx₀S) hx₀pos⟩
  have hbound := hmean ρ hρX hρwidth
  rcases abs_le.mp hbound with ⟨hlo, hhi⟩
  linarith

private theorem signed_test_row_tail9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hdeep : P.DeepAt n N E X Y) (G : Colour)
    (hn : 1 ≤ n)
    (α : Law N) (hαX : α.SupportedIn X) (w : ℝ) (hαW : α.WidthLE w)
    (hw : w ≤ (n : ℝ) ^ (P.xD : ℝ))
    (lamBase : Law N) (hBaseY : lamBase.SupportedIn Y) (s : ℝ)
    (hBaseW : lamBase.WidthLE (s - Real.log 4)) (hs : s ≤ P.Sd (n : ℝ))
    (f : Fin N → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    ∑ x ∈ Finset.univ.filter (fun x => 4 * P.bStar n <
      |∑ y, lamBase.w y * ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * f y|), α.w x ≤
      2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
  classical
  change DiscOne E X Y ((n : ℝ) ^ (P.xD : ℝ)) (P.Sd (n : ℝ)) (P.bStar n) at hdeep
  let g : Fin N → ℝ := fun x =>
    ∑ y, lamBase.w y * ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * f y
  have hmean (ρ : Law N) (hρX : ρ.SupportedIn X)
      (hρW : ρ.WidthLE ((n : ℝ) ^ (P.xD : ℝ))) :
      |∑ x, ρ.w x * g x| ≤ 4 * P.bStar n := by
    have hBaseW' : lamBase.WidthLE
        (P.Sd (n : ℝ) - Real.log (2 * (1 : ℝ) + 2)) := by
      have hh := Law.WidthLE.mono hBaseW (sub_le_sub_right hs _)
      have hlog4 : Real.log (2 * (1 : ℝ) + 2) = Real.log 4 := by norm_num
      simpa only [hlog4] using hh
    have hdisc := signedTest_of_discrepancy (show (0 : ℝ) ≤ 1 by norm_num)
      hdeep ρ lamBase hρX hBaseY hρW hBaseW' f hf G
    have heq : signedHitExpectation E G ρ lamBase f = ∑ x, ρ.w x * g x := by
      rfl
    calc
      |∑ x, ρ.w x * g x| = |signedHitExpectation E G ρ lamBase f| := by rw [heq]
      _ ≤ 2 * (1 + 1) * P.bStar n := hdisc
      _ = 4 * P.bStar n := by ring
  let Splus := Finset.univ.filter (fun x => 4 * P.bStar n < g x)
  let Sminus := Finset.univ.filter (fun x => 4 * P.bStar n < -g x)
  let Sbad := Finset.univ.filter (fun x => 4 * P.bStar n < |g x|)
  have hplus :
      ∑ x ∈ Finset.univ.filter (fun x => 4 * P.bStar n < g x), α.w x ≤
        Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
    apply one_sign_mass α hαX hαW (fun x => g x)
      (fun ρ hρX hρW => hmean ρ hρX hρW)
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hminus :
      ∑ x ∈ Finset.univ.filter (fun x => 4 * P.bStar n < -g x), α.w x ≤
        Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
    have hmeanNeg (ρ : Law N) (hρX : ρ.SupportedIn X)
        (hρW : ρ.WidthLE ((n : ℝ) ^ (P.xD : ℝ))) :
        |∑ x, ρ.w x * -g x| ≤ 4 * P.bStar n := by
      have hneg : (∑ x, ρ.w x * -g x) = -∑ x, ρ.w x * g x := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hneg]
      simpa only [abs_neg] using hmean ρ hρX hρW
    exact one_sign_mass α hαX hαW (fun x => -g x) hmeanNeg Sminus
      (by intro x hx; exact (Finset.mem_filter.mp hx).2)
  have hsubset : Sbad ⊆ Splus ∪ Sminus := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    by_cases hnonneg : 0 ≤ g x
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [abs_of_nonneg hnonneg] using hx'⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [abs_of_neg (lt_of_not_ge hnonneg)] at hx'
        exact hx'⟩
  have hdis : Disjoint Splus Sminus := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h₁ := (Finset.mem_filter.mp hx₁).2
    have h₂ := (Finset.mem_filter.mp hx₂).2
    have hb : 0 ≤ P.bStar n := by
      dsimp [Params9.bStar]
      have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
      exact le_of_lt (Real.rpow_pos_of_pos hnR _)
    linarith
  calc
    (∑ x ∈ Sbad, α.w x) ≤ ∑ x ∈ Splus ∪ Sminus, α.w x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun x hx _ => α.nonneg x)
    _ = (∑ x ∈ Splus, α.w x) + ∑ x ∈ Sminus, α.w x := by rw [Finset.sum_union hdis]
    _ ≤ Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) + Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) :=
      add_le_add hplus hminus
    _ = 2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by ring

private theorem dens_eq_rowDegree {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) : dens E G μ ν = ∑ x, μ.w x * rowDeg E G x ν := by
  classical
  simp only [dens, rowDeg]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

private theorem row_deviation_mean {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) :
    ∑ x, μ.w x * (rowDeg E G x ν - 1 / 2) = dens E G μ ν - 1 / 2 := by
  classical
  rw [dens_eq_rowDegree]
  calc
    (∑ x, μ.w x * (rowDeg E G x ν - 1 / 2)) =
        (∑ x, μ.w x * rowDeg E G x ν) - ∑ x, μ.w x * (1 / 2) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = (∑ x, μ.w x * rowDeg E G x ν) - 1 / 2 := by
          have hhalf : (∑ x, μ.w x * (1 / 2)) = 1 / 2 := by
            rw [← Finset.sum_mul, μ.sum_eq_one]
            ring
          rw [hhalf]

private theorem col_deviation_mean {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) :
    ∑ y, ν.w y * (colDeg E G μ y - 1 / 2) = dens E G μ ν - 1 / 2 := by
  classical
  have hdens : dens E G μ ν = ∑ y, ν.w y * colDeg E G μ y := by
    unfold dens colDeg
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hdens]
  calc
    (∑ y, ν.w y * (colDeg E G μ y - 1 / 2)) =
        (∑ y, ν.w y * colDeg E G μ y) - ∑ y, ν.w y * (1 / 2) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = (∑ y, ν.w y * colDeg E G μ y) - 1 / 2 := by
          have hhalf : (∑ y, ν.w y * (1 / 2)) = 1 / 2 := by
            rw [← Finset.sum_mul, ν.sum_eq_one]
            ring
          rw [hhalf]

/-- Degree outliers under the first law, by conditioning on either signed exceptional set. -/
theorem forward_bound {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hdeep : P.DeepAt n N E X Y) (G : Colour)
    (lam : Law N) (hlamY : lam.SupportedIn Y) (hlamW : lam.WidthLE (P.Sd (n : ℝ)))
    (α : Law N) (hαX : α.SupportedIn X) (w : ℝ) (hαW : α.WidthLE w)
    (hw : w ≤ (n : ℝ) ^ (P.xD : ℝ)) :
    ∑ x ∈ Finset.univ.filter (fun x => 2 * P.bStar n < |rowDeg E G x lam - 1 / 2|), α.w x ≤
      2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
  classical
  let err : ℝ := (n : ℝ) ^ (-(P.hMinus : ℝ))
  let W : ℝ := (n : ℝ) ^ (P.xD : ℝ)
  have hdisc : DiscOne E X Y W (P.Sd (n : ℝ)) err := by
    change DiscOne E X Y W (P.Sd (n : ℝ)) err at hdeep
    exact hdeep
  have herr_nonneg : 0 ≤ err := by
    dsimp [err]
    positivity
  have hbstar_nonneg : 0 ≤ P.bStar n := by
    dsimp [Params9.bStar]
    positivity
  let q : Fin N → ℝ := fun x => rowDeg E G x lam - 1 / 2
  let Splus : Finset (Fin N) := Finset.univ.filter (fun x => 2 * P.bStar n < q x)
  let Sminus : Finset (Fin N) := Finset.univ.filter (fun x => 2 * P.bStar n < -q x)
  have hmean (ρ : Law N) (hρX : ρ.SupportedIn X) (hρW : ρ.WidthLE W) :
      |∑ x, ρ.w x * (rowDeg E G x lam - 1 / 2)| ≤ err := by
    rw [row_deviation_mean]
    have hd := hdisc ρ lam hρX hlamY hρW hlamW G
    simpa [err] using hd
  have hplus : ∑ x ∈ Splus, α.w x ≤ Real.exp (w - W) := by
    apply one_sign_mass α hαX hαW
      (fun x => rowDeg E G x lam - 1 / 2)
    · intro ρ hρX hρW
      exact hmean ρ hρX hρW
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      dsimp [q] at hx'
      have hpow : P.bStar n = err := by
        simp [Params9.bStar, err]
      rw [hpow] at hx'
      linarith
  have hminus : ∑ x ∈ Sminus, α.w x ≤ Real.exp (w - W) := by
    apply one_sign_mass α hαX hαW
      (fun x => 1 / 2 - rowDeg E G x lam)
    · intro ρ hρX hρW
      have hm := hmean ρ hρX hρW
      have hneg : (∑ x, ρ.w x * (1 / 2 - rowDeg E G x lam)) =
          -∑ x, ρ.w x * (rowDeg E G x lam - 1 / 2) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hneg]
      simpa only [abs_neg] using hm
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      have hpow : P.bStar n = err := by
        simp [Params9.bStar, err]
      rw [hpow] at hx'
      dsimp [q] at hx'
      linarith
  let Sbad := Finset.univ.filter (fun x => 2 * P.bStar n < |q x|)
  have hsubset : Sbad ⊆ Splus ∪ Sminus := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    by_cases hqx : 0 ≤ q x
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · simpa [abs_of_nonneg hqx] using hx'
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · have habs : |q x| = -q x := abs_of_neg (lt_of_not_ge hqx)
        rw [habs] at hx'
        exact hx'
  have hdis : Disjoint Splus Sminus := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h₁ := (Finset.mem_filter.mp hx₁).2
    have h₂ := (Finset.mem_filter.mp hx₂).2
    linarith [hbstar_nonneg]
  calc
    (∑ x ∈ Sbad, α.w x) ≤ ∑ x ∈ Splus ∪ Sminus, α.w x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun x hx _ => α.nonneg x)
    _ = (∑ x ∈ Splus, α.w x) + ∑ x ∈ Sminus, α.w x := by rw [Finset.sum_union hdis]
    _ ≤ Real.exp (w - W) + Real.exp (w - W) := add_le_add hplus hminus
    _ = 2 * Real.exp (w - W) := by ring

/-- The transposed first-side estimate is the second-side degree test. -/
theorem reverse_bound {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hdeep : P.DeepAt n N E X Y) (G : Colour)
    (σ : Law N) (hσX : σ.SupportedIn X) (hσW : σ.WidthLE ((n : ℝ) ^ (P.xD : ℝ)))
    (lam : Law N) (hlamY : lam.SupportedIn Y) (s : ℝ)
    (hlamW : lam.WidthLE s) (hs : s ≤ P.Sd (n : ℝ)) :
    ∑ y ∈ Finset.univ.filter (fun y => 2 * P.bStar n < |colDeg E G σ y - 1 / 2|), lam.w y ≤
      2 * Real.exp (s - P.Sd (n : ℝ)) := by
  classical
  let err : ℝ := (n : ℝ) ^ (-(P.hMinus : ℝ))
  have hdisc : DiscOne (transposeRel E) Y X (P.Sd (n : ℝ)) ((n : ℝ) ^ (P.xD : ℝ)) err := by
    change DiscOne E X Y ((n : ℝ) ^ (P.xD : ℝ)) (P.Sd (n : ℝ)) err at hdeep
    exact (DiscOne.transpose_iff E X Y ((n : ℝ) ^ (P.xD : ℝ)) (P.Sd (n : ℝ)) err).mpr hdeep
  have herr_nonneg : 0 ≤ err := by
    dsimp [err]
    positivity
  have hbstar_nonneg : 0 ≤ P.bStar n := by
    dsimp [Params9.bStar]
    positivity
  let q : Fin N → ℝ := fun y => colDeg E G σ y - 1 / 2
  let Splus : Finset (Fin N) := Finset.univ.filter (fun y => 2 * P.bStar n < q y)
  let Sminus : Finset (Fin N) := Finset.univ.filter (fun y => 2 * P.bStar n < -q y)
  have hmean (ρ : Law N) (hρY : ρ.SupportedIn Y) (hρW : ρ.WidthLE (P.Sd (n : ℝ))) :
      |∑ y, ρ.w y * (rowDeg (transposeRel E) G y σ - 1 / 2)| ≤ err := by
    rw [row_deviation_mean]
    have hd := hdisc ρ σ hρY hσX hρW hσW G
    simpa [err] using hd
  have hrowEq (y : Fin N) : rowDeg (transposeRel E) G y σ = colDeg E G σ y := by
    exact (colDeg_transpose (transposeRel E) G σ y).symm.trans (by rfl)
  have hplus : ∑ y ∈ Splus, lam.w y ≤ Real.exp (s - P.Sd (n : ℝ)) := by
    apply one_sign_mass lam hlamY hlamW
      (fun y => rowDeg (transposeRel E) G y σ - 1 / 2)
    · intro ρ hρY hρW
      exact hmean ρ hρY hρW
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp [q] at hy'
      rw [← hrowEq] at hy'
      have hpow : P.bStar n = err := by simp [Params9.bStar, err]
      rw [hpow] at hy'
      linarith
  have hminus : ∑ y ∈ Sminus, lam.w y ≤ Real.exp (s - P.Sd (n : ℝ)) := by
    apply one_sign_mass lam hlamY hlamW
      (fun y => 1 / 2 - rowDeg (transposeRel E) G y σ)
    · intro ρ hρY hρW
      have hm := hmean ρ hρY hρW
      have hneg : (∑ y, ρ.w y * (1 / 2 - rowDeg (transposeRel E) G y σ)) =
          -∑ y, ρ.w y * (rowDeg (transposeRel E) G y σ - 1 / 2) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      rw [hneg]
      simpa only [abs_neg] using hm
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp [q] at hy'
      rw [← hrowEq] at hy'
      have hpow : P.bStar n = err := by simp [Params9.bStar, err]
      rw [hpow] at hy'
      linarith
  let Sbad := Finset.univ.filter (fun y => 2 * P.bStar n < |q y|)
  have hsubset : Sbad ⊆ Splus ∪ Sminus := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    by_cases hqy : 0 ≤ q y
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · simpa [abs_of_nonneg hqy] using hy'
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · have habs : |q y| = -q y := abs_of_neg (lt_of_not_ge hqy)
        rw [habs] at hy'
        exact hy'
  have hdis : Disjoint Splus Sminus := by
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    have h₁ := (Finset.mem_filter.mp hy₁).2
    have h₂ := (Finset.mem_filter.mp hy₂).2
    linarith [hbstar_nonneg]
  calc
    (∑ y ∈ Sbad, lam.w y) ≤ ∑ y ∈ Splus ∪ Sminus, lam.w y :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun y hy _ => lam.nonneg y)
    _ = (∑ y ∈ Splus, lam.w y) + ∑ y ∈ Sminus, lam.w y := by rw [Finset.sum_union hdis]
    _ ≤ Real.exp (s - P.Sd (n : ℝ)) + Real.exp (s - P.Sd (n : ℝ)) := add_le_add hplus hminus
    _ = 2 * Real.exp (s - P.Sd (n : ℝ)) := by ring

private theorem nat_rpow_decay_cutoff9 {a K : ℝ} (ha : 0 < a) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, K * (n : ℝ) ^ (-a) < 1 / 2 := by
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  have hbound : 0 < (1 / 2 : ℝ) / K := div_pos (by norm_num) hK
  have hevent := hT.eventually (Iio_mem_nhds hbound)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨n₀, ?_⟩
  intro n hn
  have hpow := hn₀ n hn
  calc
    K * (n : ℝ) ^ (-a) < K * ((1 / 2 : ℝ) / K) :=
      mul_lt_mul_of_pos_left hpow hK
    _ = 1 / 2 := by field_simp [ne_of_gt hK]

private theorem nat_rpow_growth_cutoff9 {u K : ℝ} (hu : 0 < u) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, K ≤ (n : ℝ) ^ u := by
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ u) atTop atTop := by
    exact (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (hT.eventually_ge_atTop K)
  exact ⟨n₀, hn₀⟩

private theorem coreCount_pos9 {P : Params9} {n : ℕ}
    (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n)
    (hAdj : (cube n).Adj v.1 b.1) :
    1 ≤ coreCount9 I v b := by
  classical
  have hcenterSeen : I.center v.1 ∈ I.seen b.1 := by
    unfold IDMap9.seen seenIDs9
    apply Finset.mem_image.mpr
    refine ⟨v.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact (cube n).adj_symm hAdj
  have hcenterCore : I.center v.1 ∈ I.core v.1 := I.center_mem_core v.1 v.2
  have hcenter : I.center v.1 ∈ I.seen b.1 ∩ I.core v.1 :=
    Finset.mem_inter.mpr ⟨hcenterSeen, hcenterCore⟩
  have hcard : 0 < (I.seen b.1 ∩ I.core v.1).card := Finset.card_pos.mpr ⟨_, hcenter⟩
  dsimp [coreCount9]
  exact hcard

set_option maxHeartbeats 1000000 in
theorem replace_certificate9 (P : Params9) (hP : P.Valid) (c₀ C₁ c₁ : ℝ)
    (hc₀ : 0 < c₀) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ}
      {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour}
      {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c₀ →
      EraseCert9 S I E G C₁ c₁ → ReplaceCert9 S I E G C c := by
  rcases hP with ⟨hxs, hhm, _, _, hchi, _, _⟩
  rcases hxs with ⟨hxSpos, _, _⟩
  rcases hhm with ⟨hminuspos, _, _⟩
  rcases hchi with ⟨hχpos, hχbound⟩
  have hminLe : min P.xS (min P.hMinus (1 - P.hPlus)) ≤ P.hMinus :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hχminusQ : P.χ < P.hMinus / 100 := by
    exact lt_of_lt_of_le hχbound (div_le_div_of_nonneg_right hminLe (by norm_num))
  have hu : 0 < P.u := by
    dsimp [Params9.u]
    exact_mod_cast (div_pos hxSpos (by norm_num : (0 : ℚ) < 2))
  have hχu : (P.χ : ℝ) < P.u := by
    have hχx : P.χ < P.xS / 100 := by
      exact lt_of_lt_of_le hχbound
        (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    dsimp [Params9.u]
    exact_mod_cast (by nlinarith [hχx, hxSpos] : P.χ < P.xS / 2)
  have hχminus : (P.χ : ℝ) < (P.hMinus : ℝ) := by
    have hq : (P.χ : ℝ) < (P.hMinus : ℝ) / 100 := by exact_mod_cast hχminusQ
    have hp : 0 < (P.hMinus : ℝ) := by exact_mod_cast hminuspos
    linarith
  have hχposR : 0 < (P.χ : ℝ) := by exact_mod_cast hχpos
  have hminusPosR : 0 < (P.hMinus : ℝ) := by exact_mod_cast hminuspos
  let a : ℝ := (P.hMinus : ℝ) - (P.χ : ℝ)
  have ha : 0 < a := by dsimp [a]; linarith
  let L : ℝ := Real.log (100 / 49)
  have hL : 0 < L := Real.log_pos (by norm_num)
  let H : ℝ := 2 * (P.hMinus : ℝ) + 4
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨nDecay, hDecay⟩ :=
    nat_rpow_decay_cutoff9 (a := a) (K := 8 * C₁) ha (by positivity)
  obtain ⟨nAbsorb, hAbsorb⟩ := absorb_subpower9 hu hχu hH (by positivity : 0 < c₁ / 2) hL
  obtain ⟨nPoly, hPoly⟩ := regularity_polynomial_tail9 hu hχposR
  let d : ℝ := min c₀ (1 / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdle₀ : d ≤ c₀ := min_le_left _ _
  have hdleHalf : d ≤ 1 / 2 := min_le_right _ _
  have hKtail : 0 < (2 * Real.log 2) / d := by
    apply div_pos
    · positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    · exact hd
  obtain ⟨nUnion, hUnion⟩ :=
    nat_rpow_growth_cutoff9 (u := P.u) (K := (2 * Real.log 2) / d) hu
  let C : ℝ := 16 * C₁ + 1
  have hC : 0 < C := by dsimp [C]; linarith
  let n₀ : ℕ := max (max (max nDecay nAbsorb) (max nPoly nUnion)) 2
  refine ⟨C, hC, d / 2, by positivity, n₀, ?_⟩
  intro n hn N E X Y κ G M S I hCore hRegular hErase
  have hnDecay : nDecay ≤ n := by dsimp [n₀] at hn; omega
  have hnAbsorb : nAbsorb ≤ n := by dsimp [n₀] at hn; omega
  have hnPoly : nPoly ≤ n := by dsimp [n₀] at hn; omega
  have hnUnion : nUnion ≤ n := by dsimp [n₀] at hn; omega
  have hnTwo : 2 ≤ n := by dsimp [n₀] at hn; omega
  rcases hCore with ⟨hN, hPrep, hDeep, hTags, hMasks, hTools, hScale, hAt⟩
  rcases hPrep with ⟨_, hPrepLaw⟩
  rcases hScale with ⟨hScaleχ, _, huScale, _, _⟩
  rcases hAt with ⟨hn, _, _, _, hfilter, hfirst, hbstar, _⟩
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnPos : 0 < (n : ℝ) := by linarith
  have hpowPos : 0 < (n : ℝ) ^ P.u := Real.rpow_pos_of_pos hnPos _
  have hAbsorbN := hAbsorb n hnAbsorb
  have hPolyN := hPoly n hnPoly
  have hUnionN := hUnion n hnUnion
  intro v b hAdj
  let target : I.ID := I.center v.1
  let kR : ℝ := coreCount9 I v b
  let bStar : ℝ := P.bStar n
  let B : ℝ := C₁ * kR * bStar
  let Q : Law N := outerMean9 S I E G v b
  let ν : Law N := siteSecond9 S b.1
  let alpha : Law N := siteFirst9 S v.1
  let w : ℝ := (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1
  have hbstarNonneg : 0 ≤ bStar := by
    dsimp [bStar, Params9.bStar]
    positivity
  have hkPos : 1 ≤ coreCount9 I v b := coreCount_pos9 I v b hAdj
  have hkNonneg : 0 ≤ kR := by dsimp [kR]; positivity
  have hkOne : 1 ≤ kR := by dsimp [kR]; exact_mod_cast hkPos
  have hseen : ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := by
    simpa [IDMap9.seen] using I.odd_ids b.1 b.2
  have hkCard : coreCount9 I v b ≤ (I.seen b.1).card := by
    dsimp [coreCount9]
    exact Finset.card_le_card (Finset.inter_subset_left)
  have hkSeen : kR ≤ P.idBudget n + (P.m n : ℝ) := by
    dsimp [kR]
    have hkCardR : (coreCount9 I v b : ℝ) ≤ (I.seen b.1).card := by exact_mod_cast hkCard
    linarith
  have hchiBudget : kR ≤ (n : ℝ) ^ (P.χ : ℝ) := by
    dsimp [kR, coreCount9]
    have hcard : ((I.core v.1).card : ℝ) ≤ (n : ℝ) ^ (P.χ : ℝ) := I.core_card v.1 v.2
    have hsub : (I.seen b.1 ∩ I.core v.1).card ≤ (I.core v.1).card := Finset.card_le_card Finset.inter_subset_right
    have hcast : ((I.seen b.1 ∩ I.core v.1).card : ℝ) ≤ (I.core v.1).card := by exact_mod_cast hsub
    exact hcast.trans hcard
  have htargetCore : target ∈ I.core v.1 := I.center_mem_core v.1 v.2
  have htargetNotCoreIDs : target ∉ coreIDs9 I v b := by
    intro hmem
    exact (Finset.mem_erase.mp hmem).1 rfl
  have hAlphaTag : 0 < M.Λ (S.tag (specialWord9 (P.m n) v.1)) := hTags _
  obtain ⟨hAlphaX, _, hAlphaW, _, _⟩ :=
    hPrepLaw (S.tag (specialWord9 (P.m n) v.1)) hAlphaTag
  have hAlphaX' : alpha.SupportedIn X := by simpa [alpha, siteFirst9] using hAlphaX
  have hAlphaW' : alpha.WidthLE w := by simpa [alpha, siteFirst9, w] using hAlphaW
  have hInputAlpha : inputLaw9 S I (Sum.inl target) = alpha := by
    dsimp [alpha, inputLaw9, siteFirst9, target]
    rw [I.center_slice]
  have hNuTag : 0 < M.Λ (S.tag (specialWord9 (P.m n) b.1)) := hTags _
  obtain ⟨_, hNuY, _, hNuW, _⟩ :=
    hPrepLaw (S.tag (specialWord9 (P.m n) b.1)) hNuTag
  have hNuY' : ν.SupportedIn Y := by simpa [ν, siteSecond9] using hNuY
  have hNuW' : ν.WidthLE (P.Ss (n : ℝ)) := by simpa [ν, siteSecond9] using hNuW
  have hwd : w ≤ (n : ℝ) ^ (P.xD : ℝ) := by
    dsimp [w]
    have hpow : 0 ≤ (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) := by positivity
    linarith [hfirst]
  have hgap : w - (n : ℝ) ^ (P.xD : ℝ) ≤
      -((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))) := by
    dsimp [w]
    linarith [hfirst]
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hBsmall : B ≤ 1 / 2 := by
    have hpowBound : (n : ℝ) ^ (P.χ : ℝ) * bStar ≤ (n : ℝ) ^ (-a) := by
      have hpowSub : (n : ℝ) ^ (P.χ : ℝ) * (n : ℝ) ^ (-(P.hMinus : ℝ)) =
          (n : ℝ) ^ (P.χ - (P.hMinus : ℝ)) := by
        calc
          (n : ℝ) ^ (P.χ : ℝ) * (n : ℝ) ^ (-(P.hMinus : ℝ)) =
              (n : ℝ) ^ ((P.χ : ℝ) + -(P.hMinus : ℝ)) := by
                rw [← Real.rpow_add hnPos]
          _ = (n : ℝ) ^ (P.χ - (P.hMinus : ℝ)) := by congr 1 <;> ring
      calc
        (n : ℝ) ^ (P.χ : ℝ) * bStar = (n : ℝ) ^ (P.χ : ℝ) * (n : ℝ) ^ (-(P.hMinus : ℝ)) := by
          simp [bStar, Params9.bStar]
        _ = (n : ℝ) ^ (P.χ - (P.hMinus : ℝ)) := hpowSub
        _ ≤ (n : ℝ) ^ (-a) := by
          rw [show (P.χ : ℝ) - (P.hMinus : ℝ) = -a by dsimp [a]; ring]
    have hBbound : B ≤ C₁ * (n : ℝ) ^ (-a) := by
      dsimp [B, kR]
      calc
        C₁ * (coreCount9 I v b : ℝ) * bStar ≤
            C₁ * ((n : ℝ) ^ (P.χ : ℝ)) * bStar := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hchiBudget hC₁.le) hbstarNonneg
        _ = C₁ * ((n : ℝ) ^ (P.χ : ℝ) * bStar) := by ring
        _ ≤ C₁ * (n : ℝ) ^ (-a) := mul_le_mul_of_nonneg_left hpowBound hC₁.le
    have hdecay := hDecay n hnDecay
    have hbound : B < 1 / 2 := calc
      B ≤ C₁ * (n : ℝ) ^ (-a) := hBbound
      _ ≤ 8 * C₁ * (n : ℝ) ^ (-a) := by nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) (-a), hC₁]
      _ < 1 / 2 := hdecay
    exact hbound.le
  have hnuLog : Real.log 2 ≤ (n : ℝ) ^ P.u := by
    have hlog : Real.log 2 ≤ Real.log (100 / 49) :=
      Real.log_le_log (by norm_num) (by norm_num)
    exact hlog.trans hPolyN.2
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hcountLog : kR * L ≤ L * (P.idBudget n + (P.m n : ℝ)) := by
    calc
      kR * L ≤ (P.idBudget n + (P.m n : ℝ)) * L :=
        mul_le_mul_of_nonneg_right hkSeen hL.le
      _ = L * (P.idBudget n + (P.m n : ℝ)) := by ring
  have hwidth : P.Ss (n : ℝ) + kR * L + Real.log 4 ≤ P.Sd (n : ℝ) := by
    have hfilter' : P.Ss (n : ℝ) + 2 * (n : ℝ) ^ P.u + Real.log 2 +
        L * (P.idBudget n + (P.m n : ℝ)) ≤ P.Sd (n : ℝ) := by
      simpa [Params9.filterBudget, L, two_mul, add_assoc, add_left_comm, add_comm] using hfilter
    rw [hlog4]
    linarith [hfilter', hcountLog, hnuLog]
  have hlog2n : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hnTwo)
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hAbsorbBudget : Real.log 16 + L * kR + 2 * (P.hMinus : ℝ) * Real.log (n : ℝ) ≤
      c₁ * (n : ℝ) ^ P.u := by
    have hAbsorbN' : L * (n : ℝ) ^ (P.χ : ℝ) +
        (2 * (P.hMinus : ℝ) + 4) * Real.log (n : ℝ) ≤
          (c₁ / 2) * (n : ℝ) ^ P.u := by
      simpa [H] using hAbsorbN
    have hLk : L * kR ≤ L * (n : ℝ) ^ (P.χ : ℝ) :=
      mul_le_mul_of_nonneg_left hchiBudget hL.le
    have hLog16Le : Real.log 16 ≤ 4 * Real.log (n : ℝ) := by
      rw [hlog16]
      exact mul_le_mul_of_nonneg_left hlog2n (by norm_num)
    have hExpTerms : Real.log 16 + 2 * (P.hMinus : ℝ) * Real.log (n : ℝ) ≤
        (2 * (P.hMinus : ℝ) + 4) * Real.log (n : ℝ) := by
      calc
        Real.log 16 + 2 * (P.hMinus : ℝ) * Real.log (n : ℝ) =
            2 * (P.hMinus : ℝ) * Real.log (n : ℝ) + Real.log 16 := by ring
        _ ≤ 2 * (P.hMinus : ℝ) * Real.log (n : ℝ) + 4 * Real.log (n : ℝ) :=
          add_le_add le_rfl hLog16Le
        _ = (2 * (P.hMinus : ℝ) + 4) * Real.log (n : ℝ) := by ring
    calc
      Real.log 16 + L * kR + 2 * (P.hMinus : ℝ) * Real.log (n : ℝ) ≤
          L * (n : ℝ) ^ (P.χ : ℝ) +
            (2 * (P.hMinus : ℝ) + 4) * Real.log (n : ℝ) := by
              calc
                Real.log 16 + L * kR + 2 * (P.hMinus : ℝ) * Real.log (n : ℝ) =
                    L * kR + (Real.log 16 + 2 * (P.hMinus : ℝ) * Real.log (n : ℝ)) := by ring
                _ ≤ L * (n : ℝ) ^ (P.χ : ℝ) +
                    (2 * (P.hMinus : ℝ) + 4) * Real.log (n : ℝ) := add_le_add hLk hExpTerms
      _ ≤ (c₁ / 2) * (n : ℝ) ^ P.u := hAbsorbN'
      _ ≤ c₁ * (n : ℝ) ^ P.u :=
        mul_le_mul_of_nonneg_right (by linarith : c₁ / 2 ≤ c₁) hpowPos.le
  rcases hErase v b hAdj with ⟨ψ, hψ, herr⟩
  let delta : ℝ := P.tail c₁ n
  have hdeltaRaw : delta = Real.exp (-(c₁ * (n : ℝ) ^ P.u)) := by
    simp [delta, Params9.tail]
  have hratioByMass : ∀ m : ℝ,
      (49 / 100 : ℝ) ^ coreCount9 I v b ≤ m →
      delta ≤ m / 24 ∧ 16 * delta / m ≤ bStar ^ 2 := by
    intro m hmassLB
    have hmPos : 0 < m := lt_of_lt_of_le (by positivity) hmassLB
    have hmassLog := prefix_log_bound9 hmassLB
    have hmassLog' : -Real.log m ≤ kR * L := by
      simpa [kR, L] using hmassLog
    have hExp : Real.log 16 - c₁ * (n : ℝ) ^ P.u - Real.log m ≤
        -(2 * (P.hMinus : ℝ) * Real.log (n : ℝ)) := by
      linarith [hAbsorbBudget, hmassLog']
    have hratioEq : 16 * delta / m =
        Real.exp (Real.log 16 - c₁ * (n : ℝ) ^ P.u - Real.log m) := by
      rw [hdeltaRaw]
      calc
        16 * Real.exp (-(c₁ * (n : ℝ) ^ P.u)) / m =
            (Real.exp (Real.log 16) * Real.exp (-(c₁ * (n : ℝ) ^ P.u))) / m := by
              rw [Real.exp_log (by norm_num : (0 : ℝ) < 16)]
        _ = Real.exp (Real.log 16 - c₁ * (n : ℝ) ^ P.u) / m := by
              rw [← Real.exp_add]
              congr 1
        _ = Real.exp (Real.log 16 - c₁ * (n : ℝ) ^ P.u - Real.log m) := by
              have hmExp : m = Real.exp (Real.log m) := (Real.exp_log hmPos).symm
              calc
                Real.exp (Real.log 16 - c₁ * (n : ℝ) ^ P.u) / m =
                    Real.exp (Real.log 16 - c₁ * (n : ℝ) ^ P.u) /
                      Real.exp (Real.log m) := by conv_lhs => rw [hmExp]
                _ = Real.exp (Real.log 16 - c₁ * (n : ℝ) ^ P.u - Real.log m) :=
                      (Real.exp_sub _ _).symm
    have hBstarForm : bStar = Real.exp (-(P.hMinus : ℝ) * Real.log (n : ℝ)) := by
      dsimp [bStar, Params9.bStar]
      rw [Real.rpow_def_of_pos hnPos]
      exact congrArg Real.exp (by ring)
    have hBstarSq : bStar ^ 2 =
        Real.exp (-(2 * (P.hMinus : ℝ) * Real.log (n : ℝ))) := by
      rw [hBstarForm]
      calc
        Real.exp (-(P.hMinus : ℝ) * Real.log (n : ℝ)) ^ 2 =
            Real.exp (-(P.hMinus : ℝ) * Real.log (n : ℝ)) *
              Real.exp (-(P.hMinus : ℝ) * Real.log (n : ℝ)) := by ring
        _ = Real.exp (-(P.hMinus : ℝ) * Real.log (n : ℝ) +
              -(P.hMinus : ℝ) * Real.log (n : ℝ)) := (Real.exp_add _ _).symm
        _ = Real.exp (-(2 * (P.hMinus : ℝ) * Real.log (n : ℝ))) := by
              congr 1
              ring
    have hratio : 16 * delta / m ≤ bStar ^ 2 := by
      rw [hratioEq, hBstarSq]
      exact Real.exp_le_exp.mpr hExp
    have hbstarBound : bStar ≤ 1 / 200 := by simpa [bStar] using hbstar
    have hbstarSmall : bStar ^ 2 ≤ (1 / 200 : ℝ) ^ 2 := by
      have hprod : bStar * bStar ≤ (1 / 200 : ℝ) * (1 / 200) := by
        calc
          bStar * bStar ≤ (1 / 200 : ℝ) * bStar :=
            mul_le_mul_of_nonneg_right hbstarBound hbstarNonneg
          _ ≤ (1 / 200 : ℝ) * (1 / 200) :=
            mul_le_mul_of_nonneg_left hbstarBound (by norm_num)
      simpa [pow_two] using hprod
    have hdeltaDiv : delta / m ≤ 1 / 24 := by
      have hratio' : 16 * (delta / m) ≤ bStar ^ 2 := by
        calc
          16 * (delta / m) = 16 * delta / m := by ring
          _ ≤ bStar ^ 2 := hratio
      calc
        delta / m ≤ bStar ^ 2 / 16 :=
          (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2 (by simpa [mul_comm] using hratio')
        _ ≤ (1 / 200 : ℝ) ^ 2 / 16 :=
          div_le_div_of_nonneg_right hbstarSmall (by norm_num)
        _ ≤ 1 / 24 := by norm_num
    have hdeltaMass : delta ≤ m / 24 := by
      calc
        delta = (delta / m) * m := by field_simp [ne_of_gt hmPos]
        _ ≤ (1 / 24) * m := mul_le_mul_of_nonneg_right hdeltaDiv hmPos.le
        _ = m / 24 := by ring
    exact ⟨hdeltaMass, hratio⟩
  let coreRegular : Outcome9 I N → Prop := fun ω =>
    orderRegular9 E G ω ν (coreOrder9 I v b)
  let badReplace : Outcome9 I N → Prop := fun ω =>
    C * kR * bStar ^ 2 < |rowDeg E G (anc9 ω target)
      (restrictOr9 Q (coreHitSet9 E G ω v b)) -
        rowDeg E G (anc9 ω target)
          (restrictOr9 ν (coreHitSet9 E G ω v b))|
  let signedEvent : Outcome9 I N → Prop := fun ω => coreRegular ω ∧ badReplace ω
  change (rawLaw9 S I).pr badReplace ≤ P.tail (d / 2) n
  have hcoreFailure : (rawLaw9 S I).pr (fun ω => ¬ coreRegular ω) ≤ P.tail c₀ n := by
    calc
      (rawLaw9 S I).pr (fun ω => ¬ coreRegular ω) ≤
          (rawLaw9 S I).pr (fun ω => ¬ starRegular9 S E G ω v) :=
        FinProb.pr_mono (rawLaw9 S I) _ _ (by
          intro ω hnot hstar
          have hstar' := hstar b hAdj
          exact hnot hstar'.2.2)
      _ ≤ P.tail c₀ n := hRegular v
  have hsignTail : 2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) ≤
      Real.exp (-((n : ℝ) ^ P.u / 2)) := by
    have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hnleSq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [pow_two]
        calc
          (n : ℝ) = (n : ℝ) * 1 := by ring
          _ ≤ (n : ℝ) * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hnR (by linarith [hnR])
      exact hnR.trans hnleSq
    have hfactor : 2 ≤ 18 * (n : ℝ) ^ 2 := by
      have h18 : (18 : ℝ) ≤ 18 * (n : ℝ) ^ 2 := by
        calc
          (18 : ℝ) = 18 * 1 := by ring
          _ ≤ 18 * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hnSq (by norm_num : (0 : ℝ) ≤ 18)
      calc
        2 ≤ 18 := by norm_num
        _ ≤ 18 * (n : ℝ) ^ 2 := h18
    calc
      2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) ≤
          18 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) :=
            mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
      _ ≤ Real.exp (-((n : ℝ) ^ P.u / 2)) := hPolyN.1
  have hhalfTail : Real.exp (-((n : ℝ) ^ P.u / 2)) ≤
      Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) := by
    apply Real.exp_le_exp.mpr
    have hdt : d * (n : ℝ) ^ P.u ≤ (1 / 2) * (n : ℝ) ^ P.u :=
      mul_le_mul_of_nonneg_right hdleHalf hpowPos.le
    linarith
  set_option maxHeartbeats 800000 in
  have hSignedProb : (rawLaw9 S I).pr signedEvent ≤
      2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
    change (FinProb.pi (inputLaw9 S I)).pr signedEvent ≤ _
    refine pi_pr_slice_le (inputLaw9 S I) (Sum.inl target) signedEvent
      (2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) ) ?_
    intro ξ hξ
    let ωbase : Outcome9 I N := fun j =>
      if h : j = Sum.inl target then
        cast (congrArg (Val9 I N) h.symm)
          (Classical.choice (nonempty_of_probability (inputLaw9 S I (Sum.inl target))))
      else ξ ⟨j, by simpa using h⟩
    change (inputLaw9 S I (Sum.inl target)).pr
      (fun x => signedEvent (Function.update ωbase (Sum.inl target) x)) ≤ _
    have hcoreUpdate (x : Fin N) :
        coreRegular (Function.update ωbase (Sum.inl target) x) ↔ coreRegular ωbase := by
      change orderRegular9 E G (Function.update ωbase (Sum.inl target) x) ν
          (coreOrder9 I v b) ↔ orderRegular9 E G ωbase ν (coreOrder9 I v b)
      have hnot : target ∉ (coreOrder9 I v b).toFinset := by
        simpa [coreOrder9] using htargetNotCoreIDs
      exact @orderRegular_update_anchor9 P n N M I E G ωbase target x ν
        (coreOrder9 I v b) hnot
    by_cases hcore : coreRegular ωbase
    · let A : Finset (Fin N) := coreHitSet9 E G ωbase v b
      have hAupdate (x : Fin N) :
          coreHitSet9 E G (Function.update ωbase (Sum.inl target) x) v b = A := by
        dsimp [A, coreHitSet9]
        exact @hitSet_update_anchor9 P n N M I E G ωbase target x
          (coreIDs9 I v b) htargetNotCoreIDs
      have hmassLB := coreHit_mass_lower_regular9 S I E G ωbase v b hcore hbstar
      let m : ℝ := ∑ y ∈ A, ν.w y
      have hmassLB' : (49 / 100 : ℝ) ^ coreCount9 I v b ≤ m := by
        simpa [m, A] using hmassLB
      have hmPos : 0 < m := lt_of_lt_of_le (by positivity) hmassLB'
      rcases hratioByMass m hmassLB' with ⟨hdeltaMass, hratio⟩
      have hψ' (y : Fin N) : |ψ y| ≤ B := by
        simpa [B, kR, bStar] using hψ y
      obtain ⟨hQmass, lamA, rho, s, hlamEq, hsbound, hsmean, hTilt, hL1⟩ :=
        restrict_tilt_l1_9 Q ν ψ B delta hBnonneg hBsmall hψ' herr A hmPos hdeltaMass
      have hQA : restrictOr9 Q A = Q.restrict A hQmass := by
        unfold restrictOr9
        rw [dif_pos hQmass]
      have hNuA : restrictOr9 ν A = ν.restrict A hmPos := by
        unfold restrictOr9
        rw [dif_pos hmPos]
      have hLamY : lamA.SupportedIn Y := by
        rw [hlamEq]
        exact law_restrict_supported9 hNuY' hmPos
      have hmassLog := prefix_log_bound9 hmassLB'
      have hmassLog' : -Real.log m ≤ kR * L := by simpa [kR, L] using hmassLog
      have hLamWidth : lamA.WidthLE (P.Sd (n : ℝ) - Real.log 4) := by
        rw [hlamEq]
        apply Law.WidthLE.mono (Law.WidthLE.restrict hNuW' hmPos)
        have hwidth' : P.Ss (n : ℝ) - Real.log m ≤
            P.Sd (n : ℝ) - Real.log 4 := by linarith [hwidth, hmassLog']
        simpa [m] using hwidth'
      have hBpos : 0 < B := by
        have hbstarPos : 0 < bStar := by
          dsimp [bStar, Params9.bStar]
          exact Real.rpow_pos_of_pos hnPos _
        have hkRpos : 0 < kR := by linarith [hkOne]
        dsimp [B]
        exact mul_pos (mul_pos hC₁ hkRpos) hbstarPos
      let f : Fin N → ℝ := fun y => s y / (4 * B)
      have hf (y : Fin N) : |f y| ≤ 1 := by
        dsimp [f]
        rw [abs_div, abs_of_pos (by positivity : 0 < 4 * B)]
        calc
          |s y| / (4 * B) ≤ (4 * B) / (4 * B) :=
            div_le_div_of_nonneg_right (hsbound y) (by positivity)
          _ = 1 := div_self (ne_of_gt (by positivity))
      have hSignedTest := signed_test_row_tail9 hDeep G hn alpha hAlphaX' w hAlphaW' hwd
        lamA hLamY (P.Sd (n : ℝ)) hLamWidth le_rfl f hf
      let outlier : Fin N → Prop := fun x => 4 * bStar <
        |∑ y, lamA.w y * ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * f y|
      have hAlphaOutlier : alpha.pr outlier ≤
          2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
        simpa [outlier, FinProb.pr, Finset.sum_filter] using hSignedTest
      have hL1small : ∑ y, |(Q.restrict A hQmass).w y - rho.w y| ≤ bStar ^ 2 :=
        le_trans hL1 hratio
      have hscale (y : Fin N) : s y = 4 * B * f y := by
        dsimp [f]
        field_simp [ne_of_gt hBpos]
      have hAncUpdate (x : Fin N) :
          anc9 (Function.update ωbase (Sum.inl target) x) target = x := by
        simp [anc9, target, Function.update]
      have hSignedSubset (x : Fin N) :
          signedEvent (Function.update ωbase (Sum.inl target) x) → outlier x := by
        intro hevent
        have hbad := hevent.2
        have hbad' : C * kR * bStar ^ 2 <
            |rowDeg E G x (Q.restrict A hQmass) - rowDeg E G x lamA| := by
          dsimp [badReplace] at hbad
          rw [hAupdate x, hAncUpdate x, hQA, hNuA, ← hlamEq] at hbad
          simpa [target, kR, bStar] using hbad
        by_contra hout
        have hsum :
            |∑ y, lamA.w y * ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * f y| ≤
              4 * bStar := le_of_not_gt hout
        have hTiltDegree : |rowDeg E G x rho - rowDeg E G x lamA| ≤
            16 * B * bStar := by
          rw [rowDeg_centered_tilt9 E G x lamA rho s f B hTilt hsmean hscale]
          have h4Babs : |4 * B| = 4 * B :=
            abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hBnonneg)
          calc
            |4 * B * ∑ y, lamA.w y *
                ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * f y| =
                4 * B * |∑ y, lamA.w y *
                  ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * f y| := by
                    rw [abs_mul, h4Babs]
            _ ≤ 4 * B * (4 * bStar) := mul_le_mul_of_nonneg_left hsum (by positivity)
            _ = 16 * B * bStar := by ring
        have hRowComp : |rowDeg E G x (Q.restrict A hQmass) - rowDeg E G x rho| ≤ bStar ^ 2 :=
          le_trans (rowDeg_lipschitz_l1_9 E G x (Q.restrict A hQmass) rho) hL1small
        have hTotal : |rowDeg E G x (Q.restrict A hQmass) - rowDeg E G x lamA| ≤
            (16 * C₁ * kR + 1) * bStar ^ 2 := by
          calc
            |rowDeg E G x (Q.restrict A hQmass) - rowDeg E G x lamA| ≤
                |rowDeg E G x (Q.restrict A hQmass) - rowDeg E G x rho| +
                  |rowDeg E G x rho - rowDeg E G x lamA| := abs_sub_le _ _ _
            _ ≤ bStar ^ 2 + 16 * B * bStar := add_le_add hRowComp hTiltDegree
            _ = (16 * C₁ * kR + 1) * bStar ^ 2 := by dsimp [B]; ring
        have hCoeff : 16 * C₁ * kR + 1 ≤ C * kR := by
          dsimp [C]
          calc
            16 * C₁ * kR + 1 = 1 + 16 * C₁ * kR := by ring
            _ ≤ kR + 16 * C₁ * kR := add_le_add hkOne le_rfl
            _ = 16 * C₁ * kR + kR := by ring
            _ = (16 * C₁ + 1) * kR := by ring
        have hFinal : |rowDeg E G x (Q.restrict A hQmass) - rowDeg E G x lamA| ≤
            C * kR * bStar ^ 2 := by
          exact le_trans hTotal (mul_le_mul_of_nonneg_right hCoeff (sq_nonneg bStar))
        exact (not_lt_of_ge hFinal) hbad'
      have hsliceProb : (inputLaw9 S I (Sum.inl target)).pr
          (fun x => signedEvent (Function.update ωbase (Sum.inl target) x)) ≤
            2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
        calc
          (inputLaw9 S I (Sum.inl target)).pr
              (fun x => signedEvent (Function.update ωbase (Sum.inl target) x)) ≤
              (inputLaw9 S I (Sum.inl target)).pr outlier :=
                FinProb.pr_mono _ _ _ hSignedSubset
          _ = alpha.pr outlier := by rw [hInputAlpha]; rfl
          _ ≤ 2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := hAlphaOutlier
          _ ≤ 2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgap) (by norm_num)
      exact hsliceProb
    · have hfalse (x : Fin N) :
          ¬ signedEvent (Function.update ωbase (Sum.inl target) x) := by
        intro hevent
        exact hcore ((hcoreUpdate x).mp hevent.1)
      have hzero : (inputLaw9 S I (Sum.inl target)).pr
          (fun x => signedEvent (Function.update ωbase (Sum.inl target) x)) = 0 := by
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro x hx
        simp [hfalse x]
      rw [hzero]
      positivity
  have hCover : ∀ ω, badReplace ω → ¬ coreRegular ω ∨ signedEvent ω := by
    intro ω hbad
    by_cases hcore : coreRegular ω
    · exact Or.inr ⟨hcore, hbad⟩
    · exact Or.inl hcore
  have hbadProb : (rawLaw9 S I).pr badReplace ≤
      (rawLaw9 S I).pr (fun ω => ¬ coreRegular ω) +
        (rawLaw9 S I).pr signedEvent := by
    calc
      (rawLaw9 S I).pr badReplace ≤
          (rawLaw9 S I).pr (fun ω => ¬ coreRegular ω ∨ signedEvent ω) :=
        FinProb.pr_mono _ _ _ hCover
      _ ≤ (rawLaw9 S I).pr (fun ω => ¬ coreRegular ω) +
          (rawLaw9 S I).pr signedEvent := FinProb.pr_union_le _ _ _
  have hCoreTail : P.tail c₀ n ≤ Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) := by
    simp only [Params9.tail]
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hdle₀ hpowPos.le)
  have hCoreFailExp : (rawLaw9 S I).pr (fun ω => ¬ coreRegular ω) ≤
      Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) := hcoreFailure.trans hCoreTail
  have hSignedTail : (rawLaw9 S I).pr signedEvent ≤ Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) :=
    le_trans (le_trans hSignedProb hsignTail) hhalfTail
  have hUnionExponent : Real.log 2 ≤ (d / 2) * (n : ℝ) ^ P.u := by
    calc
      Real.log 2 = ((2 * Real.log 2) / d) * (d / 2) := by field_simp [ne_of_gt hd]
      _ ≤ (n : ℝ) ^ P.u * (d / 2) := mul_le_mul_of_nonneg_right hUnionN (by positivity)
      _ = (d / 2) * (n : ℝ) ^ P.u := by ring
  have hTwoTail : 2 * Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) ≤
      Real.exp (-((d / 2) * (n : ℝ) ^ P.u)) := by
    calc
      2 * Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) =
          Real.exp (Real.log 2 - (d : ℝ) * (n : ℝ) ^ P.u) := by
            calc
              _ = Real.exp (Real.log 2) * Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) := by
                rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
              _ = Real.exp (Real.log 2 + -((d : ℝ) * (n : ℝ) ^ P.u)) :=
                (Real.exp_add _ _).symm
              _ = Real.exp (Real.log 2 - (d : ℝ) * (n : ℝ) ^ P.u) := by congr 1 <;> ring
      _ ≤ Real.exp (-((d / 2) * (n : ℝ) ^ P.u)) := by
            apply Real.exp_le_exp.mpr
            have := hUnionExponent
            nlinarith
  calc
    (rawLaw9 S I).pr badReplace ≤
        (rawLaw9 S I).pr (fun ω => ¬ coreRegular ω) +
          (rawLaw9 S I).pr signedEvent := hbadProb
    _ ≤ Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) +
          Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) := add_le_add hCoreFailExp hSignedTail
    _ = 2 * Real.exp (-((d : ℝ) * (n : ℝ) ^ P.u)) := by ring
    _ ≤ Real.exp (-((d / 2) * (n : ℝ) ^ P.u)) := hTwoTail
    _ = P.tail (d / 2) n := by simp [Params9.tail]

end HypercubeRamsey.Lane_q_s09_gain1
