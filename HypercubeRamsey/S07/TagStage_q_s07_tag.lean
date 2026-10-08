import HypercubeRamsey.S07.Experiment
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open Filter
open scoped BigOperators

namespace TagStageQ

private noncomputable def indicator {Ω : Type*} (A : Ω → Prop) (ω : Ω) : ℝ :=
  if A ω then 1 else 0

theorem pi_nonempty {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hs : (∑ a, P.w a) = 0 := by simp
  rw [P.sum_eq_one] at hs
  norm_num at hs

private theorem mass_filter_eq_pr {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (A : Ω → Prop) :
    LocalLemma.mass w (Finset.univ.filter A) = ∑ ω, if A ω then w ω else 0 := by
  classical
  unfold LocalLemma.mass
  rw [Finset.sum_filter]

private theorem pi_weight_split_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ι) (ω : ∀ i, Ω i) :
    (∏ i, (P i).w (ω i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by
  classical
  let f : ι → ℝ := fun i => (P i).w (ω i)
  let t : Finset ι := Finset.univ.filter (fun i => i ∉ s)
  have hs : (∏ i : {i // i ∈ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl
  }
  have hnot : (∏ i : {i // i ∉ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∉ s, f i := by
    calc
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 :=
        Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, f i) =
        (∏ i ∈ Finset.univ with i ∈ s, f i) *
          (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) * (∏ i : {i // i ∉ s}, f i.1) := by
      rw [← hs, ← hnot]

private theorem pi_expect_split_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
            f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  rw [FinProb.expect]
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [pi_weight_split_local P s (e.symm (a, b))]
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  simp_rw [hleft, hright]
  rfl

set_option maxHeartbeats 100000000 in
private theorem pi_expect_glue_integral
    {V : Type} [Fintype V] [DecidableEq V]
    {α : V → Type} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (P : ∀ v, FinProb (α v)) (U : Finset V) (F : (∀ v, α v) → ℝ) :
    (FinProb.pi P).expect F = (FinProb.pi P).expect
      (fun ω => ∑ a : (∀ v : U, α v),
        (FinProb.pi (fun v : U => P v.1)).w a * F (glue U ω a)) := by
  classical
  let C : Finset V := Finset.univ.filter fun v => v ∉ U
  let eU := Equiv.piEquivPiSubtypeProd (fun v : V => v ∈ U) α
  let PU := FinProb.pi (fun v : U => P v.1)
  let PC := FinProb.pi (fun v : {v // v ∉ U} => P v.1)
  let ω₀ : ∀ v, α v := fun v => Classical.choice (pi_nonempty (P v))
  let a₀ : ∀ v : U, α v.1 := fun v => ω₀ v.1
  let Z : (∀ v, α v) → ℝ := fun ω =>
    ∑ a : (∀ v : U, α v.1), PU.w a * F (glue U ω a)
  have hZ : FinProb.DependsOn Z C := by
    intro ω ω' heq
    unfold Z
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    have hglue : glue U ω a = glue U ω' a := by
      funext v
      by_cases hv : v ∈ U
      · simp [glue, hv]
      · have hvC : v ∈ C := by simp [C, hv]
        simp [glue, hv, heq v hvC]
    rw [hglue]
  have hpoint (b : ∀ v : {v // v ∉ U}, α v.1) :
      Z (eU.symm (a₀, b)) =
        ∑ a : (∀ v : U, α v.1), PU.w a * F (eU.symm (a, b)) := by
    unfold Z
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    have hglue : glue U (eU.symm (a₀, b)) a = eU.symm (a, b) := by
      funext v
      by_cases hv : v ∈ U
      · simp [glue, hv, eU, Equiv.piEquivPiSubtypeProd_symm_apply]
      · simp [glue, hv, eU, Equiv.piEquivPiSubtypeProd_symm_apply]
    rw [hglue]
  have hZeq (a : ∀ v : U, α v.1) (b : ∀ v : {v // v ∉ U}, α v.1) :
      Z (eU.symm (a, b)) = Z (eU.symm (a₀, b)) := by
    apply hZ
    intro v hvC
    have hvU : v ∉ U := by simpa [C] using hvC
    simp [eU, Equiv.piEquivPiSubtypeProd_symm_apply, hvU]
  have hZsum (b : ∀ v : {v // v ∉ U}, α v.1) :
      (∑ a : (∀ v : U, α v.1), PU.w a * Z (eU.symm (a, b))) = Z (eU.symm (a₀, b)) := by
    calc
      (∑ a : (∀ v : U, α v.1), PU.w a * Z (eU.symm (a, b))) =
          ∑ a : (∀ v : U, α v.1), PU.w a * Z (eU.symm (a₀, b)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hZeq a b]
      _ = (∑ a : (∀ v : U, α v.1), PU.w a) * Z (eU.symm (a₀, b)) := by
        rw [Finset.sum_mul]
      _ = Z (eU.symm (a₀, b)) := by rw [PU.sum_eq_one, one_mul]
  rw [pi_expect_split_local P U F]
  rw [pi_expect_split_local P U Z]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑ a : (∀ v : U, α v.1),
        (FinProb.pi (fun v : U => P v.1)).w a *
          (FinProb.pi (fun v : {v // v ∉ U} => P v.1)).w b * F (eU.symm (a, b))) =
        (FinProb.pi (fun v : {v // v ∉ U} => P v.1)).w b *
          ∑ a : (∀ v : U, α v.1),
            (FinProb.pi (fun v : U => P v.1)).w a * F (eU.symm (a, b)) := by
      calc
        _ = ∑ a : (∀ v : U, α v.1),
              (FinProb.pi (fun v : {v // v ∉ U} => P v.1)).w b *
                ((FinProb.pi (fun v : U => P v.1)).w a * F (eU.symm (a, b))) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ = (FinProb.pi (fun v : {v // v ∉ U} => P v.1)).w b * Z (eU.symm (a₀, b)) := by
      rw [← hpoint b]
    _ = (FinProb.pi (fun v : {v // v ∉ U} => P v.1)).w b *
          ∑ a : (∀ v : U, α v.1),
            (FinProb.pi (fun v : U => P v.1)).w a * Z (eU.symm (a, b)) := by
      rw [← hZsum b]
    _ = ∑ a : (∀ v : U, α v.1),
          (FinProb.pi (fun v : U => P v.1)).w a *
            (FinProb.pi (fun v : {v // v ∉ U} => P v.1)).w b * Z (eU.symm (a, b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

set_option maxHeartbeats 100000000 in
theorem cond_product_bound_impl : CondProductBound := by
  classical
  intro V _ _ α _ _ P I _ _ Bad sc x Δ hL
  let Ω := ∀ v, α v
  let w : Ω → ℝ := (FinProb.pi P).w
  let E : I → Finset Ω := fun i => Finset.univ.filter (Bad i)
  let adj : I → I → Prop := fun i j => i ≠ j ∧ ¬ Disjoint (sc i) (sc j)
  let p : I → ℝ := fun i => (FinProb.pi P).pr (Bad i)
  let xx : I → ℝ := fun _ => x
  have hmassPr (A : Ω → Prop) :
      LocalLemma.mass w (Finset.univ.filter A) = (FinProb.pi P).pr A := by
    calc
      LocalLemma.mass w (Finset.univ.filter A) =
          ∑ ω, if A ω then w ω else 0 := mass_filter_eq_pr w A
      _ = (FinProb.pi P).pr A := by rfl
  have hprExp (A : Ω → Prop) :
      (FinProb.pi P).pr A = (FinProb.pi P).expect (indicator A) := by
    simp [FinProb.pr, FinProb.expect, indicator]
  have havoidMem (S : Finset I) (ω : Ω) :
      ω ∈ LocalLemma.avoid E S ↔ ∀ j ∈ S, ¬ Bad j ω := by
    simp [LocalLemma.avoid, E]
  have hAvoidMass (S : Finset I) :
      LocalLemma.mass w (LocalLemma.avoid E S) =
        (FinProb.pi P).pr (fun ω => ∀ j ∈ S, ¬ Bad j ω) := by
    have hs : LocalLemma.avoid E S =
        Finset.univ.filter (fun ω => ∀ j ∈ S, ¬ Bad j ω) := by
      ext ω
      simp [havoidMem S ω]
    rw [hs]
    unfold LocalLemma.mass FinProb.pr
    rw [Finset.sum_filter]
    simp only [w]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hA : ∀ j ∈ S, ¬ Bad j ω <;> simp [hA]
  have hJointMass (i : I) (S : Finset I) :
      LocalLemma.mass w (E i ∩ LocalLemma.avoid E S) =
        (FinProb.pi P).pr (fun ω => Bad i ω ∧ ∀ j ∈ S, ¬ Bad j ω) := by
    have hs : E i ∩ LocalLemma.avoid E S =
        Finset.univ.filter (fun ω => Bad i ω ∧ ∀ j ∈ S, ¬ Bad j ω) := by
      ext ω
      simp [E, LocalLemma.avoid]
    rw [hs]
    unfold LocalLemma.mass FinProb.pr
    rw [Finset.sum_filter]
    simp only [w]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hA : Bad i ω ∧ ∀ j ∈ S, ¬ Bad j ω <;> simp [hA]
  have hEProb (i : I) : LocalLemma.mass w (E i) = p i := by
    change LocalLemma.mass w (Finset.univ.filter (Bad i)) = _
    rw [hmassPr]
  have hsymm : ∀ i j, adj i j → adj j i := by
    intro i j hij
    refine ⟨hij.1.symm, ?_⟩
    intro hji
    apply hij.2
    apply Finset.disjoint_left.mpr
    intro a haI haJ
    exact Finset.disjoint_left.mp hji haJ haI
  have hirr : ∀ i, ¬ adj i i := by
    intro i hi
    exact hi.1 rfl
  have hcond : ∀ i (S : Finset I), i ∉ S → (∀ j ∈ S, ¬ adj i j) →
      LocalLemma.mass w (E i ∩ LocalLemma.avoid E S) ≤
        p i * LocalLemma.mass w (LocalLemma.avoid E S) := by
    intro i S hiS hsep
    let U : Finset V := S.biUnion sc
    have hdepBad : FinProb.DependsOn (indicator (Bad i)) (sc i) := by
      intro ω ω' heq
      unfold indicator
      rw [hL.scope i ω ω' heq]
    have hdepAvoid : FinProb.DependsOn
        (indicator (fun ω => ∀ j ∈ S, ¬ Bad j ω)) U := by
      intro ω ω' heq
      unfold indicator
      congr 1
      apply propext
      constructor
      · intro h j hj
        have heqj : Bad j ω = Bad j ω' := by
          apply hL.scope j ω ω'
          intro v hv
          exact heq v (Finset.mem_biUnion.mpr ⟨j, hj, hv⟩)
        rw [← heqj]
        exact h j hj
      · intro h j hj
        have heqj : Bad j ω = Bad j ω' := by
          apply hL.scope j ω ω'
          intro v hv
          exact heq v (Finset.mem_biUnion.mpr ⟨j, hj, hv⟩)
        rw [heqj]
        exact h j hj
    have hdis : Disjoint (sc i) U := by
      apply Finset.disjoint_left.mpr
      intro v hvI hvU
      obtain ⟨j, hjS, hvJ⟩ := Finset.mem_biUnion.mp hvU
      have hij : i ≠ j := by
        intro h
        subst j
        exact hiS hjS
      have hdisij : Disjoint (sc i) (sc j) := by
        by_contra hnotdis
        exact hsep j hjS ⟨hij, hnotdis⟩
      exact Finset.disjoint_left.mp hdisij hvI hvJ
    have hind := FinProb.pi_expect_mul_of_disjoint P
      (indicator (Bad i)) (indicator (fun ω => ∀ j ∈ S, ¬ Bad j ω))
      (sc i) U hdepBad hdepAvoid hdis
    have hjointExp : LocalLemma.mass w (E i ∩ LocalLemma.avoid E S) =
        (FinProb.pi P).expect
          (fun ω => indicator (Bad i) ω * indicator (fun z => ∀ j ∈ S, ¬ Bad j z) ω) := by
      rw [hJointMass, hprExp]
      congr 1
      funext ω
      by_cases hi : Bad i ω <;>
        by_cases hs : ∀ j ∈ S, ¬ Bad j ω <;> simp [indicator, hi, hs]
    have hEq : LocalLemma.mass w (E i ∩ LocalLemma.avoid E S) =
        p i * LocalLemma.mass w (LocalLemma.avoid E S) := by
      calc
        LocalLemma.mass w (E i ∩ LocalLemma.avoid E S) =
            (FinProb.pi P).expect
              (fun ω => indicator (Bad i) ω * indicator (fun z => ∀ j ∈ S, ¬ Bad j z) ω) :=
          hjointExp
        _ = (FinProb.pi P).pr (Bad i) *
              (FinProb.pi P).pr (fun ω => ∀ j ∈ S, ¬ Bad j ω) := by
          rw [hind, ← hprExp, ← hprExp]
        _ = p i * LocalLemma.mass w (LocalLemma.avoid E S) := by
          rw [← hAvoidMass S, ← hEProb i, hmassPr (Bad i)]
    exact hEq.le
  have hpx : ∀ i, p i ≤ xx i * ∏ j ∈ Finset.univ.filter (adj i), (1 - xx j) := by
    intro i
    let T : Finset I := Finset.univ.filter (adj i)
    have hT : T = Finset.univ.filter
        (fun j => j ≠ i ∧ ¬ Disjoint (sc i) (sc j)) := by
      ext j
      simp [T, adj, ne_comm]
    have hdeg : T.card ≤ Δ := by
      simpa [hT] using hL.degree i
    have hpow : (1 - x) ^ Δ ≤ (1 - x) ^ T.card :=
      pow_le_pow_of_le_one (sub_nonneg.mpr hL.x_lt_one.le)
        (sub_le_self 1 hL.x_nonneg) hdeg
    have hprod : ∏ j ∈ T, (1 - xx j) = (1 - x) ^ T.card := by
      simp [xx]
    calc
      p i ≤ x * (1 - x) ^ Δ := by simpa [p, xx] using hL.prob i
      _ ≤ x * (1 - x) ^ T.card := mul_le_mul_of_nonneg_left hpow hL.x_nonneg
      _ = xx i * ∏ j ∈ Finset.univ.filter (adj i), (1 - xx j) := by
        rw [← hprod]
  have hx0 : ∀ i, 0 ≤ xx i := by intro _; exact hL.x_nonneg
  have hx1 : ∀ i, xx i < 1 := by intro _; exact hL.x_lt_one
  have hca := LocalLemma.conditional_avoidance w
    (by intro ω; exact (FinProb.pi P).nonneg ω)
    (by exact (FinProb.pi P).sum_eq_one)
    E adj hsymm hirr p xx hcond hx0 hx1 hpx
  have hAllSet : LocalLemma.avoid E Finset.univ =
      Finset.univ.filter (fun ω => ∀ i, ¬ Bad i ω) := by
    ext ω
    simp [LocalLemma.avoid, E]
  have hAllPos : 0 < (FinProb.pi P).pr (fun ω => ∀ i, ¬ Bad i ω) := by
    have hmassAll : LocalLemma.mass w (LocalLemma.avoid E Finset.univ) =
        (FinProb.pi P).pr (fun ω => ∀ i, ¬ Bad i ω) := by
      simpa using hAvoidMass Finset.univ
    rw [← hmassAll]
    exact hca.1
  refine ⟨hAllPos, ?_⟩
  intro U Φ hΦ B hB
  let T : Finset I := Finset.univ.filter fun i => ¬ Disjoint (sc i) U
  let S : Finset I := Finset.univ.filter fun i => Disjoint (sc i) U
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiT
    exact (Finset.mem_filter.mp hiT).2 (Finset.mem_filter.mp hiS).2
  have hcover : S ∪ T = Finset.univ := by
    ext i
    by_cases h : Disjoint (sc i) U <;> simp [S, T, h]
  have hAvoidST : LocalLemma.avoid E (S ∪ T) = LocalLemma.avoid E Finset.univ := by
    rw [hcover]
  have hdenS : 0 < LocalLemma.mass w (LocalLemma.avoid E S) := by
    have hsub : LocalLemma.avoid E Finset.univ ⊆ LocalLemma.avoid E S := by
      intro ω hω
      rw [havoidMem Finset.univ ω] at hω
      rw [havoidMem S ω]
      intro i hiS
      exact hω i (Finset.mem_univ i)
    have hmono : LocalLemma.mass w (LocalLemma.avoid E Finset.univ) ≤
        LocalLemma.mass w (LocalLemma.avoid E S) := by
      unfold LocalLemma.mass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => (FinProb.pi P).nonneg ω)
    exact lt_of_lt_of_le hca.1 hmono
  have hAvoidGlue : ∀ ω (a : ∀ v : U, α v.1),
      (∀ i ∈ S, ¬ Bad i (glue U ω a)) ↔ ∀ i ∈ S, ¬ Bad i ω := by
    intro ω a
    constructor
    · intro h i hi
      have hEq : Bad i (glue U ω a) = Bad i ω := by
        apply hL.scope i (glue U ω a) ω
        intro v hv
        have hdis := (Finset.mem_filter.mp hi).2
        have hvnot : v ∉ U := by
          intro hvU
          exact (Finset.disjoint_left.mp hdis hv hvU)
        simp [glue, hvnot]
      rw [← hEq]
      exact h i hi
    · intro h i hi
      have hEq : Bad i (glue U ω a) = Bad i ω := by
        apply hL.scope i (glue U ω a) ω
        intro v hv
        have hdis := (Finset.mem_filter.mp hi).2
        have hvnot : v ∉ U := by
          intro hvU
          exact (Finset.disjoint_left.mp hdis hv hvU)
        simp [glue, hvnot]
      rw [hEq]
      exact h i hi
  let F₀ : Ω → ℝ := fun ω => if (∀ i ∈ S, ¬ Bad i ω) then Φ ω else 0
  have hinner : ∀ ω,
      (∑ a : (∀ v : U, α v.1),
        (FinProb.pi (fun v : U => P v.1)).w a * F₀ (glue U ω a)) ≤
          if (∀ i ∈ S, ¬ Bad i ω) then B else 0 := by
    intro ω
    by_cases hω : ∀ i ∈ S, ¬ Bad i ω
    · have htrue : ∀ a : (∀ v : U, α v.1), ∀ i ∈ S, ¬ Bad i (glue U ω a) := by
        intro a i hi
        exact (hAvoidGlue ω a).2 hω i hi
      have hsum :
          (∑ a : (∀ v : U, α v.1),
            (FinProb.pi (fun v : U => P v.1)).w a * F₀ (glue U ω a)) =
            ∑ a : (∀ v : U, α v.1),
              (FinProb.pi (fun v : U => P v.1)).w a * Φ (glue U ω a) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hA : (∀ i ∈ S, ¬ Bad i (glue U ω a)) := htrue a
        simp only [F₀, if_pos hA]
      rw [hsum]
      have hB' :
          (∑ a : (∀ v : U, α v.1),
            (FinProb.pi (fun v : U => P v.1)).w a * Φ (glue U ω a)) ≤ B := by
        simpa [FinProb.pi] using hB ω
      simpa only [if_pos hω] using hB'
    · have hfalse : ∀ a : (∀ v : U, α v.1), ¬ (∀ i ∈ S, ¬ Bad i (glue U ω a)) := by
        intro a ha
        exact hω ((hAvoidGlue ω a).1 ha)
      simp [F₀, hω, hfalse, FinProb.pi]
  have hraw :
      (∑ ω ∈ LocalLemma.avoid E S, w ω * Φ ω) ≤ B * LocalLemma.mass w (LocalLemma.avoid E S) := by
    have hglue := pi_expect_glue_integral P U F₀
    have hmono := (FinProb.pi P).expect_mono hinner
    have hconst : (FinProb.pi P).expect
          (fun ω => if (∀ i ∈ S, ¬ Bad i ω) then B else 0) =
        B * (FinProb.pi P).pr (fun ω => ∀ i ∈ S, ¬ Bad i ω) := by
      unfold FinProb.expect FinProb.pr
      calc
        (∑ ω, (FinProb.pi P).w ω * (if (∀ i ∈ S, ¬ Bad i ω) then B else 0)) =
            ∑ ω, B * (if (∀ i ∈ S, ¬ Bad i ω) then (FinProb.pi P).w ω else 0) := by
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases h : ∀ i ∈ S, ¬ Bad i ω <;> simp [h, mul_comm]
        _ = B * ∑ ω, if (∀ i ∈ S, ¬ Bad i ω) then (FinProb.pi P).w ω else 0 := by
          rw [Finset.mul_sum]
        _ = _ := by
          apply congrArg (fun z : ℝ => B * z)
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases h : ∀ i ∈ S, ¬ Bad i ω <;> simp [h]
    have hnum : (FinProb.pi P).expect F₀ =
        ∑ ω ∈ LocalLemma.avoid E S, w ω * Φ ω := by
      have hset : LocalLemma.avoid E S =
          Finset.univ.filter (fun ω => ∀ i ∈ S, ¬ Bad i ω) := by
        ext ω
        simpa using havoidMem S ω
      unfold FinProb.expect F₀
      rw [hset, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hA : ∀ i ∈ S, ¬ Bad i ω <;> simp [w, hA]
    rw [← hglue] at hmono
    rw [hnum] at hmono
    rw [hconst, ← hAvoidMass S] at hmono
    exact hmono
  have hnumNonneg : 0 ≤ ∑ ω ∈ LocalLemma.avoid E S, w ω * Φ ω := by
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg ((FinProb.pi P).nonneg ω) (hΦ ω)
  have hBnonneg : 0 ≤ B := by
    by_contra hnB
    have hBneg : B < 0 := lt_of_not_ge hnB
    have hmasspos := hdenS
    have hneg : B * LocalLemma.mass w (LocalLemma.avoid E S) < 0 :=
      mul_neg_of_neg_of_pos hBneg hmasspos
    linarith
  have hrawRatio :
      (∑ ω ∈ LocalLemma.avoid E S, w ω * Φ ω) /
          LocalLemma.mass w (LocalLemma.avoid E S) ≤ B := by
    apply (div_le_iff₀ hdenS).2
    simpa [mul_comm] using hraw
  have hfactorPos : 0 < ∏ j ∈ T, (1 - xx j) := by
    apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hL.x_lt_one)
  have hcmp := hca.2.2.1 S T hST Φ hΦ
  have hcond :
      (condOr (FinProb.pi P) (fun ω => ∀ i, ¬ Bad i ω)).expect Φ =
        (∑ ω ∈ LocalLemma.avoid E Finset.univ, w ω * Φ ω) /
      LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := by
    let A : Ω → Prop := fun ω => ∀ i, ¬ Bad i ω
    letI : DecidablePred A := fun ω => Classical.propDecidable (A ω)
    have hden : (FinProb.pi P).pr (fun ω => ∀ i, ¬ Bad i ω) =
        LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := by
      simpa using (hAvoidMass Finset.univ).symm
    have hco : condOr (FinProb.pi P) (fun ω => ∀ i, ¬ Bad i ω) =
        (FinProb.pi P).cond (fun ω => ∀ i, ¬ Bad i ω) hAllPos := by
      simp [condOr, hAllPos]
    have hnumA : (∑ ω, if A ω then (FinProb.pi P).w ω * Φ ω else 0) =
        ∑ ω ∈ LocalLemma.avoid E Finset.univ, w ω * Φ ω := by
      calc
        (∑ ω, if A ω then (FinProb.pi P).w ω * Φ ω else 0) =
            ∑ ω ∈ Finset.univ.filter A, (FinProb.pi P).w ω * Φ ω := by
          symm
          rw [Finset.sum_filter]
        _ = ∑ ω ∈ LocalLemma.avoid E Finset.univ, w ω * Φ ω := by
          have hset : Finset.univ.filter A = LocalLemma.avoid E Finset.univ := by
            ext ω
            simp [A, LocalLemma.avoid, E]
          rw [hset]
    rw [hco]
    calc
      ((FinProb.pi P).cond (fun ω => ∀ i, ¬ Bad i ω) hAllPos).expect Φ =
          (∑ ω, if A ω then (FinProb.pi P).w ω * Φ ω else 0) /
            (FinProb.pi P).pr A := by
        unfold FinProb.expect
        dsimp [FinProb.cond]
        change (∑ ω, ((if A ω then (FinProb.pi P).w ω else 0) /
            (FinProb.pi P).pr A) * Φ ω) = _
        calc
          (∑ ω, ((if A ω then (FinProb.pi P).w ω else 0) /
              (FinProb.pi P).pr A) * Φ ω) =
              ∑ ω, (if A ω then (FinProb.pi P).w ω * Φ ω else 0) /
                (FinProb.pi P).pr A := by
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hA : A ω <;> simp [A, hA]
            · ring
          _ = (∑ ω, if A ω then (FinProb.pi P).w ω * Φ ω else 0) /
                (FinProb.pi P).pr A := by
            rw [← Finset.sum_div]
      _ = (∑ ω ∈ LocalLemma.avoid E Finset.univ, w ω * Φ ω) /
            LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := by
        rw [hnumA, hden]
  have hAvoidSTmass : LocalLemma.mass w (LocalLemma.avoid E (S ∪ T)) =
      LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := by rw [hAvoidST]
  have hTcount : T.card =
      (Finset.univ.filter fun i => ¬ Disjoint (sc i) U).card := by rfl
  calc
    (condOr (FinProb.pi P) (fun ω => ∀ i, ¬ Bad i ω)).expect Φ =
        (∑ ω ∈ LocalLemma.avoid E Finset.univ, w ω * Φ ω) /
          LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := hcond
    _ ≤ (∏ j ∈ T, (1 - xx j))⁻¹ *
        ((∑ ω ∈ LocalLemma.avoid E S, w ω * Φ ω) /
          LocalLemma.mass w (LocalLemma.avoid E S)) := by
      calc
      _ = (∑ ω ∈ LocalLemma.avoid E (S ∪ T), w ω * Φ ω) /
              LocalLemma.mass w (LocalLemma.avoid E (S ∪ T)) := by
          rw [← hAvoidST]
        _ ≤ _ := hcmp
    _ ≤ (∏ j ∈ T, (1 - xx j))⁻¹ * B :=
      mul_le_mul_of_nonneg_left hrawRatio (le_of_lt (inv_pos.mpr hfactorPos))
    _ = ((1 - x) ^ (Finset.univ.filter fun i => ¬ Disjoint (sc i) U).card)⁻¹ * B := by
      simp [T, xx, Finset.prod_const, hTcount]

private theorem crossValidRow_depends
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (i : M.ι) (g : Γ.Key) :
    FinProb.DependsOn (fun a : Γ.Key → Fin N => CrossValidRow Γ M i a g)
      (Γ.keyBall g 1) := by
  classical
  intro a a' hagree
  have hmap (h₀ : Γ.Key) (hh₀ : h₀ ∈ Γ.crossKeys g) :
      (Γ.crossOrder g h₀).map a = (Γ.crossOrder g h₀).map a' := by
    apply List.map_congr_left
    intro h hh
    have hmem : h ∈ Γ.crossKeys g := by
      rcases (by simpa [GridGeom.crossOrder] using hh) with he | he
      · exact List.mem_of_mem_erase he
      · subst h
        exact hh₀
    have hNbr : h ∈ Γ.keyNbrs g := by
      simpa [GridGeom.crossKeys] using hmem
    have hdist : Γ.keyDist g h = 1 := (Finset.mem_filter.mp hNbr).2
    have hball : h ∈ Γ.keyBall g 1 := by
      simp only [GridGeom.keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    exact hagree h hball
  apply propext
  constructor
  · intro h h₀ hh₀ k hk
    have hstep := h h₀ hh₀ k hk
    rw [hmap h₀ hh₀] at hstep
    exact hstep
  · intro h h₀ hh₀ k hk
    have hstep := h h₀ hh₀ k hk
    rw [← hmap h₀ hh₀] at hstep
    exact hstep

private theorem pr_eq_expect_indicator {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = P.expect (indicator A) := by
  classical
  simp [FinProb.pr, FinProb.expect, indicator]

noncomputable def tagAnchorLaw
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) : Γ.Key → FinProb (M.ι × Fin N) :=
  fun g => FinProb.bind (Q g) (fun i => M.μ i)

private theorem pi_pr_bound_of_glue
    {V : Type} [Fintype V] [DecidableEq V]
    {α : V → Type} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (P : ∀ v, FinProb (α v)) (U : Finset V) (A : (∀ v, α v) → Prop) (b : ℝ)
    (hslice : ∀ ω : ∀ v, α v,
      (∑ a : (∀ v : U, α v.1),
        (FinProb.pi (fun v : U => P v.1)).w a *
          indicator A (glue U ω a)) ≤ b) :
    (FinProb.pi P).pr A ≤ b := by
  classical
  rw [pr_eq_expect_indicator, pi_expect_glue_integral]
  calc
    (FinProb.pi P).expect
        (fun ω => ∑ a : (∀ v : U, α v.1),
          (FinProb.pi (fun v : U => P v.1)).w a * indicator A (glue U ω a)) ≤
      (FinProb.pi P).expect (fun _ => b) :=
        FinProb.expect_mono _ fun ω => hslice ω
    _ = b := FinProb.expect_const _ _

private theorem pi_singleton_expect
    {V α : Type} [Fintype V] [DecidableEq V] [Fintype α]
    (P : V → FinProb α) (j : V) (f : α → ℝ) :
    (FinProb.pi (fun v : {i // i ∈ ({j} : Finset V)} => P v.1)).expect
        (fun a => f (a ⟨j, by simp⟩)) = (P j).expect f := by
  classical
  let U : Type := {i // i ∈ ({j} : Finset V)}
  let center : U := ⟨j, by simp⟩
  letI : Unique U := {
    toInhabited := ⟨center⟩
    uniq := fun v => by
      apply Subtype.ext
      exact Finset.mem_singleton.mp v.2 }
  let e : (U → α) ≃ α :=
    { toFun := fun a => a center
      invFun := fun x _ => x
      left_inv := by
        intro a
        funext v
        have hv : v = center := Subsingleton.elim _ _
        rw [hv]
      right_inv := by intro x; rfl }
  have hw (a : U → α) :
      (∏ v : U, (P v.1).w (a v)) = (P j).w (a center) := by
    have hdefault : (default : U) = center := Subsingleton.elim _ _
    simpa [U, center, hdefault]
  rw [FinProb.expect]
  calc
    (∑ a : U → α, (FinProb.pi (fun v : U => P v.1)).w a * f (a center)) =
        ∑ a : U → α, (P j).w (a center) * f (a center) := by
      change (∑ a : U → α, (∏ v : U, (P v.1).w (a v)) * f (a center)) = _
      apply Finset.sum_congr rfl
      intro a ha
      rw [hw]
    _ = ∑ x : α, (P j).w x * f x :=
      Equiv.sum_comp e (fun x : α => (P j).w x * f x)
    _ = (P j).expect f := rfl

private theorem pi_pr_bound_of_glue_singleton
    {V α : Type} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]
    (P : V → FinProb α) (j : V) (A : (V → α) → Prop) (b : ℝ)
    (hslice : ∀ ω : V → α,
      (P j).pr (fun x => A (glue ({j} : Finset V) ω (fun _ => x))) ≤ b) :
    (FinProb.pi P).pr A ≤ b := by
  classical
  apply pi_pr_bound_of_glue P ({j} : Finset V) A b
  intro ω
  let U : Type := {i // i ∈ ({j} : Finset V)}
  let center : U := ⟨j, by simp⟩
  let f : α → ℝ := fun x => indicator A (glue ({j} : Finset V) ω (fun _ : U => x))
  have hglue (a : U → α) :
      glue ({j} : Finset V) ω a =
        glue ({j} : Finset V) ω (fun _ : U => a center) := by
    funext v
    by_cases hv : v ∈ ({j} : Finset V)
    · have hsub : (⟨v, hv⟩ : U) = center := by
        apply Subtype.ext
        exact Finset.mem_singleton.mp hv
      simp [glue, hv, hsub]
    · simp [glue, hv]
  have hpoint (a : U → α) :
      indicator A (glue ({j} : Finset V) ω a) = f (a center) := by
    rw [hglue a]
  have hsliceEq :
      (∑ a : (∀ v : U, α),
        (FinProb.pi (fun v : U => P v.1)).w a *
          indicator A (glue ({j} : Finset V) ω a)) =
        (P j).pr (fun x => A (glue ({j} : Finset V) ω (fun _ : U => x))) := by
    calc
      (∑ a : (∀ v : U, α),
          (FinProb.pi (fun v : U => P v.1)).w a *
            indicator A (glue ({j} : Finset V) ω a)) =
          (FinProb.pi (fun v : U => P v.1)).expect (fun a => f (a center)) := by
        rw [FinProb.expect]
        apply Finset.sum_congr rfl
        intro a ha
        rw [hpoint]
      _ = (P j).expect f := pi_singleton_expect P j f
      _ = (P j).pr (fun x => A (glue ({j} : Finset V) ω (fun _ : U => x))) := by
        symm
        exact pr_eq_expect_indicator (P j)
          (fun x => A (glue ({j} : Finset V) ω (fun _ : U => x)) )
  rw [hsliceEq]
  exact hslice ω

private theorem tagAnchor_pr_snd
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) (g : Γ.Key) (A : Fin N → Prop) :
    (tagAnchorLaw Γ M Q g).pr (fun z => A z.2) =
      (Law.mix (Q g) M.μ).pr A := by
  classical
  simp only [FinProb.pr, tagAnchorLaw, FinProb.bind, Law.mix]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hA : A x <;> simp [hA]

private theorem filterMass_nil {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) : filterMass E G ν [] = 1 := by
  simp [filterMass, passesAnchors, ν.sum_eq_one]

private theorem cross_prefix_mass_lower
    {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (ν : Law N)
    (n : ℕ) (d : ℝ) (L : List (Fin N)) (k : ℕ)
    (hgood : ∀ j < k,
      (n : ℝ) ^ (-(d / 80)) * filterMass E G ν (L.take j) ≤
        filterMass E G ν (L.take (j + 1))) :
    ((n : ℝ) ^ (-(d / 80))) ^ k ≤ filterMass E G ν (L.take k) := by
  have hθ : 0 ≤ (n : ℝ) ^ (-(d / 80)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  induction k with
  | zero =>
      simp [filterMass_nil]
  | succ k ih =>
      have hprev : ∀ j < k,
          (n : ℝ) ^ (-(d / 80)) * filterMass E G ν (L.take j) ≤
            filterMass E G ν (L.take (j + 1)) := by
        intro j hj
        exact hgood j (by omega)
      have hmass := ih hprev
      have hstep := hgood k (by omega)
      calc
        ((n : ℝ) ^ (-(d / 80))) ^ (k + 1) =
            (n : ℝ) ^ (-(d / 80)) * ((n : ℝ) ^ (-(d / 80))) ^ k := by
          rw [pow_succ]
          ring
        _ ≤ (n : ℝ) ^ (-(d / 80)) * filterMass E G ν (L.take k) :=
          mul_le_mul_of_nonneg_left hmass hθ
        _ ≤ filterMass E G ν (L.take (k + 1)) := hstep

private theorem filterMass_append_single
    {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (ν : Law N)
    (L : List (Fin N)) (x : Fin N) :
    filterMass E G ν (L ++ [x]) =
      ∑ y, if passesAnchors E G L y ∧ Hits E G x y then ν.w y else 0 := by
  classical
  have hp (y : Fin N) :
      passesAnchors E G (L ++ [x]) y ↔
        passesAnchors E G L y ∧ Hits E G x y := by
    unfold passesAnchors
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro a ha
        exact h a (List.mem_append.mpr (Or.inl ha))
      · exact h x (List.mem_append.mpr (Or.inr (by simp)))
    · rintro ⟨hL, hx⟩ a ha
      rcases List.mem_append.mp ha with haL | haX
      · exact hL a haL
      · have : a = x := List.mem_singleton.mp haX
        subst a
        exact hx
  unfold filterMass
  simp_rw [hp]

private theorem rowDeg_filtLaw_append
    {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (ν : Law N)
    (L : List (Fin N)) (x : Fin N) (hpos : 0 < filterMass E G ν L) :
    rowDeg E G x (filtLaw E G ν L) =
      filterMass E G ν (L ++ [x]) / filterMass E G ν L := by
  classical
  have hterm (y : Fin N) :
      (filtLaw E G ν L).w y * (if Hits E G x y then 1 else 0) =
        (if passesAnchors E G L y ∧ Hits E G x y then ν.w y else 0) /
          filterMass E G ν L := by
    by_cases hp : passesAnchors E G L y <;> by_cases hxy : Hits E G x y <;>
      simp [filtLaw, filt, hpos, hp, hxy]
  unfold rowDeg
  calc
    (∑ y, (filtLaw E G ν L).w y * (if Hits E G x y then 1 else 0)) =
        ∑ y, (if passesAnchors E G L y ∧ Hits E G x y then ν.w y else 0) /
          filterMass E G ν L := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hterm y
    _ = (∑ y, if passesAnchors E G L y ∧ Hits E G x y then ν.w y else 0) /
          filterMass E G ν L := by rw [← Finset.sum_div]
    _ = filterMass E G ν (L ++ [x]) / filterMass E G ν L := by
      rw [filterMass_append_single]

private theorem filtLaw_width_of_cross_prefix
    {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (ν : Law N)
    (n : ℕ) (d : ℝ) (hd : 0 ≤ d) (L : List (Fin N)) (k : ℕ)
    (hN : 0 < N) (hn : 2 ≤ n)
    (hraw : ν.WidthLE ((n : ℝ) ^ (d / 2)))
    (hgood : ∀ j < k,
      (n : ℝ) ^ (-(d / 80)) * filterMass E G ν (L.take j) ≤
        filterMass E G ν (L.take (j + 1)))
    (hk : k ≤ 2 * gS d n)
    (hbudget : (n : ℝ) ^ (d / 2) +
      2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) ≤
        (n : ℝ) ^ ((1 : ℝ) / 4)) :
    (filtLaw E G ν (L.take k)).WidthLE ((n : ℝ) ^ ((1 : ℝ) / 4)) := by
  classical
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmassTheta := cross_prefix_mass_lower E G ν n d L k hgood
  have hthetaPos : 0 < (n : ℝ) ^ (-(d / 80)) := Real.rpow_pos_of_pos hnRpos _
  have hmassPos : 0 < filterMass E G ν (L.take k) :=
    lt_of_lt_of_le (pow_pos hthetaPos k) hmassTheta
  have hthetaPow : ((n : ℝ) ^ (-(d / 80))) ^ k =
      (n : ℝ) ^ ((-(d / 80)) * (k : ℝ)) :=
    (Real.rpow_mul_natCast hnRpos.le (-(d / 80)) k).symm
  have hmassLower :
      (n : ℝ) ^ ((-(d / 80)) * (k : ℝ)) ≤ filterMass E G ν (L.take k) := by
    rw [← hthetaPow]
    exact hmassTheta
  have hpowPos : 0 < (n : ℝ) ^ ((-(d / 80)) * (k : ℝ)) :=
    Real.rpow_pos_of_pos hnRpos _
  have hInvMass : (filterMass E G ν (L.take k))⁻¹ ≤
      (n : ℝ) ^ ((d / 80) * (k : ℝ)) := by
    have hInv := (inv_le_inv₀ hmassPos hpowPos).2 hmassLower
    have hpowNeg : (n : ℝ) ^ ((-(d / 80)) * (k : ℝ)) =
        ((n : ℝ) ^ ((d / 80) * (k : ℝ)))⁻¹ := by
      have hexp : (-(d / 80)) * (k : ℝ) = -((d / 80) * (k : ℝ)) := by ring
      rw [hexp, Real.rpow_neg hnRpos.le]
    rw [hpowNeg, inv_inv] at hInv
    exact hInv
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hcoefNonneg : 0 ≤ d / 80 := div_nonneg hd (by norm_num)
  have hkReal : (k : ℝ) ≤ 2 * (gS d n : ℝ) := by exact_mod_cast hk
  have hpowExp : (d / 80) * (k : ℝ) * Real.log (n : ℝ) ≤
      2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) := by
    have hcoeff := mul_le_mul_of_nonneg_left hkReal hcoefNonneg
    calc
      (d / 80) * (k : ℝ) * Real.log (n : ℝ) =
          ((d / 80) * (k : ℝ)) * Real.log (n : ℝ) := by ring
      _ ≤ ((d / 80) * (2 * (gS d n : ℝ))) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff hlogNonneg
      _ = 2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) := by ring
  have hExp : (n : ℝ) ^ (d / 2) + (d / 80) * (k : ℝ) * Real.log (n : ℝ) ≤
      (n : ℝ) ^ ((1 : ℝ) / 4) := by nlinarith [hbudget, hpowExp]
  have hrpow : (n : ℝ) ^ ((d / 80) * (k : ℝ)) =
      Real.exp (Real.log (n : ℝ) * ((d / 80) * (k : ℝ))) :=
    Real.rpow_def_of_pos hnRpos _
  have hExp' : (n : ℝ) ^ (d / 2) + (d / 80) * (k : ℝ) * Real.log (n : ℝ) ≤
      (n : ℝ) ^ (4⁻¹ : ℝ) := by simpa [one_div] using hExp
  intro y
  by_cases hp : passesAnchors E G (L.take k) y
  · simp [filtLaw, hmassPos, filt, hp]
    calc
      ν.w y / filterMass E G ν (L.take k) =
          ν.w y * (filterMass E G ν (L.take k))⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ (Real.exp ((n : ℝ) ^ (d / 2)) / N) *
            (filterMass E G ν (L.take k))⁻¹ :=
        mul_le_mul_of_nonneg_right (hraw y) (inv_nonneg.mpr hmassPos.le)
      _ ≤ (Real.exp ((n : ℝ) ^ (d / 2)) / N) *
            (n : ℝ) ^ ((d / 80) * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hInvMass (by positivity)
      _ = (Real.exp ((n : ℝ) ^ (d / 2)) *
            Real.exp (Real.log (n : ℝ) * ((d / 80) * (k : ℝ)))) / N := by
        rw [hrpow]
        ring
      _ = Real.exp ((n : ℝ) ^ (d / 2) +
            (d / 80) * (k : ℝ) * Real.log (n : ℝ)) / N := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((n : ℝ) ^ (4⁻¹ : ℝ)) / N :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hExp') hNreal.le
  · simp [filtLaw, hmassPos, filt, hp]
    positivity

theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  exact Finset.sum_nonneg fun ω _ => by
    by_cases hA : A ω <;> simp [hA, P.nonneg ω]

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

theorem pr_exists_le_sum
    {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (P : FinProb Ω) (S : Finset I) (A : I → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ S, A i ω) ≤ ∑ i ∈ S, P.pr (A i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert i S hi ih =>
      have hEq : (fun ω => ∃ j ∈ insert i S, A j ω) =
          (fun ω => A i ω ∨ ∃ j ∈ S, A j ω) := by
        funext ω
        apply propext
        simp [Finset.mem_insert, hi]
      rw [hEq]
      calc
        P.pr (fun ω => A i ω ∨ ∃ j ∈ S, A j ω) ≤
            P.pr (A i) + P.pr (fun ω => ∃ j ∈ S, A j ω) :=
          FinProb.pr_union P (A i) (fun ω => ∃ j ∈ S, A j ω)
        _ ≤ P.pr (A i) + ∑ j ∈ S, P.pr (A j) := add_le_add_right ih _
        _ = ∑ j ∈ insert i S, P.pr (A j) := by rw [Finset.sum_insert hi]

theorem pi_expect_prod
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → FinProb α) (f : ι → α → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).expect (f i) := by
  classical
  rw [FinProb.expect]
  change (∑ ω : (ι → α), (∏ i, (P i).w (ω i)) * ∏ i, f i (ω i)) = _
  calc
    (∑ ω : (ι → α), (∏ i, (P i).w (ω i)) * ∏ i, f i (ω i)) =
        ∑ ω : (ι → α), ∏ i, ((P i).w (ω i) * f i (ω i)) := by
      apply Finset.sum_congr rfl
      intro ω hω
      exact (Finset.prod_mul_distrib).symm
    _ = ∏ i : ι, ∑ a : α, (P i).w a * f i a := by
      rw [Fintype.prod_sum]
    _ = ∏ i : ι, (P i).expect (f i) := by simp [FinProb.expect]

theorem pi_expect_prod_restrict
    {I V α : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Fintype α]
    (k : I → V) (hk : Function.Injective k) (Q : V → FinProb α) (f : I → α → ℝ) :
    (FinProb.pi (fun v : Finset.univ.image k => Q v.1)).expect
      (fun a => ∏ i, f i (a ⟨k i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)) =
        ∏ i, (Q (k i)).expect (f i) := by
  classical
  let S : Finset V := Finset.univ.image k
  let coord : I → S := fun i => ⟨k i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hbij : Function.Bijective coord := by
    constructor
    · intro i j hij
      apply hk
      exact congrArg Subtype.val hij
    · intro v
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp v.2
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact heq
  let e : I ≃ S := Equiv.ofBijective coord hbij
  let ePi : (∀ v : S, α) ≃ (I → α) :=
    (Equiv.piCongrLeft (fun _ : S => α) e).symm
  have hPiValue (b : I → α) (v : S) : ePi.symm b v = b (e.symm v) := by
    simp [ePi, Equiv.piCongrLeft_apply]
  have hweight (b : I → α) :
      ∏ v : S, (Q v.1).w (ePi.symm b v) = ∏ i, (Q (k i)).w (b i) := by
    calc
      ∏ v : S, (Q v.1).w (ePi.symm b v) =
          ∏ v : S, (Q v.1).w (b (e.symm v)) := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [hPiValue]
      _ = ∏ i, (Q (k i)).w (b i) := by
        symm
        exact Fintype.prod_equiv e (fun i => (Q (k i)).w (b i))
          (fun v => (Q v.1).w (b (e.symm v))) (by intro i; simp [e, coord])
  rw [FinProb.expect]
  rw [← Equiv.sum_comp ePi.symm
    (fun a => (FinProb.pi (fun v : S => Q v.1)).w a *
      ∏ i, f i (a (coord i)))]
  change (∑ b : I → α,
      (FinProb.pi (fun v : S => Q v.1)).w (ePi.symm b) *
        ∏ i, f i (ePi.symm b (coord i))) = _
  have hwpi (b : I → α) :
      (FinProb.pi (fun v : S => Q v.1)).w (ePi.symm b) =
        ∏ v : S, (Q v.1).w (ePi.symm b v) := rfl
  have hfpull (b : I → α) :
      (∏ i, f i (ePi.symm b (coord i))) = ∏ i, f i (b i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hPiValue]
    simp [coord, e]
  calc
    (∑ b : I → α,
        (FinProb.pi (fun v : S => Q v.1)).w (ePi.symm b) *
          ∏ i, f i (ePi.symm b (coord i))) =
        ∑ b : I → α, (∏ i, (Q (k i)).w (b i)) * ∏ i, f i (b i) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hwpi, hweight, hfpull]
    _ = (FinProb.pi (fun i : I => Q (k i))).expect (fun b => ∏ i, f i (b i)) := by
      rfl
    _ = ∏ i, (Q (k i)).expect (f i) := pi_expect_prod (fun i => Q (k i)) f

theorem eventually_power_gap (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  filter_upwards [hnlarge, htend.eventually_gt_atTop c] with n hn hlarge
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hnpos]; congr 1 <;> ring

theorem eventually_cross_width_budget (d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (d / 2) + 2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) ≤
        (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hexp : d + 1 / 32 < 5 / 32 := by linarith
  have hgap₁ := eventually_power_gap (d + 1 / 32) (5 / 32) 128 hexp (by norm_num)
  have hgap₂ := eventually_power_gap (5 / 32) (1 / 4) 2 (by norm_num) (by norm_num)
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  filter_upwards [hgap₁, hgap₂, hnlarge] with n h₁ h₂ hn
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnRone : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hSupper : (gS d n : ℝ) ≤ 2 * (n : ℝ) ^ d := by
    dsimp [gS]
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ d by positivity)
    have hpowge : 1 ≤ (n : ℝ) ^ d := Real.one_le_rpow hnRone (le_of_lt hd)
    linarith
  have hlog := Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1 / 32)
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hSnonneg : 0 ≤ (gS d n : ℝ) := by positivity
  have hcoeff : 0 ≤ 2 * (d / 80) ∧ 2 * (d / 80) ≤ 2 := by constructor <;> nlinarith
  have hnear :
      2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) ≤
        128 * (n : ℝ) ^ (d + 1 / 32) := by
    calc
      2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) ≤
          2 * (gS d n : ℝ) * Real.log (n : ℝ) := by
            have hcoeff' : 2 * (d / 80) * (gS d n : ℝ) ≤
                2 * (gS d n : ℝ) := by
              calc
                2 * (d / 80) * (gS d n : ℝ) =
                    (2 * (d / 80)) * (gS d n : ℝ) := by ring
                _ ≤ 2 * (gS d n : ℝ) := mul_le_mul_of_nonneg_right hcoeff.2 hSnonneg
            calc
              2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) =
                  (2 * (d / 80) * (gS d n : ℝ)) * Real.log (n : ℝ) := by ring
              _ ≤ (2 * (gS d n : ℝ)) * Real.log (n : ℝ) :=
                mul_le_mul_of_nonneg_right hcoeff' hlogNonneg
      _ ≤ 4 * (n : ℝ) ^ d * Real.log (n : ℝ) := by
            have htwos : 2 * (gS d n : ℝ) ≤ 4 * (n : ℝ) ^ d := by
              calc
                2 * (gS d n : ℝ) ≤ 2 * (2 * (n : ℝ) ^ d) :=
                  mul_le_mul_of_nonneg_left hSupper (by norm_num)
                _ = 4 * (n : ℝ) ^ d := by ring
            exact mul_le_mul_of_nonneg_right htwos hlogNonneg
      _ ≤ 128 * (n : ℝ) ^ d * (n : ℝ) ^ ((1 : ℝ) / 32) := by
            calc
              4 * (n : ℝ) ^ d * Real.log (n : ℝ) ≤
                  4 * (n : ℝ) ^ d * ((n : ℝ) ^ ((1 : ℝ) / 32) / ((1 : ℝ) / 32)) :=
                mul_le_mul_of_nonneg_left hlog (by positivity)
              _ = 128 * (n : ℝ) ^ d * (n : ℝ) ^ ((1 : ℝ) / 32) := by
                rw [div_eq_mul_inv]
                norm_num
                ring
      _ = 128 * (n : ℝ) ^ (d + 1 / 32) := by
            calc
              128 * (n : ℝ) ^ d * (n : ℝ) ^ ((1 : ℝ) / 32) =
                  128 * ((n : ℝ) ^ d * (n : ℝ) ^ ((1 : ℝ) / 32)) := by ring
              _ = 128 * (n : ℝ) ^ (d + 1 / 32) := by
                rw [← Real.rpow_add hnRpos]
  have hexpBase : d / 2 ≤ 5 / 32 := by linarith
  have hbase : (n : ℝ) ^ (d / 2) ≤ (n : ℝ) ^ ((5 : ℝ) / 32) := by
    exact Real.rpow_le_rpow_of_exponent_le hnRone hexpBase
  have hresult :
      (n : ℝ) ^ (d / 2) + 2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) <
        (n : ℝ) ^ ((1 : ℝ) / 4) := by
    calc
      (n : ℝ) ^ (d / 2) + 2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) ≤
          (n : ℝ) ^ ((5 : ℝ) / 32) + 128 * (n : ℝ) ^ (d + 1 / 32) :=
            add_le_add hbase hnear
      _ < 2 * (n : ℝ) ^ ((5 : ℝ) / 32) := by nlinarith [h₁]
      _ < (n : ℝ) ^ ((1 : ℝ) / 4) := h₂
  exact le_of_lt hresult

set_option maxHeartbeats 100000000 in
theorem tagBad_depends
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (D₀ : ℝ) (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (g : Γ.Key) :
    FinProb.DependsOn (TagBad Γ M D₀ · g) (Γ.keyBall g 1) := by
  classical
  intro σ σ' hagree
  have hself : g ∈ Γ.keyBall g 1 := by
    simp only [GridGeom.keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold GridGeom.keyDist
    simp [Nat.dist_self]
  have hσg : σ g = σ' g := hagree g hself
  let Scope := Γ.keyBall g 1
  let Pσ : Γ.Key → FinProb (Fin N) := fun h => M.μ (σ h)
  let Pσ' : Γ.Key → FinProb (Fin N) := fun h => M.μ (σ' h)
  let Bad : (Γ.Key → Fin N) → Prop := fun a => ¬ CrossValidRow Γ M (σ g) a g
  let F : (Γ.Key → Fin N) → ℝ := indicator Bad
  have hdep : FinProb.DependsOn F Scope := by
    intro a a' ha
    unfold F indicator Bad
    have hrow := crossValidRow_depends Γ M (σ g) g a a' ha
    have hrow' : CrossValidRow Γ M (σ g) a g = CrossValidRow Γ M (σ g) a' g := hrow
    rw [hrow']
  let z : Fin N := Classical.choice (pi_nonempty (M.μ (σ g)))
  let a₀ : Γ.Key → Fin N := fun _ => z
  have hP : (fun h : Scope => Pσ h.1) = (fun h : Scope => Pσ' h.1) := by
    funext h
    dsimp [Pσ, Pσ']
    rw [hagree h.1 h.2]
  have hleft : crossFailKey Γ M σ g =
      (FinProb.pi (fun h : Scope => Pσ h.1)).expect
        (fun a => F ((Equiv.piEquivPiSubtypeProd (fun h => h ∈ Scope) _).symm
          (a, fun h : {h // h ∉ Scope} => a₀ h.1))) := by
    unfold crossFailKey
    rw [pr_eq_expect_indicator]
    exact FinProb.pi_expect_depends Pσ Scope F a₀ hdep
  have hright : crossFailKey Γ M σ' g =
      (FinProb.pi (fun h : Scope => Pσ' h.1)).expect
        (fun a => F ((Equiv.piEquivPiSubtypeProd (fun h => h ∈ Scope) _).symm
          (a, fun h : {h // h ∉ Scope} => a₀ h.1))) := by
    unfold crossFailKey
    rw [show (fun a : Γ.Key → Fin N => ¬ CrossValidRow Γ M (σ' g) a g) = Bad by
      funext a
      rw [← hσg]]
    rw [pr_eq_expect_indicator]
    exact FinProb.pi_expect_depends Pσ' Scope F a₀ hdep
  have hfail : crossFailKey Γ M σ g = crossFailKey Γ M σ' g := by
    calc
      crossFailKey Γ M σ g =
          (FinProb.pi (fun h : Scope => Pσ h.1)).expect
            (fun a => F ((Equiv.piEquivPiSubtypeProd (fun h => h ∈ Scope) _).symm
              (a, fun h : {h // h ∉ Scope} => a₀ h.1))) := hleft
      _ = (FinProb.pi (fun h : Scope => Pσ' h.1)).expect
            (fun a => F ((Equiv.piEquivPiSubtypeProd (fun h => h ∈ Scope) _).symm
              (a, fun h : {h // h ∉ Scope} => a₀ h.1))) := by rw [hP]
      _ = crossFailKey Γ M σ' g := hright.symm
  change ((n : ℝ) ^ (-(D₀ / 2)) < crossFailKey Γ M σ g) =
    ((n : ℝ) ^ (-(D₀ / 2)) < crossFailKey Γ M σ' g)
  rw [hfail]

set_option maxHeartbeats 100000000 in
theorem eventually_tag_moment_small (D₀ d : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d)
    (hd' : d < D₀ / 1000) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * (2 * (n : ℝ) ^ (-d / 4)) ^ gS d n *
        Real.exp ((n : ℝ) ^ (d / 2)) ≤ 1 := by
  have hbaseGap : ∀ᶠ n : ℕ in Filter.atTop, 2 * (n : ℝ) ^ (0 : ℝ) < (n : ℝ) ^ (d / 8) :=
    eventually_power_gap 0 (d / 8) 2 (by linarith) (by norm_num)
  have hdomGap : ∀ᶠ n : ℕ in Filter.atTop,
      (16 / d) * (n : ℝ) ^ (d / 2) < (n : ℝ) ^ d :=
    eventually_power_gap (d / 2) d (16 / d) (by linarith) (div_pos (by norm_num) hd)
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log (n : ℝ) := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop 1
  have hnlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (((hbaseGap.and hdomGap).and hlog).and hnlarge)
  filter_upwards [Filter.eventually_atTop.2 ⟨n₀, fun n hn => hn₀ n hn⟩] with n hn₀n
  rcases hn₀n with ⟨⟨⟨hbaseN, hdomN⟩, hlogN⟩, hn2⟩
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnRone : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  let u : ℝ := (n : ℝ) ^ (d / 8)
  have huPos : 0 < u := Real.rpow_pos_of_pos hnRpos _
  have hu : 1 ≤ u := by
    dsimp [u]
    exact Real.one_le_rpow hnRone (by positivity)
  have hbaseN' : 2 < u := by simpa [u] using hbaseN
  have hu2 : u ^ 2 = (n : ℝ) ^ (d / 4) := by
    dsimp [u]
    calc
      ((n : ℝ) ^ (d / 8)) ^ 2 = (n : ℝ) ^ ((d / 8) * 2) :=
        (Real.rpow_mul_natCast hnRpos.le (d / 8) 2).symm
      _ = (n : ℝ) ^ (d / 4) := by congr 1 <;> ring
  have hsmallDen : 2 / u ^ 2 ≤ 1 / u := by
    apply (div_le_iff₀ (sq_pos_of_pos huPos)).2
    have hmul : (1 / u) * u ^ 2 = u := by field_simp [ne_of_gt huPos]
    rw [hmul]
    exact le_of_lt hbaseN'
  have hbase : 2 * (n : ℝ) ^ (-d / 4) ≤ (n : ℝ) ^ (-d / 8) := by
    have he1 : -d / 4 = -(d / 4) := by ring
    have he2 : -d / 8 = -(d / 8) := by ring
    rw [he1, Real.rpow_neg hnRpos.le, he2, Real.rpow_neg hnRpos.le, ← hu2]
    simpa [u, div_eq_mul_inv] using hsmallDen
  have hsLower : (n : ℝ) ^ d ≤ (gS d n : ℝ) := by
    dsimp [gS]
    exact Nat.le_ceil _
  have hcoefNonpos : -d / 8 ≤ 0 := by
    rw [show -d / 8 = -(d / 8) by ring]
    exact neg_nonpos.mpr (div_nonneg hd.le (by norm_num))
  have hExpLower : (-d / 8) * (gS d n : ℝ) ≤ (-d / 8) * (n : ℝ) ^ d :=
    mul_le_mul_of_nonpos_left hsLower hcoefNonpos
  have hfBase : 0 ≤ 2 * (n : ℝ) ^ (-d / 4) := by positivity
  have hf : (2 * (n : ℝ) ^ (-d / 4)) ^ gS d n ≤
      (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) := by
    calc
      (2 * (n : ℝ) ^ (-d / 4)) ^ gS d n ≤
          ((n : ℝ) ^ (-d / 8)) ^ gS d n := pow_le_pow_left₀ hfBase hbase _
      _ = (n : ℝ) ^ ((-d / 8) * (gS d n : ℝ)) :=
        (Real.rpow_mul_natCast hnRpos.le (-d / 8) (gS d n)).symm
      _ ≤ (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) :=
        Real.rpow_le_rpow_of_exponent_le hnRone hExpLower
  have hL : Real.exp ((n : ℝ) ^ (d / 2)) ≤ (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) := by
    have hRpow : (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) =
        Real.exp (Real.log (n : ℝ) * (n : ℝ) ^ (d / 2)) :=
      Real.rpow_def_of_pos hnRpos _
    have hpowNonneg : 0 ≤ (n : ℝ) ^ (d / 2) := Real.rpow_nonneg hnRpos.le _
    calc
      Real.exp ((n : ℝ) ^ (d / 2)) ≤
          Real.exp (Real.log (n : ℝ) * (n : ℝ) ^ (d / 2)) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hlogN) hpowNonneg])
      _ = (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) := hRpow.symm
  have hdomScaled : (n : ℝ) ^ (d / 2) < (d / 16) * (n : ℝ) ^ d := by
    have hscalePos : 0 < d / 16 := div_pos hd (by norm_num : (0 : ℝ) < 16)
    have h := mul_lt_mul_of_pos_left hdomN hscalePos
    have hcoef : (d / 16) * (16 / d) = 1 := by
      field_simp [ne_of_gt hd]
      <;> ring
    have hleft : (d / 16) * ((16 / d) * (n : ℝ) ^ (d / 2)) =
        (n : ℝ) ^ (d / 2) := by
      rw [← mul_assoc, hcoef, one_mul]
    rw [hleft] at h
    exact h
  have hpowge : 1 ≤ (n : ℝ) ^ (d / 2) := Real.one_le_rpow hnRone (by positivity)
  have hdomScaled' : (d / 8) * (n : ℝ) ^ d > (n : ℝ) ^ (d / 2) + 1 := by
    nlinarith [hdomScaled, hpowge]
  have hexp : 1 + (-d / 8) * (n : ℝ) ^ d + (n : ℝ) ^ (d / 2) ≤ 0 := by
    nlinarith [hdomScaled']
  have hprodPow : (n : ℝ) * (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) *
      (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) =
        (n : ℝ) ^ (1 + (-d / 8) * (n : ℝ) ^ d + (n : ℝ) ^ (d / 2)) := by
    have hpowone : (n : ℝ) ^ (1 : ℝ) = (n : ℝ) := Real.rpow_one _
    have hpowadd1 : (n : ℝ) ^ (1 : ℝ) *
        (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) =
          (n : ℝ) ^ (1 + (-d / 8) * (n : ℝ) ^ d) :=
      (Real.rpow_add hnRpos (1 : ℝ) ((-d / 8) * (n : ℝ) ^ d)).symm
    have hpowadd2 : (n : ℝ) ^ (1 + (-d / 8) * (n : ℝ) ^ d) *
        (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) =
          (n : ℝ) ^ ((1 + (-d / 8) * (n : ℝ) ^ d) + (n : ℝ) ^ (d / 2)) :=
      (Real.rpow_add hnRpos (1 + (-d / 8) * (n : ℝ) ^ d) ((n : ℝ) ^ (d / 2))).symm
    calc
      (n : ℝ) * (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) *
          (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) *
            (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) := by
        have hFirst : (n : ℝ) * (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) =
            (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) :=
          congrArg (fun z : ℝ => z * (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d)) hpowone.symm
        exact congrArg (fun z : ℝ => z * (n : ℝ) ^ ((n : ℝ) ^ (d / 2))) hFirst
      _ = (n : ℝ) ^ (1 + (-d / 8) * (n : ℝ) ^ d + (n : ℝ) ^ (d / 2)) := by
        calc
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) *
              (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) =
              (n : ℝ) ^ (1 + (-d / 8) * (n : ℝ) ^ d) *
                (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) := by rw [hpowadd1]
          _ = (n : ℝ) ^ ((1 + (-d / 8) * (n : ℝ) ^ d) + (n : ℝ) ^ (d / 2)) := hpowadd2
          _ = _ := by congr 1 <;> ring
  calc
    (n : ℝ) * (2 * (n : ℝ) ^ (-d / 4)) ^ gS d n *
        Real.exp ((n : ℝ) ^ (d / 2)) ≤
      (n : ℝ) * (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) *
        (n : ℝ) ^ ((n : ℝ) ^ (d / 2)) := by
      calc
        _ ≤ (n : ℝ) * (n : ℝ) ^ ((-d / 8) * (n : ℝ) ^ d) *
              Real.exp ((n : ℝ) ^ (d / 2)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hnRpos.le)
            (Real.exp_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hL (by positivity)
    _ = (n : ℝ) ^ (1 + (-d / 8) * (n : ℝ) ^ d + (n : ℝ) ^ (d / 2)) := hprodPow
    _ ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le hnRone hexp
      simpa using h

private theorem dens_eq_sum_rowDeg {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) : dens E c μ ν = ∑ x, μ.w x * rowDeg E c x ν := by
  classical
  unfold dens rowDeg
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

set_option maxHeartbeats 100000000 in
theorem low_degree_mass_bound
    {N : ℕ} (D₀ d : ℝ) (n : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
    (X Y : Finset (Fin N)) (K : ℝ) (α τ : Law N)
    (hN : 0 < N) (hn : 0 < n) (hK : 0 < K)
    (hEq : Eq71At D₀ d n N E X Y)
    (hαsupp : α.SupportedIn X) (hτsupp : τ.SupportedIn Y)
    (hαcap : α.CapLE K) (hτwidth : τ.WidthLE ((n : ℝ) ^ ((1 : ℝ) / 4))) :
    (∑ x ∈ Finset.univ.filter (fun x => rowDeg E G x τ < (n : ℝ) ^ (-(d / 80))), α.w x) <
      K * (n : ℝ) ^ (-D₀) := by
  classical
  let θ : ℝ := (n : ℝ) ^ (-(d / 80))
  let H : Finset (Fin N) := Finset.univ.filter (fun x => rowDeg E G x τ < θ)
  let massH : ℝ := ∑ x ∈ H, α.w x
  by_contra hnot
  have hlarge : K * (n : ℝ) ^ (-D₀) ≤ massH := by
    dsimp [massH, H, θ]
    exact le_of_not_gt hnot
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpowPos : 0 < (n : ℝ) ^ (-D₀) := Real.rpow_pos_of_pos hnRpos _
  have hmassPos : 0 < massH :=
    lt_of_lt_of_le (mul_pos hK hpowPos) hlarge
  let ρ : Law N := α.restrict H hmassPos
  have hρsupp : ρ.SupportedIn X := by
    intro x hxX
    by_cases hxH : x ∈ H
    · have hαx : α.w x = 0 := hαsupp x hxX
      simp [ρ, Law.restrict, hxH, hαx]
    · simp [ρ, Law.restrict, hxH]
  have hρcap : ρ.CapLE ((n : ℝ) ^ D₀) := by
    intro x
    by_cases hxH : x ∈ H
    · have hrestrict : ρ.w x = α.w x / massH := by simp [ρ, Law.restrict, hxH, massH]
      have hαbound : (N : ℝ) * α.w x / massH ≤ K / massH :=
        div_le_div_of_nonneg_right (hαcap x) hmassPos.le
      have hpowerCancel : (n : ℝ) ^ D₀ * (n : ℝ) ^ (-D₀) = 1 := by
        rw [← Real.rpow_add hnRpos]
        simp
      have hNumerator : K ≤ (n : ℝ) ^ D₀ * massH := by
        calc
          K = K * ((n : ℝ) ^ D₀ * (n : ℝ) ^ (-D₀)) := by rw [hpowerCancel, mul_one]
          _ = (n : ℝ) ^ D₀ * (K * (n : ℝ) ^ (-D₀)) := by ring
          _ ≤ (n : ℝ) ^ D₀ * massH :=
            mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hnRpos.le _)
      have hKdiv : K / massH ≤ (n : ℝ) ^ D₀ :=
        (div_le_iff₀ hmassPos).2 (by simpa [mul_comm] using hNumerator)
      calc
        (N : ℝ) * ρ.w x = (N : ℝ) * α.w x / massH := by rw [hrestrict]; ring
        _ ≤ K / massH := hαbound
        _ ≤ (n : ℝ) ^ D₀ := hKdiv
    · simp [ρ, Law.restrict, hxH]
      positivity
  have hdensLow : dens E G ρ τ ≤ θ := by
    rw [dens_eq_sum_rowDeg]
    have hsum : (∑ x, ρ.w x * rowDeg E G x τ) ≤ ∑ x, ρ.w x * θ := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hxH : x ∈ H
      · have hrow : rowDeg E G x τ < θ := (Finset.mem_filter.mp hxH).2
        exact mul_le_mul_of_nonneg_left hrow.le (ρ.nonneg x)
      · have hρx : ρ.w x = 0 := by simp [ρ, Law.restrict, hxH]
        simp [hρx]
    calc
      (∑ x, ρ.w x * rowDeg E G x τ) ≤ ∑ x, ρ.w x * θ := hsum
      _ = (∑ x, ρ.w x) * θ := by rw [Finset.sum_mul]
      _ = θ := by rw [ρ.sum_eq_one, one_mul]
  have hEq71 := hEq ρ τ hρsupp hτsupp hρcap hτwidth G
  have hθ : (n : ℝ) ^ (-(d / 80)) < dens E G ρ τ := by
    simpa [θ] using hEq71
  dsimp [θ] at hdensLow
  linarith

theorem tagAnchor_pi_crossFail
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) (g : Γ.Key) :
    (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g) =
      (FinProb.pi (tagAnchorLaw Γ M Q)).pr
        (fun z => ¬ CrossValidRow Γ M (z g).1
          (fun h => (z h).2) g) := by
  classical
  let e : (Γ.Key → M.ι × Fin N) ≃ ((Γ.Key → M.ι) × (Γ.Key → Fin N)) :=
    { toFun := fun z => ((fun h => (z h).1), fun h => (z h).2)
      invFun := fun p h => (p.1 h, p.2 h)
      left_inv := by
        intro z
        funext h
        change ((z h).1, (z h).2) = z h
        cases z h
        rfl
      right_inv := by
        intro p
        cases p with
        | mk σ a =>
          apply Prod.ext
          · funext h
            rfl
          · funext h
            rfl }
  have hleft :
      (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g) =
        ∑ σ : Γ.Key → M.ι, ∑ a : Γ.Key → Fin N,
          if ¬ CrossValidRow Γ M (σ g) a g then
            (∏ h, (Q h).w (σ h)) * (∏ h, (M.μ (σ h)).w (a h)) else 0 := by
    simp only [FinProb.expect, crossFailKey, FinProb.pr, FinProb.pi]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hbad : ¬ CrossValidRow Γ M (σ g) a g <;> simp [hbad] <;> ring
  have hright :
      (FinProb.pi (tagAnchorLaw Γ M Q)).pr
          (fun z => ¬ CrossValidRow Γ M (z g).1 (fun h => (z h).2) g) =
        ∑ σ : Γ.Key → M.ι, ∑ a : Γ.Key → Fin N,
          if ¬ CrossValidRow Γ M (σ g) a g then
            (∏ h, (Q h).w (σ h)) * (∏ h, (M.μ (σ h)).w (a h)) else 0 := by
    rw [pr_eq_expect_indicator]
    simp only [FinProb.expect, FinProb.pi, tagAnchorLaw, FinProb.bind]
    let F : (Γ.Key → M.ι × Fin N) → ℝ := fun z =>
      (∏ h, ((Q h).w ((z h).1) * (M.μ ((z h).1)).w ((z h).2))) *
        indicator (fun z => ¬ CrossValidRow Γ M (z g).1 (fun h => (z h).2) g) z
    calc
      (∑ z : Γ.Key → M.ι × Fin N,
          (∏ h, ((Q h).w ((z h).1) * (M.μ ((z h).1)).w ((z h).2))) *
            indicator (fun z => ¬ CrossValidRow Γ M (z g).1 (fun h => (z h).2) g) z) =
          ∑ p : ((Γ.Key → M.ι) × (Γ.Key → Fin N)), F (e.symm p) := by
        simpa [F] using (Equiv.sum_comp e.symm F).symm
      _ = ∑ σ : Γ.Key → M.ι, ∑ a : Γ.Key → Fin N,
          if ¬ CrossValidRow Γ M (σ g) a g then
            (∏ h, (Q h).w (σ h)) * (∏ h, (M.μ (σ h)).w (a h)) else 0 := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro σ hσ
        apply Finset.sum_congr rfl
        intro a ha
        have heval : e.symm (σ, a) = fun h => (σ h, a h) := by
          funext h
          rfl
        rw [heval]
        by_cases hbad : ¬ CrossValidRow Γ M (σ g) a g
        · simp [F, indicator, hbad, Finset.prod_mul_distrib]
        · simp [F, indicator, hbad, Finset.prod_mul_distrib]
  rw [hleft, hright]

private theorem tagAnchor_low_degree_pr_le
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) (D₀ d' K : ℝ) (g : Γ.Key) (τ : Law N)
    (hN : 0 < N) (hn : 0 < n) (hK : 0 < K)
    (hmean : ∀ g x, (N : ℝ) * ∑ i, (Q g).w i * (M.μ i).w x ≤ K)
    (hEq : Eq71At D₀ d' n N E X Y)
    (hτsupp : τ.SupportedIn Y)
    (hτwidth : τ.WidthLE ((n : ℝ) ^ ((1 : ℝ) / 4))) :
    (tagAnchorLaw Γ M Q g).pr
      (fun z => rowDeg E G z.2 τ < (n : ℝ) ^ (-(d' / 80))) ≤
        K * (n : ℝ) ^ (-D₀) := by
  classical
  let α : Law N := Law.mix (Q g) M.μ
  let Bad : Fin N → Prop := fun x => rowDeg E G x τ < (n : ℝ) ^ (-(d' / 80))
  let H : Finset (Fin N) := Finset.univ.filter Bad
  have hαsupp : α.SupportedIn X := by
    intro x hx
    change ∑ i, (Q g).w i * (M.μ i).w x = 0
    apply Finset.sum_eq_zero
    intro i hi
    rw [M.μ_supp i x hx]
    simp
  have hαcap : α.CapLE K := by
    intro x
    simpa [α, Law.mix] using hmean g x
  have hlow := low_degree_mass_bound D₀ d' n E G X Y K α τ hN hn hK hEq
    hαsupp hτsupp hαcap hτwidth
  have hpr : (tagAnchorLaw Γ M Q g).pr (fun z => Bad z.2) =
      ∑ x ∈ H, α.w x := by
    calc
      (tagAnchorLaw Γ M Q g).pr (fun z => Bad z.2) = α.pr Bad :=
        tagAnchor_pr_snd Γ M Q g Bad
      _ = ∑ x ∈ H, α.w x := by
        unfold FinProb.pr
        simp [H, Bad, Finset.sum_filter]
  rw [hpr]
  exact hlow.le

private theorem crossOrder_nodup
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (g h₀ : Γ.Key)
    (hh₀ : h₀ ∈ Γ.crossKeys g) : (Γ.crossOrder g h₀).Nodup := by
  classical
  have hkeys : (Γ.crossKeys g).Nodup := by
    simpa [GridGeom.crossKeys] using (Γ.keyNbrs g).nodup_toList
  have hErase : ((Γ.crossKeys g).erase h₀).Nodup := hkeys.erase _
  have h₀not : h₀ ∉ (Γ.crossKeys g).erase h₀ := by
    intro hx
    exact hkeys.not_mem_erase hx
  have hdisj : List.Disjoint ((Γ.crossKeys g).erase h₀) [h₀] := by
    rw [List.disjoint_iff_ne]
    intro x hx y hy heq
    subst y
    have hxEq : x = h₀ := List.mem_singleton.mp hy
    subst x
    exact h₀not hx
  simpa [GridGeom.crossOrder] using hErase.append (by simp) hdisj

private theorem crossOrder_length
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (g h₀ : Γ.Key)
    (hh₀ : h₀ ∈ Γ.crossKeys g) :
    (Γ.crossOrder g h₀).length = (Γ.crossKeys g).length := by
  have hlen : 0 < (Γ.crossKeys g).length := List.length_pos_of_mem hh₀
  simp [GridGeom.crossOrder, List.length_erase_of_mem hh₀]
  omega

private theorem crossOrder_mem_crossKeys
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (g h₀ : Γ.Key)
    (hh₀ : h₀ ∈ Γ.crossKeys g) {x : Γ.Key}
    (hx : x ∈ Γ.crossOrder g h₀) : x ∈ Γ.crossKeys g := by
  unfold GridGeom.crossOrder at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_of_mem_erase hx
  · exact (List.mem_singleton.mp hx) ▸ hh₀

private theorem keyNbr_ne_center
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (g h : Γ.Key)
    (hh : h ∈ Γ.keyNbrs g) : h ≠ g := by
  intro heq
  subst h
  have hh' : Γ.keyDist g g = 1 := by simpa [GridGeom.keyNbrs] using hh
  simp [GridGeom.keyDist] at hh'

private theorem exists_first_bad
    (m : ℕ) (Bad : ℕ → Prop) (hbad : ∃ k < m, Bad k) :
    ∃ k < m, Bad k ∧ ∀ j < k, ¬ Bad j := by
  classical
  obtain ⟨w, hwm, hw⟩ := hbad
  let hp : ∃ k, Bad k := ⟨w, hw⟩
  let k := Nat.find hp
  have hkBad : Bad k := Nat.find_spec hp
  have hkw : k ≤ w := Nat.find_min' hp hw
  have hkle : k < m := lt_of_le_of_lt hkw hwm
  refine ⟨k, hkle, hkBad, ?_⟩
  intro j hj hjBad
  have hkj : k ≤ j := Nat.find_min' hp hjBad
  omega

private theorem get_not_mem_take_of_nodup
    {α : Type*} [DecidableEq α] (L : List α) (hnd : L.Nodup)
    (i : Fin L.length) : L.get i ∉ L.take i.val := by
  have htakeNodup : (L.take (i.val + 1)).Nodup := hnd.take
  have happend : L.take i.val ++ [L.get i] = L.take (i.val + 1) := by
    simpa using List.take_concat_get' L i.val i.isLt
  rw [← happend] at htakeNodup
  have hdisj := (List.nodup_append'.mp htakeNodup).2.2
  intro hmem
  have hne := (List.disjoint_iff_ne.mp hdisj) (L.get i) hmem (L.get i) (by simp)
  exact hne rfl

private def crossStepPrefixGood
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (z : Γ.Key → M.ι × Fin N) (g h₀ : Γ.Key) (k : ℕ) : Prop :=
  let ν := M.ν ((z g).1)
  let anchors := (Γ.crossOrder g h₀).map fun h => (z h).2
  (∀ j < k,
    (n : ℝ) ^ (-(d / 80)) * filterMass E G ν (anchors.take j) ≤
      filterMass E G ν (anchors.take (j + 1)))

def crossStepBad
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (z : Γ.Key → M.ι × Fin N) (g h₀ : Γ.Key) (k : ℕ) : Prop :=
  crossStepPrefixGood Γ M z g h₀ k ∧
    let ν := M.ν ((z g).1)
    let anchors := (Γ.crossOrder g h₀).map fun h => (z h).2
    ¬ ((n : ℝ) ^ (-(d / 80)) * filterMass E G ν (anchors.take k) ≤
      filterMass E G ν (anchors.take (k + 1)))

theorem crossFail_imp_exists_step
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (z : Γ.Key → M.ι × Fin N) (g : Γ.Key)
    (hfail : ¬ CrossValidRow Γ M (z g).1 (fun h => (z h).2) g) :
    ∃ h₀ ∈ Γ.crossKeys g, ∃ k < (Γ.crossKeys g).length,
      crossStepBad Γ M z g h₀ k := by
  classical
  change ¬ (∀ h₀ ∈ Γ.crossKeys g, ∀ k < (Γ.crossKeys g).length,
    (n : ℝ) ^ (-(d / 80)) *
        filterMass E G (M.ν ((z g).1)) (((Γ.crossOrder g h₀).map fun h => (z h).2).take k) ≤
      filterMass E G (M.ν ((z g).1)) (((Γ.crossOrder g h₀).map fun h => (z h).2).take (k + 1)))
    at hfail
  push_neg at hfail
  obtain ⟨h₀, hh₀, k, hk, hkbad⟩ := hfail
  let ν := M.ν ((z g).1)
  let anchors := (Γ.crossOrder g h₀).map fun h => (z h).2
  let Bad : ℕ → Prop := fun j =>
    ¬ ((n : ℝ) ^ (-(d / 80)) * filterMass E G ν (anchors.take j) ≤
      filterMass E G ν (anchors.take (j + 1)))
  have hfirstInput : ∃ j < (Γ.crossOrder g h₀).length, Bad j := by
    refine ⟨k, ?_, ?_⟩
    · simpa only [crossOrder_length Γ g h₀ hh₀] using hk
    · simpa [Bad, ν, anchors] using hkbad
  obtain ⟨k₀, hk₀, hk₀bad, hprev⟩ :=
    exists_first_bad (Γ.crossOrder g h₀).length Bad hfirstInput
  refine ⟨h₀, hh₀, k₀, ?_, ?_⟩
  · rw [crossOrder_length Γ g h₀ hh₀] at hk₀
    exact hk₀
  · dsimp [crossStepBad]
    constructor
    · intro j hj
      by_contra hnot
      exact hprev j hj hnot
    · simpa [Bad, ν, anchors] using hk₀bad

set_option maxHeartbeats 100000000 in
theorem crossStepBad_pr_le
    {d : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) (D₀ K : ℝ) (g h₀ : Γ.Key)
    (hh₀ : h₀ ∈ Γ.crossKeys g) (k : Fin (Γ.crossKeys g).length)
    (hN : 0 < N) (hn : 2 ≤ n) (hd : 0 ≤ d) (hloc : GeomLocal Γ)
    (hmean : ∀ g x, (N : ℝ) * ∑ i, (Q g).w i * (M.μ i).w x ≤ K)
    (hEq : Eq71At D₀ d n N E X Y)
    (hbudget : (n : ℝ) ^ (d / 2) +
      2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) ≤
        (n : ℝ) ^ ((1 : ℝ) / 4)) :
    (FinProb.pi (tagAnchorLaw Γ M Q)).pr
      (fun z => crossStepBad Γ M z g h₀ k.val) ≤
        K * (n : ℝ) ^ (-D₀) := by
  classical
  let O := Γ.crossOrder g h₀
  have hOlen := crossOrder_length Γ g h₀ hh₀
  have hkO : k.val < O.length := by
    change k.val < (Γ.crossOrder g h₀).length
    rw [crossOrder_length Γ g h₀ hh₀]
    exact k.isLt
  have hOndup : O.Nodup := by simpa [O] using crossOrder_nodup Γ g h₀ hh₀
  let curr : Γ.Key := O.get ⟨k.val, hkO⟩
  have hcurrNotPrev : curr ∉ O.take k.val := by
    dsimp [curr, O]
    exact get_not_mem_take_of_nodup _ hOndup _
  have hcurrMem : curr ∈ Γ.crossKeys g := by
    exact crossOrder_mem_crossKeys Γ g h₀ hh₀ (List.get_mem O ⟨k.val, hkO⟩)
  have hcurrNbr : curr ∈ Γ.keyNbrs g := by
    simpa [GridGeom.crossKeys] using hcurrMem
  have hcurrNe : curr ≠ g := keyNbr_ne_center Γ g curr hcurrNbr
  have hkeyBound : k.val ≤ 2 * gS d n := by
    have hlen : (Γ.crossKeys g).length ≤ 2 * gS d n := by
      calc
        (Γ.crossKeys g).length = (Γ.keyNbrs g).card := by simp [GridGeom.crossKeys]
        _ ≤ 2 * gS d n := hloc.keyNbrs_card g
    exact le_trans (Nat.le_of_lt k.isLt) hlen
  let α : Law N := Law.mix (Q curr) M.μ
  have hαcap : α.CapLE K := by
    intro x
    simpa [α, Law.mix] using hmean curr x
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hKone : 1 ≤ K := by
    have hsum : (N : ℝ) ≤ (N : ℝ) * K := by
      calc
        (N : ℝ) = ∑ x, (N : ℝ) * α.w x := by
          calc
            (N : ℝ) = (N : ℝ) * 1 := by ring
            _ = (N : ℝ) * ∑ x, α.w x := by rw [α.sum_eq_one]
            _ = ∑ x, (N : ℝ) * α.w x := by rw [Finset.mul_sum]
        _ ≤ ∑ x, K := Finset.sum_le_sum fun x hx => hαcap x
        _ = (N : ℝ) * K := by simp
    nlinarith
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hKone
  let A : (Γ.Key → M.ι × Fin N) → Prop := fun z => crossStepBad Γ M z g h₀ k.val
  apply pi_pr_bound_of_glue_singleton (tagAnchorLaw Γ M Q) curr A
    (K * (n : ℝ) ^ (-D₀))
  intro ω
  let r₀ : M.ι × Fin N := Classical.choice (pi_nonempty (tagAnchorLaw Γ M Q curr))
  let z₀ : Γ.Key → M.ι × Fin N := glue {curr} ω (fun _ => r₀)
  let zOf : (M.ι × Fin N) → Γ.Key → M.ι × Fin N := fun r => glue {curr} ω (fun _ => r)
  have hprefix (r : M.ι × Fin N) :
      ((O.map fun h => (zOf r h).2).take k.val) =
        ((O.map fun h => (z₀ h).2).take k.val) := by
    rw [← List.map_take, ← List.map_take]
    apply List.map_congr_left
    intro h hh
    have hne : h ≠ curr := by
      intro heq
      subst h
      exact hcurrNotPrev hh
    simp [zOf, z₀, glue, hne]
  have htag (r : M.ι × Fin N) : (zOf r g).1 = (z₀ g).1 := by
    have hg : g ≠ curr := Ne.symm hcurrNe
    simp [zOf, z₀, glue, hg]
  have hprefixJ (r : M.ι × Fin N) (j : ℕ) (hj : j ≤ k.val) :
      ((O.map fun h => (zOf r h).2).take j) =
        ((O.map fun h => (z₀ h).2).take j) := by
    by_cases hjEq : j = k.val
    · subst j
      exact hprefix r
    · have hjlt : j < k.val := lt_of_le_of_ne hj hjEq
      calc
        ((O.map fun h => (zOf r h).2).take j) =
            (((O.map fun h => (zOf r h).2).take k.val).take j) := by
              rw [List.take_take]
              simp [Nat.min_eq_left (Nat.le_of_lt hjlt)]
        _ = (((O.map fun h => (z₀ h).2).take k.val).take j) := by rw [hprefix r]
        _ = ((O.map fun h => (z₀ h).2).take j) := by
              rw [List.take_take]
              simp [Nat.min_eq_left (Nat.le_of_lt hjlt)]
  have hprevEq (r : M.ι × Fin N) :
      crossStepPrefixGood Γ M (zOf r) g h₀ k.val =
        crossStepPrefixGood Γ M z₀ g h₀ k.val := by
    apply propext
    dsimp only [crossStepPrefixGood]
    rw [htag r]
    constructor
    · intro h j hj
      have hstep := h j hj
      rw [hprefixJ r j (Nat.le_of_lt hj), hprefixJ r (j + 1) (by omega)] at hstep
      exact hstep
    · intro h j hj
      have hstep := h j hj
      rw [← hprefixJ r j (Nat.le_of_lt hj), ← hprefixJ r (j + 1) (by omega)] at hstep
      exact hstep
  by_cases hprev : crossStepPrefixGood Γ M z₀ g h₀ k.val
  · let ν := M.ν ((z₀ g).1)
    let anchors₀ := O.map fun h => (z₀ h).2
    let L₀ := anchors₀.take k.val
    let τ : Law N := filtLaw E G ν L₀
    have hgood : ∀ j < k.val,
        (n : ℝ) ^ (-(d / 80)) * filterMass E G ν (anchors₀.take j) ≤
          filterMass E G ν (anchors₀.take (j + 1)) := by
      simpa [crossStepPrefixGood, ν, anchors₀, O] using hprev
    have hmassTheta := cross_prefix_mass_lower E G ν n d anchors₀ k.val hgood
    have hthetaPos : 0 < (n : ℝ) ^ (-(d / 80)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
    have hmassPos : 0 < filterMass E G ν L₀ :=
      lt_of_lt_of_le (pow_pos hthetaPos k.val) hmassTheta
    have hτsupp : τ.SupportedIn Y := by
      intro y hy
      by_cases hp : passesAnchors E G L₀ y
      · have hνy := M.ν_supp ((z₀ g).1) y hy
        have hνy' : ν.w y = 0 := by simpa [ν] using hνy
        simp [τ, ν, filtLaw, filt, hmassPos, hp, hνy']
      · simp [τ, filtLaw, filt, hmassPos, hp]
    have hrawWidth : ν.WidthLE ((n : ℝ) ^ (d / 2)) := (M.pure ((z₀ g).1)).2.1
    have hτwidth := filtLaw_width_of_cross_prefix E G ν n d hd anchors₀ k.val
      hN hn hrawWidth hgood hkeyBound hbudget
    have hlow := tagAnchor_low_degree_pr_le Γ M Q D₀ d K curr τ hN
      (by exact_mod_cast (by omega : 0 < n)) hKpos hmean hEq hτsupp hτwidth
    have happend (r : M.ι × Fin N) :
        (O.map fun h => (zOf r h).2).take (k.val + 1) = L₀ ++ [r.2] := by
      have hkmap : k.val < (O.map fun h => (zOf r h).2).length := by simpa using hkO
      rw [← List.take_concat_get' (O.map fun h => (zOf r h).2) k.val hkmap]
      rw [hprefix r]
      simp [L₀, anchors₀, zOf, curr, glue]
    have hstepEq (r : M.ι × Fin N) :
        A (zOf r) ↔ rowDeg E G r.2 τ < (n : ℝ) ^ (-(d / 80)) := by
      change crossStepBad Γ M (zOf r) g h₀ k.val ↔ _
      rw [crossStepBad, hprevEq r, htag r]
      simp [hprev]
      rw [hprefix r, happend r]
      have hratio := rowDeg_filtLaw_append E G ν L₀ r.2 hmassPos
      rw [hratio]
      rw [div_lt_iff₀ hmassPos]
    have hprobEq :
        (tagAnchorLaw Γ M Q curr).pr (fun r => A (zOf r)) =
          (tagAnchorLaw Γ M Q curr).pr
            (fun r => rowDeg E G r.2 τ < (n : ℝ) ^ (-(d / 80))) := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro r hr
      simp [hstepEq r]
    rw [hprobEq]
    exact hlow
  · have hzero : ∀ r : M.ι × Fin N, ¬ A (zOf r) := by
      intro r hstep
      have hprevR := hstep.1
      rw [hprevEq r] at hprevR
      exact hprev hprevR
    have hpr : (tagAnchorLaw Γ M Q curr).pr (fun r => A (zOf r)) = 0 := by
      unfold FinProb.pr
      rw [Finset.sum_eq_zero]
      intro r hr
      simp [hzero r]
    rw [hpr]
    positivity

end TagStageQ

end HypercubeRamsey.S07
