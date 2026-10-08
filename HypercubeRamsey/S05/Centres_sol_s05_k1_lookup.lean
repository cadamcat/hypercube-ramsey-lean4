import HypercubeRamsey.S05.Centres_sol_s05_k1_mass
import HypercubeRamsey.S05.Centres_sol_s05_k1_rows
import HypercubeRamsey.S05.Centres_sol_s05_k1_records

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i, Fintype (A i)]

theorem pi_pr_forall (P : ∀ i, FinProb (A i)) (F : ∀ i, A i → Prop) :
    (FinProb.pi P).pr (fun ω => ∀ i, F i (ω i)) = ∏ i, (P i).pr (F i) := by
  unfold FinProb.pr FinProb.pi
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hf : ∀ i, F i (ω i)
  · simp [hf]
  · rw [if_neg hf]
    obtain ⟨i, hi⟩ := not_forall.mp hf
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem pi_nested_cylinder_pr {J : Type*} [Fintype J] [DecidableEq J]
    {B : J → Type*} [∀ j, Fintype (B j)]
    (P : ∀ i : I, ∀ j : J, FinProb (B j)) (s : Finset (I × J))
    (a : ∀ c : I × J, B c.2) :
    (FinProb.pi (fun i => FinProb.pi (P i))).pr
      (fun ω => ∀ c ∈ s, ω c.1 c.2 = a c) = ∏ c ∈ s, (P c.1 c.2).w (a c) := by
  have he : (fun ω : ∀ _i : I, ∀ j : J, B j => ∀ c ∈ s, ω c.1 c.2 = a c) =
      (fun ω => ∀ i, ∀ j ∈ Finset.univ.filter (fun j => (i, j) ∈ s), ω i j = a (i, j)) := by
    funext ω
    apply propext
    constructor
    · intro h i j hj
      exact h (i, j) (Finset.mem_filter.mp hj).2
    · intro h c hc
      exact h c.1 c.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  rw [he, pi_pr_forall (fun i => FinProb.pi (P i))
    (fun i ω => ∀ j ∈ Finset.univ.filter (fun j => (i, j) ∈ s), ω j = a (i, j))]
  simp_rw [pi_cylinder_pr]
  simp only [Finset.prod_filter]
  change (∏ i : I, ∏ j : J, (fun c : I × J =>
    if c ∈ s then (P c.1 c.2).w (a c) else 1) (i, j)) = _
  calc
    _ = ∏ c : I × J, if c ∈ s then (P c.1 c.2).w (a c) else 1 :=
      (Fintype.prod_prod_type (fun c : I × J =>
        if c ∈ s then (P c.1 c.2).w (a c) else 1)).symm
    _ = _ := Finset.prod_ite_mem_eq s (fun c => (P c.1 c.2).w (a c))

theorem pi_prod_pr_snd {B : I → Type*} [∀ i, Fintype (B i)]
    (P : ∀ i, FinProb (A i)) (Q : ∀ i, FinProb (B i)) (F : (∀ i, B i) → Prop) :
    (FinProb.pi fun i => (P i).prod (Q i)).pr (fun ω => F (fun i => (ω i).2)) =
      (FinProb.pi Q).pr F := by
  have hT : (FinProb.pi P).pr (fun _ => True) = 1 := by
    simp [FinProb.pr, FinProb.sum_eq_one]
  simpa only [true_and, hT, one_mul] using
    pi_prod_pr_and P Q (fun _ => True) F

/-- Presence can be held fixed in the lookup while activations and ties are
integrated out. Only the arrays named in the datum remain. -/
theorem raw_observation_pr {J : Type*} [Fintype J] [DecidableEq J]
    {B : J → Type*} [∀ j, Fintype (B j)]
    {C D : I → Type*} [∀ i, Fintype (C i)] [∀ i, Fintype (D i)]
    (P : ∀ i, FinProb (A i)) (Q : ∀ i, FinProb (C i)) (R : ∀ i, FinProb (D i))
    (S : ∀ i : I, ∀ j : J, FinProb (B j)) (F : (∀ i, A i) → Prop)
    (s : Finset (I × J)) (a : ∀ c : I × J, B c.2) :
    (FinProb.pi fun i => (P i).prod ((Q i).prod ((R i).prod (FinProb.pi (S i))))).pr
      (fun ω => F (fun i => (ω i).1) ∧ ∀ c ∈ s, (ω c.1).2.2.2 c.2 = a c) =
        (FinProb.pi P).pr F * ∏ c ∈ s, (S c.1 c.2).w (a c) := by
  rw [pi_prod_pr_and P (fun i => (Q i).prod ((R i).prod (FinProb.pi (S i)))) F
    (fun ω => ∀ c ∈ s, (ω c.1).2.2 c.2 = a c)]
  congr 1
  rw [pi_prod_pr_snd Q (fun i => (R i).prod (FinProb.pi (S i)))
    (fun ω => ∀ c ∈ s, (ω c.1).2 c.2 = a c)]
  rw [pi_prod_pr_snd R (fun i => FinProb.pi (S i))
    (fun ω => ∀ c ∈ s, ω c.1 c.2 = a c)]
  exact pi_nested_cylinder_pr S s a

end Product

section Completion

variable {Target Data Ω : Type*} [Fintype Target] [Fintype Data] [Fintype Ω]

namespace PresentationTable

variable (T : PresentationTable (Target := Target) (Data := Data) (Ω := Ω))

theorem ext_fields (U : PresentationTable (Target := Target) (Data := Data) (Ω := Ω))
    (hp : T.prior = U.prior) (hr : T.raw = U.raw) (ho : T.present = U.present)
    (hl : T.likelihood = U.likelihood) (hb : T.recordBound = U.recordBound) : T = U := by
  cases T
  cases U
  simp_all

theorem experiment_baseMass_factor (d : Data) (c : ℝ) (f : Target → ℝ)
    (hlik : ∀ y, T.likelihood y d = c * f y) :
    T.experiment.baseMass d = c * ∑ y, T.prior.w y * f y := by
  unfold SelectionExperiment5.baseMass
  change (∑ y, T.prior.w y * T.likelihood y d) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [hlik y]
  ring

theorem selectedMass_zero_of_baseMass_zero (d : Data) (hd : T.experiment.baseMass d = 0) :
    T.experiment.selectedMass d = 0 := by
  apply le_antisymm
  · calc
      T.experiment.selectedMass d ≤ T.experiment.baseMass d := by
        unfold SelectionExperiment5.selectedMass SelectionExperiment5.baseMass
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_of_le_one_right
          (mul_nonneg (T.prior.nonneg y) (T.likelihood_nonneg y d))
          (T.selection_le_one y d)
      _ = 0 := hd
  · exact Lane_sol_s05_centres.selection_selectedMass_nonneg _ _

/-- Values at null conditioning data may be filled by the base posterior.
They have zero weight in the short presentation identity. -/
def completedProxy (ε : ℝ) (source : Data → Target → ℝ) (d : Data) (x : Target) : ℝ :=
  if T.experiment.baseMass d = 0 then source d x else T.experiment.proxyRow ε d x

def completedRow (ε : ℝ) (source : Data → Target → ℝ) (obs : Option Data) (x : Target) : ℝ :=
  match obs with
  | none => 0
  | some d => T.completedProxy ε source d x

theorem completedProxy_source_congr (ε : ℝ) (source source' : Data → Target → ℝ)
    (d : Data) (x : Target) (h : source d x = source' d x) :
    T.completedProxy ε source d x = T.completedProxy ε source' d x := by
  unfold completedProxy
  rw [h]

theorem completedProxy_le_source (ε : ℝ) (source : Data → Target → ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (d : Data)
    (hs : ∀ x, 0 ≤ source d x)
    (hbase : T.experiment.baseMass d ≠ 0 → ∀ x, T.experiment.baseRow d x = source d x)
    (x : Target) : T.completedProxy ε source d x ≤ ε⁻¹ * source d x := by
  unfold completedProxy
  split_ifs with hz
  · exact le_mul_of_one_le_left (hs x) ((one_le_inv₀ hε).2 hε1)
  · simpa only [hbase hz x] using L5_1k_row_comparison T.experiment ε hε hε1 d x

theorem completedProxy_sum (ε : ℝ) (source : Data → Target → ℝ) (hε : 0 < ε)
    (d : Data) (hs : ∑ x, source d x = 1) : ∑ x, T.completedProxy ε source d x = 1 := by
  by_cases hz : T.experiment.baseMass d = 0
  · simpa only [completedProxy, hz, ite_true] using hs
  · have hm : 0 < T.experiment.baseMass d := lt_of_le_of_ne
      (Lane_sol_s05_centres.selection_baseMass_nonneg _ _) (Ne.symm hz)
    simpa only [completedProxy, hz, ite_false] using
      Lane_sol_s05_centres.selection_proxy_sum T.experiment ε hε d hm

theorem completedRow_nonneg (ε : ℝ) (source : Data → Target → ℝ)
    (hs : ∀ d x, 0 ≤ source d x) (obs : Option Data) (x : Target) :
    0 ≤ T.completedRow ε source obs x := by
  cases obs with
  | none => exact le_rfl
  | some d =>
    change 0 ≤ T.completedProxy ε source d x
    unfold completedProxy
    split_ifs
    · exact hs d x
    · exact Lane_sol_s05_centres.selection_proxy_nonneg _ _ _ _

theorem completedRow_sum (ε : ℝ) (source : Data → Target → ℝ)
    (obs : Option Data) (x : Target) (w : ℝ) :
    w * T.completedRow ε source obs x =
      ∑ d, (if obs = some d then w else 0) * T.completedProxy ε source d x := by
  cases obs with
  | none => simp [completedRow]
  | some d => simp [completedRow]

theorem expect_completedRow (ε : ℝ) (source : Data → Target → ℝ) (y x : Target) :
    (T.raw y).expect (fun ω => T.completedRow ε source (T.present y ω) x) =
      ∑ d, presentationMass T.raw T.present y d * T.completedProxy ε source d x := by
  unfold FinProb.expect presentationMass FinProb.pr
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ d, (if T.present y ω = some d then (T.raw y).w ω else 0) *
        T.completedProxy ε source d x :=
      T.completedRow_sum ε source (T.present y ω) x ((T.raw y).w ω)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : T.present y ω = some d <;> simp only [hd, ite_true, ite_false]

theorem short_mean_completed (ε : ℝ) (source : Data → Target → ℝ) (x : Target) :
    ∑ y, T.prior.w y * (T.raw y).expect (fun ω => T.completedRow ε source (T.present y ω) x) =
      ∑ d, T.experiment.selectedMass d * T.experiment.proxyRow ε d x := by
  simp_rw [T.expect_completedRow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have he : (∑ y, T.prior.w y * (presentationMass T.raw T.present y d * T.completedProxy ε source d x)) =
      T.experiment.selectedMass d * T.completedProxy ε source d x := by
    rw [T.experiment_selectedMass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he]
  unfold completedProxy
  split_ifs with hz
  · rw [T.selectedMass_zero_of_baseMass_zero d hz]
    simp
  · rfl

theorem short_mean_completed_scaled (ε c : ℝ) (source : Data → Target → ℝ) (x : Target) :
    ∑ y, T.prior.w y * (T.raw y).expect
      (fun ω => c * T.completedRow ε source (T.present y ω) x) =
        c * ∑ d, T.experiment.selectedMass d * T.experiment.proxyRow ε d x := by
  have hscale (y : Target) : (T.raw y).expect
      (fun ω => c * T.completedRow ε source (T.present y ω) x) =
        c * (T.raw y).expect (fun ω => T.completedRow ε source (T.present y ω) x) := by
    unfold FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  simp_rw [hscale]
  rw [← T.short_mean_completed ε source x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem short_mean_external (ε c : ℝ) (source : Data → Target → ℝ)
    (prior : FinProb Target) (raw : Target → FinProb Ω) (rows : Target → Ω → Target → ℝ)
    (hp : T.prior = prior) (hr : ∀ y, T.raw y = raw y)
    (ho : ∀ y ω x, rows y ω x = T.completedRow ε source (T.present y ω) x) (x : Target) :
    (∑ y, prior.w y * (raw y).expect (fun ω => c * rows y ω x)) =
      c * ∑ d, T.experiment.selectedMass d * T.experiment.proxyRow ε d x := by
  rw [← T.short_mean_completed_scaled ε c source x]
  apply Finset.sum_congr rfl
  intro y _
  rw [hp, hr y]
  congr 1
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro ω _
  change (raw y).w ω * (c * rows y ω x) =
    (raw y).w ω * (c * T.completedRow ε source (T.present y ω) x)
  rw [ho y ω x]

end PresentationTable

end Completion

section Observations

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) {Id : Type} [DecidableEq Id]

def datumIf [Fintype Id] (r : X.RecordOn Id) (a : X.ArraysOn Id) (v : Prop) :
    Option (ObservationDatum X (Id := Id)) := if v then some (observationDatum X r a) else none

theorem observationPresentation_datumIf [Fintype Id] {Target Ω : Type*}
    (record : Target → Ω → X.RecordOn Id) (arrays : Target → Ω → X.ArraysOn Id)
    (valid : Target → Ω → Prop) (x : Target) (ω : Ω) :
    observationPresentation X record arrays valid x ω = datumIf X (record x ω) (arrays x ω) (valid x ω) := rfl

def neighborPool {d h : ℕ} (site : EvenRole5 n → CubeVertex d) (y : OddRole5 n)
    (rad : ℕ) (P : CubeVertex d × Fin (h + 1) → Bool) :
    Finset (CubeVertex d × Fin (h + 1)) :=
  (Setup5.evenNbrs y).biUnion (fun a => Finset.univ.filter (fun l =>
    P l = true ∧ _root_.hammingDist l.1 (site a) ≤ rad))

theorem low_column_sum (ℓ : X.Key) (hl : ℓ.isLeft)
    (f : (Fin (colLen5 (X.p.s n) ℓ) → Fin N) → ℝ) :
    (∑ θ, f θ) = ∑ x, f (fun _ => x) := by
  cases ℓ with
  | inl k =>
    change (∑ θ : Fin 1 → Fin N, f θ) = ∑ x, f (fun _ => x)
    exact (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin N)).symm f).symm
  | inr k => simp at hl

theorem low_step3Mass_sum (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hl : r.1.isLeft) :
    X.step3MassOn H r a none = ∑ x,
      (X.prior H.1 r.1).w x * (if X.candGateOn H r a (fun _ => x) then 1 else 0) *
        X.obsLikOn H r a (fun _ => x) none := by
  unfold Setup5.step3MassOn
  rw [low_column_sum X r.1 hl]
  apply Finset.sum_congr rfl
  intro x _
  simp only [low_key_length X r.1 hl, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]

theorem low_step3Post_sum (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hl : r.1.isLeft) (hm : X.step3MassOn H r a none ≠ 0) :
    (∑ x, X.step3PostOn H r a none (fun _ => x)) = 1 := by
  unfold Setup5.step3PostOn
  simp only [low_key_length X r.1 hl, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  rw [← Finset.sum_div, ← low_step3Mass_sum X H r a hl]
  exact div_self hm

theorem low_step3Post_withCol (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (x : Fin N) :
    X.step3PostOn (X.withCol H r.1 θ) r a none (fun _ => x) =
      X.step3PostOn H r a none (fun _ => x) := by
  simp only [Setup5.step3PostOn,
    Lane_sol_s05_hist1b.candGateOn_withCol, Lane_sol_s05_hist1b.obsLikOn_withCol,
    Lane_sol_s05_hist1b.step3MassOn_withCol]
  rfl

def abstractRecordBudget (C : ℝ) (y : OddRole5 n) : ℝ :=
  Real.exp (C * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
    (((X.g.roleKey (X.p.J n) y.1).level : ℝ) + 1) * Real.log (X.p.m n) +
    (if (X.g.roleKey (X.p.J n) y.1).isLeft ∧
        (X.g.roleKey (X.p.J n) y.1).level = X.p.J n then
      (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0)))

def lookupBudget (C B : ℝ) (y : OddRole5 n) : ℝ :=
  if X.g.low (X.p.J n) y.1 then abstractRecordBudget X C y * (B + 1) ^ X.p.T n else 0

def prospectiveRecords [Fintype Id] (y : OddRole5 n) (pool : Finset Id) (B : ℝ) :
    Finset (X.RecordOn Id) :=
  if X.g.low (X.p.J n) y.1 ∧ (pool.card : ℝ) ≤ B then potentialRecords X y pool else ∅

theorem prospectiveRecords_card_le [Fintype Id] (C B : ℝ) (y : OddRole5 n)
    (pool : Finset Id) (fallback : Id) (hB : 0 ≤ B) (hT : 0 < X.p.T n)
    (hcount : X.RecordCount C) :
    ((prospectiveRecords X y pool B).card : ℝ) ≤ lookupBudget X C B y := by
  by_cases hg : X.g.low (X.p.J n) y.1 ∧ (pool.card : ℝ) ≤ B
  · rw [prospectiveRecords, if_pos hg, lookupBudget, if_pos hg.1]
    calc
      _ ≤ abstractRecordBudget X C y * (pool.card + 1 : ℕ) ^ X.p.T n :=
        potentialRecords_budget X C hcount y pool fallback hT
      _ ≤ abstractRecordBudget X C y * (B + 1) ^ X.p.T n := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith [hg.2]
  · rw [prospectiveRecords, if_neg hg]
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold lookupBudget
    split_ifs
    · exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg (by linarith) _)
    · exact le_rfl

theorem prospectiveRecords_mem_from [Fintype Id] (y : OddRole5 n) (pool : Finset Id)
    (B : ℝ) (r : X.RecordOn Id) (hr : r ∈ prospectiveRecords X y pool B) :
    ∃ μ, X.RecordFrom r y μ := by
  unfold prospectiveRecords at hr
  split_ifs at hr with hg
  · exact (Finset.mem_filter.mp hr).2.1
  · simp at hr

theorem prospectiveRecords_mem_key [Fintype Id] (y : OddRole5 n) (pool : Finset Id)
    (B : ℝ) (r : X.RecordOn Id) (hr : r ∈ prospectiveRecords X y pool B) :
    r.1 = X.g.roleKey (X.p.J n) y.1 := by
  obtain ⟨μ, hμ⟩ := prospectiveRecords_mem_from X y pool B r hr
  exact hμ.1.symm

theorem observationCover_mem_iff [Fintype Id] (rs : Finset (X.RecordOn Id))
    (a : X.ArraysOn Id) (gate : ObservationDatum X (Id := Id) → Prop)
    (d : ObservationDatum X (Id := Id)) :
    d ∈ observationCover X rs a (fun r => gate (observationDatum X r a)) ↔
      d.1 ∈ rs ∧ gate d ∧ ∀ c ∈ d.1.2.1, a c = observationArrays X d c := by
  constructor
  · intro hd
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hd
    have hrd : r = d.1 := congrArg Sigma.fst he
    subst r
    obtain ⟨hmem, hg⟩ := Finset.mem_filter.mp hr
    refine ⟨hmem, he ▸ hg, ?_⟩
    have heq : observationDatum X d.1 a = observationDatum X d.1 (observationArrays X d) :=
      he.trans (observationDatum_reconstruct X d).symm
    exact (observationDatum_eq_iff X _ _ _).mp heq
  · rintro ⟨hmem, hg, ha⟩
    have he : observationDatum X d.1 a = d :=
      ((observationDatum_eq_iff X _ _ _).mpr ha).trans (observationDatum_reconstruct X d)
    apply Finset.mem_image.mpr
    exact ⟨d.1, Finset.mem_filter.mpr ⟨hmem, he.symm ▸ hg⟩, he⟩

/-- The target-deleted reference law includes every observed array; arrays of
types that do not list the target retain their original law. -/
def observationReferenceMass (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id) : ℝ :=
  ∏ c ∈ r.2.1, ∏ i : Fin (X.p.typeBlocks n c.2),
    if r.1 ∈ c.2.2.1 then (X.blockLawDel H c.2 r.1).w (a c i)
    else (X.blockLaw H c.2).w (a c i)

theorem observationReferenceMass_nonneg (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) : 0 ≤ observationReferenceMass X H r a := by
  apply Finset.prod_nonneg
  intro c _
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> exact FinProb.nonneg _ _

theorem observationReferenceMass_withCol (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    observationReferenceMass X (X.withCol H r.1 θ) r a = observationReferenceMass X H r a := by
  unfold observationReferenceMass
  apply Finset.prod_congr rfl
  intro c _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hm : r.1 ∈ c.2.2.1
  · simp only [hm, ite_true, Lane_sol_s05_hist1b.blockLawDel_withCol]
  · have he := Lane_sol_s05_hist1b.blockLawOn_withCol_eq_of_not_mem X H c.2 c.2.2.1 r.1 θ hm
    simp only [hm, ite_false, show X.blockLaw (X.withCol H r.1 θ) c.2 = X.blockLaw H c.2 from he]

theorem observation_law_recompose (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (hg : X.candGateOn H r a θ) :
    (∏ c ∈ r.2.1, (FinProb.pi fun _ : Fin (X.p.typeBlocks n c.2) =>
      X.blockLaw (X.withCol H r.1 θ) c.2).w (a c)) =
        observationReferenceMass X H r a * X.obsLikOn H r a θ none := by
  have hnone (c : Id × X.Ty) (i : Fin (X.p.typeBlocks n c.2)) :
      ¬ X.InRef (none : Option (Id × X.Ty × Finset (Fin X.blockBound))) c i := by
    simp [Setup5.InRef]
  unfold observationReferenceMass Setup5.obsLikOn
  simp only [hnone, ite_false, FinProb.pi]
  rw [Finset.prod_filter]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c hc
  by_cases hm : r.1 ∈ c.2.2.1
  · rw [if_pos hm, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [hm, ite_true]
    exact Lane_sol_s05_hist1b.blockLaw_candidate_recompose X H c.2 r.1 θ hm
      (hg.1 c hc hm).1 (hg.1 c hc hm).2 (a c i)
  · simp only [hm, ite_false, mul_one]
    have he : X.blockLaw (X.withCol H r.1 θ) c.2 = X.blockLaw H c.2 :=
      Lane_sol_s05_hist1b.blockLawOn_withCol_eq_of_not_mem X H c.2 c.2.2.1 r.1 θ hm
    simp only [he]

theorem observation_gated_law_recompose (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    (if X.candGateOn H r a θ then
      ∏ c ∈ r.2.1, (FinProb.pi fun _ : Fin (X.p.typeBlocks n c.2) =>
        X.blockLaw (X.withCol H r.1 θ) c.2).w (a c) else 0) =
      observationReferenceMass X H r a *
        ((if X.candGateOn H r a θ then 1 else 0) * X.obsLikOn H r a θ none) := by
  by_cases hg : X.candGateOn H r a θ
  · simp only [hg, ite_true, one_mul, observation_law_recompose X H r a θ hg]
  · simp only [hg, ite_false, zero_mul, mul_zero]

theorem candGateOn_arrays_congr (H : X.KeyHist) (r : X.RecordOn Id) (a b : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c) (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.candGateOn H r a θ ↔ X.candGateOn H r b θ := by
  unfold Setup5.candGateOn
  apply and_congr Iff.rfl
  apply forall_congr'
  intro c
  apply forall_congr'
  intro M
  by_cases hm : r.2.2.2 = some (c.1, c.2, M)
  · simp only [hm, true_implies]
    have he : X.hitSet a c = X.hitSet b c := by
      funext x
      simp only [Setup5.hitSet, hab c (hmask c M hm)]
    rw [he]
  · simp only [hm, false_implies]

end Observations

end
end HypercubeRamsey.Lane_sol_s05_k1
