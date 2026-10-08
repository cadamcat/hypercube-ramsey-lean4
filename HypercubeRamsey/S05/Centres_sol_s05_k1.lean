import HypercubeRamsey.S05.Centres_sol_s05_centres_low

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical
open scoped BigOperators

set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

noncomputable section

variable {Target Data Ω : Type*} [Fintype Target] [Fintype Data] [Fintype Ω]

/-- A presentation has one datum, or no datum on invalidity. The law is generated
at the candidate target value, including every unrecorded variable. -/
def presentationMass (raw : Target → FinProb Ω) (present : Target → Ω → Option Data)
    (y : Target) (d : Data) : ℝ :=
  (raw y).pr fun ω => present y ω = some d

theorem presentationMass_nonneg (raw : Target → FinProb Ω)
    (present : Target → Ω → Option Data) (y : Target) (d : Data) :
    0 ≤ presentationMass raw present y d := by
  unfold presentationMass FinProb.pr
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact (raw y).nonneg ω
  · exact le_rfl

theorem presentationMass_sum_le_one (raw : Target → FinProb Ω)
    (present : Target → Ω → Option Data) (y : Target) :
    ∑ d, presentationMass raw present y d ≤ 1 := by
  unfold presentationMass FinProb.pr
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ ω, (raw y).w ω := by
      apply Finset.sum_le_sum
      intro ω _
      cases he : present y ω with
      | none => simp [he, (raw y).nonneg ω]
      | some d => simp [he]
    _ = 1 := (raw y).sum_eq_one

/-- The finite form of the paper's `F_y(o) a_y(o)` factorization. The
likelihood includes the reference-observation and fixed-input weights. -/
structure PresentationTable where
  prior : FinProb Target
  raw : Target → FinProb Ω
  present : Target → Ω → Option Data
  likelihood : Target → Data → ℝ
  likelihood_nonneg : ∀ y d, 0 ≤ likelihood y d
  mass_le_likelihood : ∀ y d, presentationMass raw present y d ≤ likelihood y d
  recordBound : ℝ
  likelihood_mass : ∀ y, ∑ d, likelihood y d ≤ recordBound

/-- Before applying selection, list the gated records compatible with the
fixed presence and their actual observed arrays. Several records can occur in
this cover, whereas a valid selection presents exactly one datum. -/
def coverLikelihood (raw : Target → FinProb Ω) (cover : Target → Ω → Finset Data)
    (y : Target) (d : Data) : ℝ :=
  (raw y).pr fun ω => d ∈ cover y ω

theorem coverLikelihood_nonneg (raw : Target → FinProb Ω)
    (cover : Target → Ω → Finset Data) (y : Target) (d : Data) :
    0 ≤ coverLikelihood raw cover y d := by
  unfold coverLikelihood FinProb.pr
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact (raw y).nonneg ω
  · exact le_rfl

theorem presentationMass_le_coverLikelihood (raw : Target → FinProb Ω)
    (present : Target → Ω → Option Data) (cover : Target → Ω → Finset Data)
    (hcover : ∀ y ω d, present y ω = some d → d ∈ cover y ω) (y : Target) (d : Data) :
    presentationMass raw present y d ≤ coverLikelihood raw cover y d := by
  unfold presentationMass coverLikelihood FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : present y ω = some d
  · simp [hp, hcover y ω d hp]
  · simp only [if_neg hp]
    split_ifs
    · exact (raw y).nonneg ω
    · exact le_rfl

theorem coverLikelihood_mass (raw : Target → FinProb Ω)
    (cover : Target → Ω → Finset Data) (y : Target) :
    ∑ d, coverLikelihood raw cover y d =
      (raw y).expect (fun ω => ((cover y ω).card : ℝ)) := by
  unfold coverLikelihood FinProb.pr FinProb.expect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ d, if d ∈ cover y ω then (raw y).w ω else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d ∈ cover y ω <;> simp only [hd, ite_true, ite_false]
    _ = _ := by simp [Finset.sum_ite_mem_eq, mul_comm]

theorem coverLikelihood_mass_le (raw : Target → FinProb Ω)
    (cover : Target → Ω → Finset Data) (B : ℝ)
    (hcard : ∀ y ω, ((cover y ω).card : ℝ) ≤ B) (y : Target) :
    ∑ d, coverLikelihood raw cover y d ≤ B := by
  rw [coverLikelihood_mass]
  calc
    _ ≤ (raw y).expect (fun _ => B) :=
      FinProb.expect_mono _ fun ω => hcard y ω
    _ = B := FinProb.expect_const _ _

/-- A table constructor using raw probabilities directly. The subsequent
Bayes calculation can identify this likelihood with its reference density. -/
def tableOfCover (prior : FinProb Target) (raw : Target → FinProb Ω)
    (present : Target → Ω → Option Data) (cover : Target → Ω → Finset Data) (B : ℝ)
    (hcover : ∀ y ω d, present y ω = some d → d ∈ cover y ω)
    (hcard : ∀ y ω, ((cover y ω).card : ℝ) ≤ B) :
    PresentationTable (Target := Target) (Data := Data) (Ω := Ω) where
  prior := prior
  raw := raw
  present := present
  likelihood := coverLikelihood raw cover
  likelihood_nonneg := coverLikelihood_nonneg raw cover
  mass_le_likelihood := presentationMass_le_coverLikelihood raw present cover hcover
  recordBound := B
  likelihood_mass := coverLikelihood_mass_le raw cover B hcard

namespace PresentationTable

variable (T : PresentationTable (Target := Target) (Data := Data) (Ω := Ω))

def selection (y : Target) (d : Data) : ℝ :=
  presentationMass T.raw T.present y d / T.likelihood y d

theorem selection_nonneg (y : Target) (d : Data) : 0 ≤ T.selection y d :=
  div_nonneg (presentationMass_nonneg _ _ _ _) (T.likelihood_nonneg y d)

theorem selection_le_one (y : Target) (d : Data) : T.selection y d ≤ 1 := by
  by_cases hq : T.likelihood y d = 0
  · simp [selection, hq]
  · exact (div_le_one (lt_of_le_of_ne (T.likelihood_nonneg y d) (Ne.symm hq))).2
      (T.mass_le_likelihood y d)

theorem likelihood_mul_selection (y : Target) (d : Data) :
    T.likelihood y d * T.selection y d = presentationMass T.raw T.present y d := by
  by_cases hq : T.likelihood y d = 0
  · have hp : presentationMass T.raw T.present y d = 0 :=
      le_antisymm (hq ▸ T.mass_le_likelihood y d) (presentationMass_nonneg _ _ _ _)
    simp [hq, hp]
  · unfold selection
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hq]

def experiment : SelectionExperiment5 Target Data where
  prior := T.prior
  likelihood := T.likelihood
  selection := T.selection
  likelihood_nonneg := T.likelihood_nonneg
  selection_nonneg := T.selection_nonneg
  selection_le_one := T.selection_le_one
  recordBound := T.recordBound
  likelihood_mass := T.likelihood_mass
  gated_subprob y := by
    simpa only [T.likelihood_mul_selection] using presentationMass_sum_le_one T.raw T.present y

theorem experiment_selectedMass (d : Data) :
    T.experiment.selectedMass d =
      ∑ y, T.prior.w y * presentationMass T.raw T.present y d := by
  unfold SelectionExperiment5.selectedMass
  apply Finset.sum_congr rfl
  intro y _
  change T.prior.w y * T.likelihood y d * T.selection y d = _
  rw [mul_assoc, T.likelihood_mul_selection]

theorem experiment_baseRow (d : Data) (y : Target) :
    T.experiment.baseRow d y =
      T.prior.w y * T.likelihood y d / ∑ z, T.prior.w z * T.likelihood z d := by
  change (if T.experiment.baseMass d = 0 then 0 else
    T.prior.w y * T.likelihood y d / T.experiment.baseMass d) = _
  by_cases hm : T.experiment.baseMass d = 0
  · change (if T.experiment.baseMass d = 0 then 0 else _) =
      T.prior.w y * T.likelihood y d / T.experiment.baseMass d
    simp [hm]
  · rw [if_neg hm]
    rfl

/-- Reference-array and position weights common to all candidates cancel
from the unadjusted posterior. -/
theorem experiment_baseRow_factor (d : Data) (c : ℝ) (f : Target → ℝ)
    (hc : c ≠ 0) (hlik : ∀ y, T.likelihood y d = c * f y) (y : Target) :
    T.experiment.baseRow d y = T.prior.w y * f y / ∑ z, T.prior.w z * f z := by
  rw [T.experiment_baseRow]
  have hmass : (∑ z, T.prior.w z * T.likelihood z d) = c * ∑ z, T.prior.w z * f z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [hlik z]
    ring
  rw [hmass, hlik y, show T.prior.w y * (c * f y) = c * (T.prior.w y * f y) by ring]
  exact mul_div_mul_left _ _ hc

/-- The same table may be consulted at any height truncation. -/
def row (ε : ℝ) (obs : Option Data) (x : Target) : ℝ :=
  match obs with
  | none => 0
  | some d => T.experiment.proxyRow ε d x

theorem row_nonneg (ε : ℝ) (obs : Option Data) (x : Target) : 0 ≤ T.row ε obs x := by
  cases obs with
  | none => exact le_rfl
  | some d => exact Lane_sol_s05_centres.selection_proxy_nonneg _ _ _ _

theorem row_sum (ε : ℝ) (obs : Option Data) (x : Target) (w : ℝ) :
    w * T.row ε obs x =
      ∑ d, (if obs = some d then w else 0) * T.experiment.proxyRow ε d x := by
  cases obs with
  | none => simp [row]
  | some d => simp [row]

theorem expect_row (ε : ℝ) (y x : Target) :
    (T.raw y).expect (fun ω => T.row ε (T.present y ω) x) =
      ∑ d, presentationMass T.raw T.present y d * T.experiment.proxyRow ε d x := by
  unfold FinProb.expect presentationMass FinProb.pr
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ d, (if T.present y ω = some d then (T.raw y).w ω else 0) *
        T.experiment.proxyRow ε d x := T.row_sum ε (T.present y ω) x ((T.raw y).w ω)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : T.present y ω = some d <;> simp only [hd, ite_true, ite_false]

/-- Disintegration of the target-averaged proxy mean. -/
theorem short_mean (ε : ℝ) (x : Target) :
    ∑ y, T.prior.w y * (T.raw y).expect (fun ω => T.row ε (T.present y ω) x) =
      ∑ d, T.experiment.selectedMass d * T.experiment.proxyRow ε d x := by
  simp_rw [T.expect_row, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [T.experiment_selectedMass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem short_mean_scaled (ε c : ℝ) (x : Target) :
    ∑ y, T.prior.w y * (T.raw y).expect (fun ω => c * T.row ε (T.present y ω) x) =
      c * ∑ d, T.experiment.selectedMass d * T.experiment.proxyRow ε d x := by
  have hexp (y : Target) :
      (T.raw y).expect (fun ω => c * T.row ε (T.present y ω) x) =
        c * (T.raw y).expect (fun ω => T.row ε (T.present y ω) x) := by
    unfold FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  simp_rw [hexp]
  rw [← T.short_mean ε x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

end PresentationTable

section Observations

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) {Id : Type} [Fintype Id]

/-- Unrecorded arrays are absent from the datum. This avoids multiplying the
record-count budget by the number of arbitrary completions of an observation. -/
abbrev ObservationDatum :=
  Σ r : X.RecordOn Id, ∀ c : {c : Id × X.Ty // c ∈ r.2.1}, X.Array c.1.2

noncomputable instance observationDatumFintype : Fintype (ObservationDatum X (Id := Id)) :=
  inferInstanceAs (Fintype (Σ r : X.RecordOn Id,
    ∀ c : {c : Id × X.Ty // c ∈ r.2.1}, X.Array c.1.2))

def observationDatum (r : X.RecordOn Id) (a : X.ArraysOn Id) : ObservationDatum X (Id := Id) :=
  ⟨r, fun c => a c.1⟩

def observationArrays (d : ObservationDatum X (Id := Id)) : X.ArraysOn Id :=
  fun c => if hc : c ∈ d.1.2.1 then d.2 ⟨c, hc⟩ else fun _ => X.fallbackBlock c.2

theorem observationArrays_eq (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty) (hc : c ∈ r.2.1) :
    observationArrays X (observationDatum X r a) c = a c := by
  simp [observationArrays, observationDatum, hc]

theorem observationDatum_eq_iff (r : X.RecordOn Id) (a b : X.ArraysOn Id) :
    observationDatum X r a = observationDatum X r b ↔ ∀ c ∈ r.2.1, a c = b c := by
  constructor
  · intro h c hc
    have he := congrArg (fun d : ObservationDatum X (Id := Id) => observationArrays X d c) h
    simpa only [observationArrays_eq X r a c hc, observationArrays_eq X r b c hc] using he
  · intro hab
    have he : (fun c : {c : Id × X.Ty // c ∈ r.2.1} => a c.1) =
        (fun c : {c : Id × X.Ty // c ∈ r.2.1} => b c.1) :=
      funext fun c => hab c.1 c.2
    exact congrArg (Sigma.mk r) he

theorem observationDatum_reconstruct (d : ObservationDatum X (Id := Id)) :
    observationDatum X d.1 (observationArrays X d) = d := by
  rcases d with ⟨r, a⟩
  apply congrArg (Sigma.mk r)
  funext c
  simp [observationArrays]

theorem observationDatum_record_eq_iff (r s : X.RecordOn Id) (a b : X.ArraysOn Id) :
    observationDatum X r a = observationDatum X s b ↔ r = s ∧ ∀ c ∈ r.2.1, a c = b c := by
  constructor
  · intro h
    have hrs : r = s := congrArg Sigma.fst h
    subst s
    exact ⟨rfl, (observationDatum_eq_iff X r a b).mp h⟩
  · rintro ⟨rfl, hab⟩
    exact (observationDatum_eq_iff X _ a b).mpr hab

/-- Each candidate record contributes one observed datum to the cover. -/
def observationCover (rs : Finset (X.RecordOn Id)) (a : X.ArraysOn Id)
    (gate : X.RecordOn Id → Prop) : Finset (ObservationDatum X (Id := Id)) :=
  (rs.filter gate).image fun r => observationDatum X r a

theorem observationCover_card_le (rs : Finset (X.RecordOn Id)) (a : X.ArraysOn Id)
    (gate : X.RecordOn Id → Prop) :
    (observationCover X rs a gate).card ≤ rs.card :=
  (Finset.card_image_le).trans (Finset.card_filter_le _ _)

theorem observationDatum_mem_cover (rs : Finset (X.RecordOn Id)) (a : X.ArraysOn Id)
    (gate : X.RecordOn Id → Prop) (r : X.RecordOn Id) (hr : r ∈ rs) (hg : gate r) :
    observationDatum X r a ∈ observationCover X rs a gate :=
  Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hg⟩, rfl⟩

variable (record : Target → Ω → X.RecordOn Id) (arrays : Target → Ω → X.ArraysOn Id)
variable (valid : Target → Ω → Prop)

def observationPresentation (y : Target) (ω : Ω) : Option (ObservationDatum X (Id := Id)) :=
  if valid y ω then some (observationDatum X (record y ω) (arrays y ω)) else none

theorem observationPresentation_eq_some (y : Target) (ω : Ω)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) :
    observationPresentation X record arrays valid y ω = some (observationDatum X r a) ↔
      valid y ω ∧ record y ω = r ∧ ∀ c ∈ r.2.1, arrays y ω c = a c := by
  unfold observationPresentation
  split_ifs with hv
  · constructor
    · intro h
      have he := Option.some.inj h
      obtain ⟨hr, hab⟩ := (observationDatum_record_eq_iff X _ _ _ _).mp he
      exact ⟨hv, hr, hr ▸ hab⟩
    · rintro ⟨_, hr, hab⟩
      apply congrArg some
      exact (observationDatum_record_eq_iff X _ _ _ _).mpr ⟨hr, hr.symm ▸ hab⟩
  · simp [hv]

theorem observationPresentation_mass (raw : Target → FinProb Ω) (y : Target)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) :
    presentationMass raw (observationPresentation X record arrays valid) y (observationDatum X r a) =
      (raw y).pr (fun ω => valid y ω ∧ record y ω = r ∧ ∀ c ∈ r.2.1, arrays y ω c = a c) := by
  unfold presentationMass
  congr 1
  funext ω
  exact propext (observationPresentation_eq_some X record arrays valid y ω r a)

/-- The low selection table, once its position gate supplies the record count
and its validity tests imply the candidate gate. -/
def observationTable (prior : FinProb Target) (raw : Target → FinProb Ω)
    (records : Target → Ω → Finset (X.RecordOn Id))
    (gate : Target → Ω → X.RecordOn Id → Prop) (B : ℝ)
    (hrecord : ∀ y ω, valid y ω → record y ω ∈ records y ω)
    (hgate : ∀ y ω, valid y ω → gate y ω (record y ω))
    (hcard : ∀ y ω, ((records y ω).card : ℝ) ≤ B) :
    PresentationTable (Target := Target) (Data := ObservationDatum X (Id := Id)) (Ω := Ω) :=
  tableOfCover prior raw (observationPresentation X record arrays valid)
    (fun y ω => observationCover X (records y ω) (arrays y ω) (gate y ω)) B
    (by
      intro y ω d hd
      by_cases hv : valid y ω
      · have he : observationDatum X (record y ω) (arrays y ω) = d := by
          simpa only [observationPresentation, if_pos hv, Option.some.injEq] using hd
        rw [← he]
        exact observationDatum_mem_cover X _ _ _ _ (hrecord y ω hv) (hgate y ω hv)
      · simp [observationPresentation, hv] at hd)
    (fun y ω => (Nat.cast_le.mpr (observationCover_card_le X _ _ _)).trans (hcard y ω))

end Observations

end
end HypercubeRamsey.Lane_sol_s05_k1
