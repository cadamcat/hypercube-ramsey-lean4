import HypercubeRamsey.S05.Even_refs_sol_s05_even
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

def resampleCoords {I : Type*} [DecidableEq I] {Ω : I → Type*} (S : Finset I)
    (ω : ∀ i, Ω i) (z : ∀ i : S, Ω i.1) : ∀ i, Ω i :=
  fun i => if h : i ∈ S then z ⟨i, h⟩ else ω i

theorem pi_weight_split {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (S : Finset I) (ω : ∀ i, Ω i) :
    (FinProb.pi P).w ω =
      (FinProb.pi (fun i : S => P i.1)).w (fun i => ω i.1) *
      (FinProb.pi (fun i : {i : I // i ∉ S} => P i.1)).w (fun i => ω i.1) := by
  let f : I → ℝ := fun i => (P i).w (ω i)
  have hs : (∏ i : S, f i.1) = ∏ i ∈ S, f i := by
    rw [Finset.univ_eq_attach]
    exact Finset.prod_attach S f
  let T := Finset.univ.filter fun i : I => i ∉ S
  let e : {i : I // i ∉ S} ≃ T := {
    toFun i := ⟨i.1, by simp [T, i.2]⟩
    invFun i := ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv i := by apply Subtype.ext; rfl
    right_inv i := by apply Subtype.ext; rfl }
  have hc : (∏ i : {i : I // i ∉ S}, f i.1) = ∏ i ∈ Finset.univ with i ∉ S, f i := by
    calc
      _ = ∏ i : T, f i.1 := Fintype.prod_equiv e _ _ (fun _ => rfl)
      _ = ∏ i ∈ T, f i := by rw [Finset.univ_eq_attach]; exact Finset.prod_attach T f
      _ = _ := rfl
  change (∏ i, f i) = (∏ i : S, f i.1) * (∏ i : {i : I // i ∉ S}, f i.1)
  rw [hs, hc]
  simpa using (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : I => i ∈ S) f).symm

theorem pi_expect_split {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (S : Finset I) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ b : (∀ i : {i : I // i ∉ S}, Ω i.1),
        (FinProb.pi (fun i : {i : I // i ∉ S} => P i.1)).w b *
          ∑ a : (∀ i : S, Ω i.1), (FinProb.pi (fun i : S => P i.1)).w a *
            f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω).symm (a, b)) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω
  unfold FinProb.expect
  rw [← Equiv.sum_comp e.symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [pi_weight_split P S]
  have ha : (fun i : S => e.symm (a, b) i.1) = a := by
    funext i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hb : (fun i : {i : I // i ∉ S} => e.symm (a, b) i.1) = b := by
    funext i
    simp [e, Equiv.piEquivPiSubtypeProd, i.2]
  rw [ha, hb]
  ring

theorem resampleCoords_split {I : Type*} [DecidableEq I] {Ω : I → Type*}
    (S : Finset I) (a z : ∀ i : S, Ω i.1) (b : ∀ i : {i : I // i ∉ S}, Ω i.1) :
    resampleCoords S ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω).symm (a, b)) z =
      (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω).symm (z, b) := by
  funext i
  by_cases hi : i ∈ S <;> simp [resampleCoords, Equiv.piEquivPiSubtypeProd, hi]

theorem pi_expect_resample {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (S : Finset I) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect (fun ω =>
      (FinProb.pi (fun i : S => P i.1)).expect (fun z => f (resampleCoords S ω z))) =
      (FinProb.pi P).expect f := by
  rw [pi_expect_split P S, pi_expect_split P S]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  simp only [FinProb.expect, resampleCoords_split]
  rw [← Finset.sum_mul, (FinProb.pi (fun i : S => P i.1)).sum_eq_one, one_mul]

theorem pi_expect_update {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (i : I) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect (fun ω => (P i).expect (fun z => f (Function.update ω i z))) =
      (FinProb.pi P).expect f := by
  have hh := pi_expect_resample P {i} f
  have heq (ω : ∀ i, Ω i) :
      (FinProb.pi (fun j : ({i} : Finset I) => P j.1)).expect
          (fun z => f (resampleCoords {i} ω z)) =
        (P i).expect (fun z => f (Function.update ω i z)) := by
    let j₀ : ({i} : Finset I) := ⟨i, by simp⟩
    let e : (∀ j : ({i} : Finset I), Ω j.1) ≃ Ω i := {
      toFun z := z j₀
      invFun z j := by
        have hj : j.1 = i := Finset.mem_singleton.mp j.2
        exact hj.symm ▸ z
      left_inv z := by
        funext j
        have hj : j = j₀ := Subtype.ext (Finset.mem_singleton.mp j.2)
        subst j
        rfl
      right_inv z := rfl }
    unfold FinProb.expect
    rw [← Equiv.sum_comp e.symm]
    apply Finset.sum_congr rfl
    intro z _
    have hw : (FinProb.pi (fun j : ({i} : Finset I) => P j.1)).w (e.symm z) = (P i).w z := by
      change (∏ j : ({i} : Finset I), (P j.1).w (e.symm z j)) = _
      rw [Finset.prod_eq_single j₀]
      · simp [e, j₀]
      · intro j hj hne
        exact (hne (Subtype.ext (Finset.mem_singleton.mp j.2))).elim
      · intro hnot
        exact (hnot (Finset.mem_univ j₀)).elim
    have hfun : resampleCoords {i} ω (e.symm z) = Function.update ω i z := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [resampleCoords, e]
      · simp [resampleCoords, hj, Function.update_of_ne hj]
    rw [hw]
    change (P i).w z * f (resampleCoords {i} ω (e.symm z)) = (P i).w z * f (Function.update ω i z)
    rw [hfun]
  simpa only [heq] using hh

theorem prod_expect_resample_right {A B Z : Type*} [Fintype A] [Fintype B] [Fintype Z]
    (P : FinProb A) (Q : FinProb B) (R : FinProb Z) (update : B → Z → B)
    (hinvariant : ∀ f : B → ℝ, Q.expect (fun b => R.expect (fun z => f (update b z))) = Q.expect f)
    (f : A × B → ℝ) :
    (P.prod Q).expect (fun ab => R.expect (fun z => f (ab.1, update ab.2 z))) = (P.prod Q).expect f := by
  change (∑ ab : A × B, P.w ab.1 * Q.w ab.2 * R.expect (fun z => f (ab.1, update ab.2 z))) =
    ∑ ab : A × B, P.w ab.1 * Q.w ab.2 * f ab
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have hh := hinvariant (fun b => f (a, b))
  change (∑ b, Q.w b * R.expect (fun z => f (a, update b z))) = ∑ b, Q.w b * f (a, b) at hh
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hh]

theorem pi_expect_resample_cell {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] {Z : Type*} [Fintype Z]
    (P : ∀ i, FinProb (Ω i)) (i : I) (R : FinProb Z) (update : Ω i → Z → Ω i)
    (hinvariant : ∀ f : Ω i → ℝ, (P i).expect (fun x => R.expect (fun z => f (update x z))) = (P i).expect f)
    (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect (fun ω => R.expect (fun z => f (Function.update ω i (update (ω i) z)))) =
      (FinProb.pi P).expect f := by
  let g := fun ω => R.expect (fun z => f (Function.update ω i (update (ω i) z)))
  have hfirst := pi_expect_update P i g
  have hlast := pi_expect_update P i f
  change (FinProb.pi P).expect g = (FinProb.pi P).expect f
  rw [← hfirst, ← hlast]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  have hh := hinvariant (fun x => f (Function.update ω i x))
  simpa [g, FinProb.expect] using hh

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def replaceBlockData {h : X.HeightChoice5} (ω : X.CΩ h) (l : h.hp.Loc) (K : X.Ty)
    (S : Finset (Fin (X.p.typeBlocks n K))) (z : ∀ _i : S, X.Block K) : X.CΩ h :=
  Function.update ω l ((ω l).1, (ω l).2.1, (ω l).2.2.1,
    Function.update (ω l).2.2.2 K (resampleCoords S ((ω l).2.2.2 K) z))

theorem centre_expect_resample {h : X.HeightChoice5} (H : X.KeyHist) (l : h.hp.Loc) (K : X.Ty)
    (S : Finset (Fin (X.p.typeBlocks n K))) (f : X.CΩ h → ℝ) :
    (X.centreLaw h H).expect (fun ω =>
      (FinProb.pi (fun _i : S => X.blockLaw H K)).expect (fun z => f (replaceBlockData X ω l K S z))) =
      (X.centreLaw h H).expect f := by
  let R := FinProb.pi (fun _i : S => X.blockLaw H K)
  let updateArray (a : X.Array K) (z : ∀ _i : S, X.Block K) := resampleCoords S a z
  have hblock (f : X.Array K → ℝ) :
      (FinProb.pi (fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K)).expect
        (fun a => R.expect (fun z => f (updateArray a z))) =
      (FinProb.pi (fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K)).expect f :=
    pi_expect_resample (fun _ => X.blockLaw H K) S f
  let arrayLaw := FinProb.pi (fun K' : X.Ty => FinProb.pi (fun _ : Fin (X.p.typeBlocks n K') => X.blockLaw H K'))
  let updateTypes (a : ∀ K' : X.Ty, X.Array K') (z : ∀ _i : S, X.Block K) :=
    Function.update a K (updateArray (a K) z)
  have htypes (f : (∀ K' : X.Ty, X.Array K') → ℝ) :
      arrayLaw.expect (fun a => R.expect (fun z => f (updateTypes a z))) = arrayLaw.expect f :=
    pi_expect_resample_cell (fun K' : X.Ty => FinProb.pi (fun _ : Fin (X.p.typeBlocks n K') => X.blockLaw H K'))
      K R updateArray hblock f
  let tieLaw := FinProb.uniformAll (Ω := h.hp.TiePerm) ⟨1⟩
  have htie (f : h.hp.TiePerm × (∀ K' : X.Ty, X.Array K') → ℝ) :
      (tieLaw.prod arrayLaw).expect (fun a => R.expect (fun z => f (a.1, updateTypes a.2 z))) =
        (tieLaw.prod arrayLaw).expect f :=
    prod_expect_resample_right tieLaw arrayLaw R updateTypes htypes f
  let actLaw := FinProb.bernoulli ((n : ℝ) ^ h.b₀ / h.hp.lam)
  let updateTie (a : h.hp.TiePerm × (∀ K' : X.Ty, X.Array K')) (z : ∀ _i : S, X.Block K) :=
    (a.1, updateTypes a.2 z)
  have hact (f : Bool × h.hp.TiePerm × (∀ K' : X.Ty, X.Array K') → ℝ) :
      (actLaw.prod (tieLaw.prod arrayLaw)).expect (fun a => R.expect (fun z => f (a.1, updateTie a.2 z))) =
        (actLaw.prod (tieLaw.prod arrayLaw)).expect f :=
    prod_expect_resample_right actLaw (tieLaw.prod arrayLaw) R updateTie htie f
  let posLaw := FinProb.bernoulli (h.hp.lam / (h.hp.V : ℝ))
  let cellLaw := posLaw.prod (actLaw.prod (tieLaw.prod arrayLaw))
  let updateTail (a : Bool × h.hp.TiePerm × (∀ K' : X.Ty, X.Array K')) (z : ∀ _i : S, X.Block K) :=
    (a.1, updateTie a.2 z)
  let updateCell (a : X.CVal h) (z : ∀ _i : S, X.Block K) := (a.1, updateTail a.2 z)
  have hcell (f : X.CVal h → ℝ) :
      cellLaw.expect (fun a => R.expect (fun z => f (updateCell a z))) = cellLaw.expect f :=
    prod_expect_resample_right posLaw (actLaw.prod (tieLaw.prod arrayLaw)) R updateTail hact f
  exact pi_expect_resample_cell (fun _ : h.hp.Loc => cellLaw) l R updateCell hcell f

theorem resampleCoords_twice {I : Type*} [DecidableEq I] {Ω : I → Type*}
    (S : Finset I) (ω : ∀ i, Ω i) (z z' : ∀ i : S, Ω i.1) :
    resampleCoords S (resampleCoords S ω z) z' = resampleCoords S ω z' := by
  funext i
  by_cases hi : i ∈ S <;> simp [resampleCoords, hi]

theorem replaceBlockData_twice {h : X.HeightChoice5} (ω : X.CΩ h) (l : h.hp.Loc) (K : X.Ty)
    (S : Finset (Fin (X.p.typeBlocks n K))) (z z' : ∀ _i : S, X.Block K) :
    replaceBlockData X (replaceBlockData X ω l K S z) l K S z' = replaceBlockData X ω l K S z' := by
  unfold replaceBlockData
  simp only [Function.update_self]
  rw [resampleCoords_twice, Function.update_idem, Function.update_idem]

theorem test_bad_iff (m q ε : ℝ) (hm : 0 ≤ m) :
    ¬ (0 < m ∧ ε * q ≤ m) ↔ m < ε * q ∨ m = 0 := by
  by_cases hz : m = 0
  · simp [hz]
  · have hp : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
    simp [hp, hz, not_le]

theorem gated_resampling_bound {Ω Z D : Type*} [Fintype Ω] [Fintype Z] [Fintype D]
    (raw : FinProb Ω) (π : FinProb Z) (replace : Ω → Z → Ω)
    (hresample : ∀ f : Ω → ℝ, raw.expect (fun ω => π.expect (fun z => f (replace ω z))) = raw.expect f)
    (hreplace : ∀ ω z z', replace (replace ω z) z' = replace ω z')
    (F : Ω → D → ℝ) (hF : ∀ ω y, 0 ≤ F ω y) (Q : Ω → FinProb D)
    (hQ : ∀ ω z, Q (replace ω z) = Q ω) (ε : ℝ) (hε : 0 < ε) :
    let m := fun ω y => ∑ z, π.w z * F (replace ω z) y
    raw.expect (fun ω => ∑ y, if ¬ (0 < m ω y ∧ ε * (Q ω).w y ≤ m ω y) then F ω y else 0) ≤ ε := by
  dsimp only
  let m := fun ω y => ∑ z, π.w z * F (replace ω z) y
  let bad := fun ω y => ¬ (0 < m ω y ∧ ε * (Q ω).w y ≤ m ω y)
  let failMass := fun ω => ∑ y, if bad ω y then F ω y else 0
  have hm0 (ω : Ω) (y : D) : 0 ≤ m ω y :=
    Finset.sum_nonneg fun z _ => mul_nonneg (π.nonneg z) (hF _ _)
  have hmInvariant (ω : Ω) (z : Z) (y : D) : m (replace ω z) y = m ω y := by
    simp only [m, hreplace]
  have hbadInvariant (ω : Ω) (z : Z) (y : D) : bad (replace ω z) y = bad ω y := by
    simp only [bad, hmInvariant, hQ]
  have hpoint (ω : Ω) : π.expect (fun z => failMass (replace ω z)) ≤ ε := by
    have heq : π.expect (fun z => failMass (replace ω z)) =
        ∑ y, if bad ω y then m ω y else 0 := by
      unfold FinProb.expect
      simp only [failMass, hbadInvariant, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hb : bad ω y
      · simp only [if_pos hb]
        rfl
      · simp [hb]
    rw [heq]
    have hbound := (gated_posterior π (fun z y => F (replace ω z) y)
      (fun z y => hF _ _) (Q ω) ε 0 hε).1
    change (∑ y, if m ω y < ε * (Q ω).w y ∨ m ω y = 0 then m ω y else 0) ≤ ε at hbound
    have hbad (y : D) : bad ω y ↔ m ω y < ε * (Q ω).w y ∨ m ω y = 0 :=
      test_bad_iff _ _ _ (hm0 ω y)
    simpa only [hbad] using hbound
  change raw.expect failMass ≤ ε
  rw [← hresample failMass]
  calc
    _ ≤ raw.expect (fun _ => ε) := FinProb.expect_mono raw hpoint
    _ = ε := FinProb.expect_const raw ε

theorem map_weight_eq_pr {Ω D : Type*} [Fintype Ω] [Fintype D] [DecidableEq D]
    (P : FinProb Ω) (f : Ω → D) (d : D) :
    (FinProb.map P f).w d = P.pr (fun ω => f ω = d) := by
  change (∑ ω, if f ω = d then P.w ω else 0) = P.pr (fun ω => f ω = d)
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> rfl

def extendOutputs {I O : Type*} [DecidableEq I] (S : Finset I) (o₀ : O) (d : S → O) : I → O :=
  fun i => if hi : i ∈ S then d ⟨i, hi⟩ else o₀

theorem query_eq_iff {I O : Type*} [DecidableEq I] (S : Finset I) (o₀ : O)
    (ω : I → O) (d : S → O) :
    (fun i : S => ω i.1) = d ↔ ∀ i ∈ S, ω i = extendOutputs S o₀ d i := by
  constructor
  · intro h i hi
    have hh := congrFun h ⟨i, hi⟩
    simpa [extendOutputs, hi] using hh
  · intro h
    funext i
    simpa [extendOutputs, i.2] using h i.1 i.2

theorem query_weight {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (S : Finset I) [DecidableEq (S → O)] (P : FinProb (I → O)) (o₀ : O) (d : S → O) :
    (FinProb.map P (fun ω (i : S) => ω i.1)).w d =
      P.pr (fun ω => ∀ i ∈ S, ω i = extendOutputs S o₀ d i) := by
  rw [map_weight_eq_pr]
  congr 1
  funext ω
  exact propext (query_eq_iff S o₀ ω d)

theorem extend_project {I O : Type*} [DecidableEq I] (S : Finset I) (o₀ : O)
    (ω : I → O) (i : I) (hi : i ∈ S) :
    extendOutputs S o₀ (fun j : S => ω j.1) i = ω i := by
  simp [extendOutputs, hi]

theorem pi_query_weight {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (S : Finset I) (Q : I → FinProb O) (o₀ : O) (d : S → O) :
    (FinProb.pi (fun i : S => Q i.1)).w d = ∏ i ∈ S, (Q i).w (extendOutputs S o₀ d i) := by
  change (∏ i : S, (Q i.1).w (d i)) = _
  calc
    _ = ∏ i : S, (Q i.1).w (extendOutputs S o₀ d i.1) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [extendOutputs, i.2]
    _ = _ := by
      rw [Finset.univ_eq_attach]
      exact Finset.prod_attach S (fun i => (Q i).w (extendOutputs S o₀ d i))

end
end HypercubeRamsey.Lane_sol_s05_even
