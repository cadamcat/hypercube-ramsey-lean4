import HypercubeRamsey.S05.History_sol_s05_h3_symmetry
import HypercubeRamsey.S05.History_sol_s05_hist1e_bound

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical OAI.HypercubeRamsey Lane_q_s05_h23
open Lane_sol_s05_hist1b Lane_sol_s05_h5l
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

 theorem shiftSign_flip {m : ℕ} (t s : CubeVertex m) (i : Fin m) :
    shiftSignVector5 t (flipVertex5 s i) = flipVertex5 (shiftSignVector5 t s) i := by
  funext k
  by_cases hk : k = i
  · subst k
    cases ht : t i <;> cases hs : s i <;>
      simp [shiftSignVector5, flipVertex5, Function.update, ht, hs]
  · simp [shiftSignVector5, flipVertex5, Function.update_of_ne hk]

 theorem normalized_signBall1 {m : ℕ} (t s : CubeVertex m) (hs : s ∈ signBall1 t) :
    shiftSignVector5 t s ∈ signBall1 (default : CubeVertex m) := by
  simp only [signBall1, Finset.mem_insert, Finset.mem_image] at hs ⊢
  rcases hs with hsame | ⟨i, hi, rfl⟩
  · exact Or.inl (by rw [hsame]; exact shiftSignVector_self5 t)
  · exact Or.inr ⟨i, hi, by
      change flipVertex5 default i = shiftSignVector5 t (flipVertex5 t i)
      rw [shiftSign_flip, shiftSignVector_self5]⟩

def sigSignMap (X : Setup5 γ K' χ n N E G) (t : CubeVertex (X.p.m n))
    (c : X.Ty × Option X.Key) : X.Ty × Option X.Key :=
  (signShiftType5 X t c.1, c.2.map (signShiftKey5 X t))

 theorem signatureFromData_signShift (X : Setup5 γ K' χ n N E G)
    (t s : CubeVertex (X.p.m n)) (q : CoarseKey5 n) (C : Finset (CoarseKey5 n))
    (F : Finset (Fin (X.p.m n))) (j : ℕ) :
    sigSignMap X t (signatureFromData (X.p.J n) q C s F j) =
      signatureFromData (X.p.J n) q C (shiftSignVector5 t s) F j := by
  classical
  by_cases hj : j ≤ X.p.J n
  · simp only [sigSignMap, signatureFromData, signShiftType5, hj, dite_true, ite_true,
      Finset.image_union, Finset.image_image, Function.comp_def, Option.map_ite, Option.map_some, Option.map_none]
    simp_rw [signShiftKey5_keyAt5, shiftSign_flip]
    by_cases ho : j = X.p.J n + 1
    · omega
    · simp only [ho, ite_false, Option.map_none]
  · simp only [sigSignMap, signatureFromData, signShiftType5, hj, dite_false, ite_false,
      Finset.image_image, Function.comp_def, Option.map_ite, Option.map_some, Option.map_none]
    have he : (fun i : CoarseKey5 n => signShiftKey5 X t (.inr i)) = Sum.inr := by
      funext i
      rfl
    rw [he]
    by_cases ho : j = X.p.J n + 1
    · simp only [ho, ite_true]
      rfl
    · simp only [ho, ite_false]

 theorem genericSignature_normalized_mem (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (q : CoarseKey5 n) (F : Finset (Fin (X.p.m n)))
    (j : ℕ) (c : X.Ty × Option X.Key)
    (hc : c ∈ genericSignatures (X.p.J n) q t j F) :
    sigSignMap X t c ∈ genericSignatures (X.p.J n) q default j F := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
  apply Finset.mem_image.mpr
  refine ⟨d, hd, ?_⟩
  symm
  simpa only [shiftSignVector_self5] using
    signatureFromData_signShift X t t d.1.1 d.1.2 F d.2

 theorem allSignature_normalized_mem (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (q : CoarseKey5 n) (F : Finset (Fin (X.p.m n)))
    (j : ℕ) (c : X.Ty × Option X.Key)
    (hc : c ∈ allSignatures (X.p.J n) q t j F) :
    sigSignMap X t c ∈ allSignatures (X.p.J n) q default j F := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hq, hf⟩ := Finset.mem_product.mp hd
  obtain ⟨hs, hrest⟩ := Finset.mem_product.mp hf
  apply Finset.mem_image.mpr
  refine ⟨(d.1, (shiftSignVector5 t d.2.1, d.2.2)),
    Finset.mem_product.mpr ⟨hq, Finset.mem_product.mpr
      ⟨normalized_signBall1 t d.2.1 hs, hrest⟩⟩, ?_⟩
  symm
  exact signatureFromData_signShift X t d.2.1 d.1.1 d.1.2 d.2.2.1 d.2.2.2

 theorem joint_normalized_mem (X : Setup5 γ K' χ n N E G)
    (y : OddRole5 n) (μ : X.St.Site → Fin (X.p.T n)) :
    ((Setup5.evenNbrs y).image fun a =>
      (μ (X.St.stateOf a.1), sigSignMap X (X.g.sign y.1)
        (X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1))) ∈
      groupJointUniverse X (X.g.key y.1) default (X.g.severity y.1) (X.g.flippable y.1) := by
  classical
  apply joint_image_sparse (Setup5.evenNbrs y) (fun a => X.St.stateOf a.1)
    (fun a => sigSignMap X (X.g.sign y.1)
      (X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)) μ
    _ _ (criticalStates X.g X.St y.1) _
  · intro a ha he
    apply genericSignature_normalized_mem
    exact neighbor_genericSignatures X.g X.St y.1 a.1 ((Finset.mem_filter.mp ha).2.symm) he
  · intro a ha
    apply allSignature_normalized_mem
    exact neighbor_allSignatures X.g (X.p.J n) y.1 a.1 ((Finset.mem_filter.mp ha).2.symm)
  · intro a ha b hb he
    have h := X.St.state_determines a.1 b.1 he
    exact congrArg (sigSignMap X (X.g.sign y.1)) (Prod.ext h.2.2.2.2.1 h.2.2.2.2.2.1)
  · exact critical_flip_states_card_le X.g X.St y.1

end
end HypercubeRamsey.Lane_sol_s05_h23
