import HypercubeRamsey.S05.History_sol_s05_h3_counts

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical OAI.HypercubeRamsey Lane_q_s05_h23
open Lane_sol_s05_hist1b Lane_sol_s05_h5l
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

def jointSignMap (X : Setup5 γ K' χ n N E G) (t : CubeVertex (X.p.m n))
    (c : Fin (X.p.T n) × X.Ty × Option X.Key) : Fin (X.p.T n) × X.Ty × Option X.Key :=
  (c.1, sigSignMap X t c.2)

 theorem recordFromJoint_high_signShift (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (q : CoarseKey5 n)
    (I : Finset (Fin (X.p.T n) × X.Ty × Option X.Key)) :
    shiftHighRecord X t (recordFromJoint X (.inr q) I none) =
      recordFromJoint X (.inr q) (I.image (jointSignMap X t)) none := by
  classical
  let p : (Fin (X.p.T n) × X.Ty × Option X.Key) → Prop := fun c =>
    (.inr q : X.Key) ∈ c.2.1.2.1 ∧ (.inr q : X.Key).isLeft = c.2.1.2.2.isSome
  have hp (c) : p (jointSignMap X t c) ↔ p c := by
    change ((.inr q : X.Key) ∈ c.2.1.2.1.image (signShiftKey5 X t) ∧
      (.inr q : X.Key).isLeft = c.2.1.2.2.isSome) ↔ _
    rw [mem_signShift_keys_high]
  have hf : (I.filter p).image (jointSignMap X t) =
      (I.image (jointSignMap X t)).filter p := by
    ext c
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨d, ⟨hd, hp'⟩, rfl⟩
      exact ⟨⟨d, hd, rfl⟩, (hp d).mpr hp'⟩
    · rintro ⟨⟨d, hd, rfl⟩, hp'⟩
      exact ⟨d, ⟨hd, (hp d).mp hp'⟩, rfl⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change (I.image (fun c => (c.1, c.2.1))).image (obsSignMap X t) =
      (I.image (jointSignMap X t)).image (fun c => (c.1, c.2.1))
    rw [Finset.image_image, Finset.image_image]
    rfl
  apply Prod.ext
  · exact hf
  · rfl

 def nearHighRecordUniverse (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (j : ℕ) : Finset X.AbsRecord :=
  (smallSubsets (X.p.m n) j).biUnion fun F =>
    (groupJointUniverse X q default j F).image (fun I => recordFromJoint X (.inr q) I none)

 def farHighRecordUniverse (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) : Finset X.AbsRecord :=
  (((Finset.univ : Finset (Fin (X.p.T n))).product (farHighSignatures X q)).powerset).image
    (fun I => recordFromJoint X (.inr q) I none)

 def normalizedHighRecordUniverse (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Finset X.AbsRecord :=
  nearHighRecordUniverse X q (X.p.J n + 1) ∪
    nearHighRecordUniverse X q (X.p.J n + 2) ∪ farHighRecordUniverse X q

 theorem nearHighRecordUniverse_card (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (j : ℕ) :
    (nearHighRecordUniverse X q j).card ≤
      ((j + 1) * (X.p.m n + 1) ^ j) *
        (2 ^ (X.p.T n * signatureConstant) * (2 * j + 1) *
          (X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) + 1) ^ (2 * j)) := by
  classical
  unfold nearHighRecordUniverse
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ F ∈ smallSubsets (X.p.m n) j,
        2 ^ (X.p.T n * signatureConstant) * (2 * j + 1) *
          (X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) + 1) ^ (2 * j) := by
      apply Finset.sum_le_sum
      intro F hF
      exact Finset.card_image_le.trans (groupJointUniverse_card X q default j F)
    _ = (smallSubsets (X.p.m n) j).card *
        (2 ^ (X.p.T n * signatureConstant) * (2 * j + 1) *
          (X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) + 1) ^ (2 * j)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (smallSubsets_card _ _)

 theorem farHighRecordUniverse_card (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :
    (farHighRecordUniverse X q).card ≤ 2 ^ (X.p.T n * signatureConstant) := by
  calc
    _ ≤ _ := Finset.card_image_le
    _ = 2 ^ (X.p.T n * (farHighSignatures X q).card) := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < 2)
      (Nat.mul_le_mul_left _ (farHighSignatures_card X q))

end
end HypercubeRamsey.Lane_sol_s05_h23
