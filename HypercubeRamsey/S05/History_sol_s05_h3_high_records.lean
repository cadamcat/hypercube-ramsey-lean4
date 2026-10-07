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

 theorem farSignature_signShift_fixed (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (q : CoarseKey5 n) (c : X.Ty × Option X.Key)
    (hc : c ∈ farHighSignatures X q) : sigSignMap X t c = c := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
  simp only [sigSignMap, signShiftType5, Finset.image_image, Function.comp_def, Option.map_none]
  rfl

 theorem joint_far_subset (X : Setup5 γ K' χ n N E G)
    (y : OddRole5 n) (μ : X.St.Site → Fin (X.p.T n))
    (hj : X.p.J n + 2 < X.g.severity y.1) :
    ((Setup5.evenNbrs y).image fun a =>
      (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)) ⊆
      (Finset.univ : Finset (Fin (X.p.T n))).product (farHighSignatures X (X.g.key y.1)) := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hadj := (Finset.mem_filter.mp ha).2.symm
  obtain ⟨b, hb⟩ := adjacent_flip y.1 a.1 hadj
  have hs := severity_flip_bounds X.g y.1 b
  rw [← hb] at hs
  have hhi : ¬ X.g.severity a.1 ≤ X.p.J n := by omega
  have hopt : X.g.severity a.1 ≠ X.p.J n + 1 := by omega
  have hdata := neighbor_coarse_data X.g y.1 a.1 hadj
  apply Finset.mem_image.mpr
  refine ⟨(X.g.key a.1, X.g.coarseRange a.1),
    Finset.mem_product.mpr ⟨hdata.1, Finset.mem_powerset.mpr hdata.2⟩, ?_⟩
  simp [ChunkGeometry5.evenType, ChunkGeometry5.typeKeys, ChunkGeometry5.optionalKey, hhi, hopt]

 theorem normalized_high_record_mem (X : Setup5 γ K' χ n N E G)
    (y : OddRole5 n) (μ : X.St.Site → Fin (X.p.T n)) (r : X.AbsRecord)
    (hr : X.RecordFrom r y μ) (q : CoarseKey5 n) (hkey : r.1 = .inr q) :
    shiftHighRecord X (X.g.sign y.1) r ∈ normalizedHighRecordUniverse X q := by
  classical
  have hocc : X.RecOccurs r := ⟨y, μ, hr⟩
  have hmask := occurring_high_mask_none X r hocc q hkey
  have hq : X.g.key y.1 = q := by
    rw [← Lane_sol_s05_hist1b.roleKey_coarse X y.1, hr.1, hkey]
    rfl
  have hhigh : X.p.J n < X.g.severity y.1 := by
    by_cases h : X.g.severity y.1 ≤ X.p.J n
    · have hh := hr.1.trans hkey
      simp [ChunkGeometry5.roleKey, h] at hh
    · omega
  let I := (Setup5.evenNbrs y).image fun a =>
    (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)
  have he : recordFromJoint X (.inr q) I none = r := by
    simpa only [hkey, hmask] using recordFromJoint_eq X y μ r hr
  have hn : shiftHighRecord X (X.g.sign y.1) r =
      recordFromJoint X (.inr q) (I.image (jointSignMap X (X.g.sign y.1))) none := by
    rw [← he, recordFromJoint_high_signShift]
  rw [hn]
  by_cases hj : X.p.J n + 2 < X.g.severity y.1
  · have hsub : I.image (jointSignMap X (X.g.sign y.1)) ⊆
        (Finset.univ : Finset (Fin (X.p.T n))).product (farHighSignatures X q) := by
      intro c hc
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      have hd' := joint_far_subset X y μ hj hd
      have hsig : d.2 ∈ farHighSignatures X q := by
        simpa only [hq] using (Finset.mem_product.mp hd').2
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, by
        change sigSignMap X (X.g.sign y.1) d.2 ∈ farHighSignatures X q
        rw [farSignature_signShift_fixed X (X.g.sign y.1) q d.2 hsig]
        exact hsig⟩
    apply Finset.mem_union.mpr
    exact Or.inr (Finset.mem_image.mpr
      ⟨_, Finset.mem_powerset.mpr hsub, rfl⟩)
  · have hI : I.image (jointSignMap X (X.g.sign y.1)) ∈
        groupJointUniverse X q default (X.g.severity y.1) (X.g.flippable y.1) := by
      simpa only [I, jointSignMap, Finset.image_image, Function.comp_def, hq] using
        joint_normalized_mem X y μ
    have hnear : recordFromJoint X (.inr q) (I.image (jointSignMap X (X.g.sign y.1))) none ∈
        nearHighRecordUniverse X q (X.g.severity y.1) := by
      exact Finset.mem_biUnion.mpr ⟨X.g.flippable y.1,
        (mem_smallSubsets _).mpr (flippable_card_le_severity5 X y.1),
        Finset.mem_image.mpr ⟨_, hI, rfl⟩⟩
    have hsev : X.g.severity y.1 = X.p.J n + 1 ∨ X.g.severity y.1 = X.p.J n + 2 := by omega
    apply Finset.mem_union.mpr
    apply Or.inl
    apply Finset.mem_union.mpr
    rcases hsev with h1 | h2
    · exact Or.inl (by simpa only [h1] using hnear)
    · exact Or.inr (by simpa only [h2] using hnear)

 def highRecordCountBound (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  2 ^ (p.T n * signatureConstant) * (p.m n + 1) ^ (20 * (p.J n + 4))

 theorem nearHighRecordUniverse_card_poly (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : ℕ) (hj : j ≤ X.p.J n + 2)
    (hm : 2 ≤ X.p.m n) (hD : signatureConstant ≤ X.p.m n) (hT : X.p.T n ≤ X.p.m n) :
    (nearHighRecordUniverse X q j).card ≤ highRecordCountBound X.p n := by
  have hJ := Lane_sol_s05_h1.J_le_m X.p n (by omega)
  have hjm : j ≤ X.p.m n + 2 := by omega
  let M := X.p.m n + 1
  let A := X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1))
  have hM : 3 ≤ M := by dsimp [M]; omega
  have h2 : 2 * X.p.m n + 1 ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hTD : X.p.T n * signatureConstant ≤ M ^ 2 := by
    calc
      _ ≤ X.p.m n * X.p.m n := Nat.mul_le_mul hT hD
      _ ≤ M * M := Nat.mul_le_mul (by dsimp [M]; omega) (by dsimp [M]; omega)
      _ = _ := (pow_two _).symm
  have hA' : A ≤ M ^ 5 := by
    calc
      _ = (X.p.T n * signatureConstant) * M * (2 * X.p.m n + 1) := by dsimp [A, M]; ac_rfl
      _ ≤ M ^ 2 * M * M ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul_right _ hTD) h2
      _ = M ^ 5 := by ring
  have hA : A + 1 ≤ M ^ 6 := by
    have h5 : 1 ≤ M ^ 5 := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ M ^ 5 + 1 := Nat.add_le_add_right hA' 1
      _ ≤ M ^ 5 * 2 := by omega
      _ ≤ M ^ 5 * M := Nat.mul_le_mul_left _ (by omega)
      _ = _ := (pow_succ M 5).symm
  have hs : j + 1 ≤ M ^ 2 := by dsimp [M]; nlinarith
  have ht : 2 * j + 1 ≤ M ^ 3 := by
    have hlin : 2 * j + 1 ≤ 3 * M := by dsimp [M]; omega
    have hMM : 3 ≤ M ^ 2 := by nlinarith
    exact hlin.trans ((Nat.mul_le_mul_right M hMM).trans_eq (pow_succ M 2).symm)
  apply (nearHighRecordUniverse_card X q j).trans
  change ((j + 1) * M ^ j) *
    (2 ^ (X.p.T n * signatureConstant) * (2 * j + 1) * (A + 1) ^ (2 * j)) ≤ _
  calc
    _ ≤ (M ^ 2 * M ^ j) *
        (2 ^ (X.p.T n * signatureConstant) * M ^ 3 * (M ^ 6) ^ (2 * j)) := by gcongr
    _ = 2 ^ (X.p.T n * signatureConstant) * M ^ (13 * j + 5) := by
      rw [← pow_mul]
      calc
        _ = 2 ^ (X.p.T n * signatureConstant) * (M ^ 2 * M ^ j * M ^ 3 * M ^ (6 * (2 * j))) := by ac_rfl
        _ = _ := by
          have he : 2 + j + 3 + 6 * (2 * j) = 13 * j + 5 := by omega
          simp only [← pow_add, he]
    _ ≤ highRecordCountBound X.p n := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by omega : 0 < M)
      omega

 theorem normalizedHighRecordUniverse_card (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (hm : 2 ≤ X.p.m n) (hD : signatureConstant ≤ X.p.m n)
    (hT : X.p.T n ≤ X.p.m n) :
    (normalizedHighRecordUniverse X q).card ≤ 3 * highRecordCountBound X.p n := by
  have ha := nearHighRecordUniverse_card_poly X q (X.p.J n + 1) (by omega) hm hD hT
  have hb := nearHighRecordUniverse_card_poly X q (X.p.J n + 2) le_rfl hm hD hT
  have hc : (farHighRecordUniverse X q).card ≤ highRecordCountBound X.p n := by
    apply (farHighRecordUniverse_card X q).trans
    calc
      _ = 2 ^ (X.p.T n * signatureConstant) * 1 := (mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega : 0 < X.p.m n + 1))
  unfold normalizedHighRecordUniverse
  calc
    _ ≤ (nearHighRecordUniverse X q (X.p.J n + 1) ∪ nearHighRecordUniverse X q (X.p.J n + 2)).card +
        (farHighRecordUniverse X q).card := Finset.card_union_le _ _
    _ ≤ (nearHighRecordUniverse X q (X.p.J n + 1)).card +
        (nearHighRecordUniverse X q (X.p.J n + 2)).card +
        (farHighRecordUniverse X q).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ highRecordCountBound X.p n + highRecordCountBound X.p n + highRecordCountBound X.p n := by omega
    _ = _ := by omega

abbrev NormalizedHighRecordAt (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  {r : X.AbsRecord // r ∈ normalizedHighRecordUniverse X q ∧
    ∃ r₀ : X.AbsRecord, ∃ t : CubeVertex (X.p.m n), X.RecOccurs r₀ ∧ r₀.1 = .inr q ∧
      r = shiftHighRecord X t r₀}

noncomputable instance normalizedHighRecordAtFintype (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (NormalizedHighRecordAt X q) := by
  classical
  infer_instance

 theorem normalizedHighRecordAt_card (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (hm : 2 ≤ X.p.m n) (hD : signatureConstant ≤ X.p.m n)
    (hT : X.p.T n ≤ X.p.m n) :
    Fintype.card (NormalizedHighRecordAt X q) ≤ 3 * highRecordCountBound X.p n := by
  classical
  let f : NormalizedHighRecordAt X q → {r // r ∈ normalizedHighRecordUniverse X q} :=
    fun r => ⟨r.1, r.2.1⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun r : {r // r ∈ normalizedHighRecordUniverse X q} => r.1) h)
  apply (Fintype.card_le_of_injective f hf).trans
  rw [Fintype.card_coe]
  exact normalizedHighRecordUniverse_card X q hm hD hT

 theorem normalizedHighRecordAt_exists (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (r : X.AbsRecord) (hr : X.RecOccurs r) (hkey : r.1 = .inr q) :
    ∃ t : CubeVertex (X.p.m n), ∃ r' : NormalizedHighRecordAt X q,
      r'.1 = shiftHighRecord X t r := by
  obtain ⟨y, μ, hrec⟩ := hr
  refine ⟨X.g.sign y.1, ⟨shiftHighRecord X (X.g.sign y.1) r, ?_⟩, rfl⟩
  exact ⟨normalized_high_record_mem X y μ r hrec q hkey,
    r, X.g.sign y.1, ⟨y, μ, hrec⟩, hkey, rfl⟩

end
end HypercubeRamsey.Lane_sol_s05_h23
