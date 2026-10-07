import HypercubeRamsey.S06.OddRows
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.Tools.ScatteredUnion
import Mathlib.Data.Nat.Choose.Bounds

namespace HypercubeRamsey
namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey
open OAI.HypercubeRamsey

open S06
open Classical
open Filter Real Set
open OAI.HypercubeRamsey
open scoped Topology

/-- Expectation under `restrictOr6` is the raw weighted sum conditioned on its event. -/
theorem restrictOr6_expect_formula {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) (ω₀ : Ω) (hA : 0 < P.pr A) (f : Ω → ℝ) :
    (restrictOr6 P A ω₀).expect f =
      (∑ ω, if A ω then P.w ω * f ω else 0) / P.pr A := by
  classical
  have hmax (ω : Ω) :
      max 0 (if A ω then P.w ω else 0) = if A ω then P.w ω else 0 := by
    by_cases h : A ω
    · simp [h, P.nonneg ω]
    · simp [h]
  have hmass :
      (∑ ω, if A ω then P.w ω else 0) = P.pr A := by
    unfold FinProb.pr
    rfl
  have hweight (ω : Ω) :
      (restrictOr6 P A ω₀).w ω = (if A ω then P.w ω else 0) / P.pr A := by
    simp [restrictOr6, normalize6, hmass, hmax, hA]
  unfold FinProb.expect
  simp_rw [hweight]
  calc
    (∑ ω, (if A ω then P.w ω else 0) / P.pr A * f ω) =
        ∑ ω, (if A ω then P.w ω * f ω else 0) / P.pr A := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : A ω <;> simp [h] <;> ring
    _ = (∑ ω, if A ω then P.w ω * f ω else 0) / P.pr A := by
      rw [Finset.sum_div]

/-- A valid avoidance certificate guarantees positive mass for avoiding every certified event. -/
theorem S06.AvoidCert6.mass_avoid_pos {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [DecidableEq I] {w : Ω → ℝ} {E : I → Finset Ω} {xmax : ℝ}
    (cert : HypercubeRamsey.S06.AvoidCert6 w E xmax)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (hxmax : xmax < 1) :
    0 < LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := by
  classical
  let p : I → ℝ := fun i =>
    cert.x i * ∏ j ∈ Finset.univ.filter (cert.adj i), (1 - cert.x j)
  have hx0 : ∀ i, 0 ≤ cert.x i := cert.x_nonneg
  have hx1 : ∀ i, cert.x i < 1 := by
    intro i
    exact (cert.x_le i).trans_lt hxmax
  have hpx : ∀ i, p i ≤ cert.x i * ∏ j ∈ Finset.univ.filter (cert.adj i), (1 - cert.x j) := by
    intro i
    rfl
  have hAvoid := LocalLemma.conditional_avoidance w hw hw1 E cert.adj
    cert.adj_symm cert.adj_irrefl p cert.x cert.local_bound hx0 hx1 hpx
  exact hAvoid.1

/-- Supported histories avoid every stage-3 bad event indexed by a bin and central sign. -/
theorem histSupport_noBad3 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M)
    (hSupport : X.HistSupport) (H : X.Hist) (hH : X.histLaw.w H ≠ 0)
    (gr : X.Bin × CubeVertex X.m) : ¬ X.Bad3 H.1 gr H.2 := by
  rcases hSupport H hH with ⟨_, _, _, _, hTests, hRate3⟩
  intro hBad
  rcases hBad with ⟨x, hEven, hbin, hsign, hFail⟩ |
      ⟨b, hb, hbin, hsign, D, hD, hRate⟩
  · have hmem : X.evenType x ∈ X.occTypes := by
      unfold S06.Ctx6.occTypes
      exact Finset.mem_image.mpr ⟨x,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEven⟩, rfl⟩
    exact hFail.2 (hTests (X.evenType x) hmem)
  · exact (not_lt_of_ge (hRate3 b hb D hD)) hRate

/-- Step-2 tests only read hidden scalars in the type's observation list. -/
theorem step2Tests_congr_hid {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : S06.Ctx6 γ p₀ K n N E G M) (b : X.Base) (Z Z' : X.Hid) (β : X.Ty)
    (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.Step2Tests (b, Z) β ↔ X.Step2Tests (b, Z') β := by
  classical
  have hWeight (S : Finset X.HKey) (hS : S ⊆ β.obs) (i : X.ι) :
      X.tagWeight (b, Z) β S i = X.tagWeight (b, Z') β S i := by
    unfold S06.Ctx6.tagWeight
    have hprod :
        (∏ ℓ ∈ S, safeRatio6 ((X.hidPostRep b ℓ.1 β.key i).w (Z ℓ))
          ((X.hidPostDel b ℓ.1 β.key).w (Z ℓ))) =
        ∏ ℓ ∈ S, safeRatio6 ((X.hidPostRep b ℓ.1 β.key i).w (Z' ℓ))
          ((X.hidPostDel b ℓ.1 β.key).w (Z' ℓ)) := by
      apply Finset.prod_congr rfl
      intro ℓ hℓ
      rw [hobs ℓ (hS hℓ)]
    rw [hprod]
  have hMass (S : Finset X.HKey) (hS : S ⊆ β.obs) :
      X.tagMass (b, Z) β S = X.tagMass (b, Z') β S := by
    unfold S06.Ctx6.tagMass
    apply Finset.sum_congr rfl
    intro i hi
    exact hWeight S hS i
  have hObsSub : β.obs ⊆ β.obs := Finset.Subset.rfl
  constructor
  · intro h
    unfold S06.Ctx6.Step2Tests at h ⊢
    rcases h with ⟨hpos, hthr, hdel⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hMass β.obs hObsSub]
      exact hpos
    · rw [← hMass β.obs hObsSub]
      exact hthr
    · intro ℓ hℓ
      rw [← hMass (β.obs.erase ℓ) (Finset.erase_subset _ _), ← hMass β.obs hObsSub]
      exact hdel ℓ hℓ
  · intro h
    unfold S06.Ctx6.Step2Tests at h ⊢
    rcases h with ⟨hpos, hthr, hdel⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hMass β.obs hObsSub]
      exact hpos
    · rw [hMass β.obs hObsSub]
      exact hthr
    · intro ℓ hℓ
      rw [hMass (β.obs.erase ℓ) (Finset.erase_subset _ _), hMass β.obs hObsSub]
      exact hdel ℓ hℓ

set_option maxHeartbeats 2000000
/-- A supported history witnesses positive raw hidden mass on the stage-3 avoidance event. -/
theorem histSupport_hidLaw_good_mass_pos {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : S06.Ctx6 γ p₀ K n N E G M) (hSupport : X.HistSupport)
    (H : X.Hist) (hH : X.histLaw.w H ≠ 0) :
    (X.hidLaw H.1).pr (fun Z => ∀ gr, ¬ X.Bad3 H.1 gr Z) > 0 := by
  rcases hSupport H hH with ⟨_hBase, hPost, _hV0, _hStep1, _hStep2, _hRate3⟩
  have hGood : ∀ gr, ¬ X.Bad3 H.1 gr H.2 := histSupport_noBad3 X hSupport H hH
  have hRaw : 0 < (X.hidLaw H.1).w H.2 := by
    simp only [S06.Ctx6.hidLaw, FinProb.pi]
    apply Finset.prod_pos
    intro ℓ hℓ
    exact hPost ℓ
  unfold FinProb.pr
  letI : DecidablePred (fun Z : X.Hid => ∀ gr, ¬ X.Bad3 H.1 gr Z) :=
    fun Z => Classical.propDecidable _
  have hsingle := Finset.single_le_sum (s := Finset.univ)
    (f := fun Z : X.Hid => if (∀ gr, ¬ X.Bad3 H.1 gr Z) then
      (X.hidLaw H.1).w Z else 0)
    (fun Z _ => by
      split_ifs with h
      · exact (X.hidLaw H.1).nonneg Z
      · exact le_rfl) (Finset.mem_univ H.2)
  have hterm : (0 : ℝ) <
      if (∀ gr, ¬ X.Bad3 H.1 gr H.2) then (X.hidLaw H.1).w H.2 else 0 := by
    simp [hGood, hRaw]
  exact lt_of_lt_of_le hterm hsingle

/-- The stage-3 expectation is the raw hidden expectation conditioned on avoiding `Bad3`. -/
theorem stage3Law_expect_formula {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : S06.Ctx6 γ p₀ K n N E G M) (b₀ : X.Base)
    (hGood : 0 < (X.hidLaw b₀).pr (fun Z => ∀ gr, ¬ X.Bad3 b₀ gr Z)) (f : X.Hid → ℝ) :
    (X.stage3Law b₀).expect f =
      (∑ Z, if (∀ gr, ¬ X.Bad3 b₀ gr Z) then (X.hidLaw b₀).w Z * f Z else 0) /
        (X.hidLaw b₀).pr (fun Z => ∀ gr, ¬ X.Bad3 b₀ gr Z) := by
  simpa [S06.Ctx6.stage3Law] using
    restrictOr6_expect_formula (X.hidLaw b₀)
      (fun Z => ∀ gr, ¬ X.Bad3 b₀ gr Z) (fun _ => X.y₀) hGood f

/-- One actual cube edge changes at most one fine sign. -/
theorem adjacent_sign_dist_le_one {n : ℕ} {α : ℝ} (g : S06.ChunkGeometry6 n α)
    {x y : CubeVertex n} (hxy : (cube n).Adj x y) :
    _root_.hammingDist (g.L.sign x) (g.L.sign y) ≤ 1 := by
  classical
  by_cases hflip : ∃ i a, a ∈ g.L.fineChunks i ∧ x a ≠ y a
  · obtain ⟨i, a, hai, haxy⟩ := hflip
    have hsign := g.flips.fine_flip_sign x y i hxy ⟨a, hai, haxy⟩
    have hsub :
        (Finset.univ.filter fun j : Fin g.L.m => g.L.sign x j ≠ g.L.sign y j) ⊆ {i} := by
      intro j hj
      have hdiff : g.L.sign x j ≠ g.L.sign y j := (Finset.mem_filter.mp hj).2
      by_cases hji : j = i
      · simp [hji]
      · exact False.elim (hdiff (hsign j hji))
    change (Finset.univ.filter
      (fun j : Fin g.L.m => g.L.sign x j ≠ g.L.sign y j)).card ≤ 1
    calc
      _ ≤ ({i} : Finset (Fin g.L.m)).card := Finset.card_le_card hsub
      _ = 1 := by simp
  · have hagree : ∀ i a, a ∈ g.L.fineChunks i → x a = y a := by
      intro i a hai
      by_contra hne
      exact hflip ⟨i, a, hai, hne⟩
    have hsign := (g.flips.nonfine_flip_fine x y hxy hagree).1
    simp [hsign, _root_.hammingDist]

/-- Sign neighborhoods of consecutive odd/even states differ in one coordinate. -/
theorem ctx6_stNbr_sign_dist_le_one {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : S06.Ctx6 γ p₀ K n N E G M) (b a : X.State) (ha : a ∈ X.g.L.stNbr b) :
    _root_.hammingDist (X.g.L.stSign b) (X.g.L.stSign a) ≤ 1 := by
  classical
  simp only [S06.ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  rcases ha with ⟨u, v, _, _, hbu, hav, huv⟩
  have hdist := adjacent_sign_dist_le_one X.g huv
  have hsignu := X.facts.sign_eq u
  have hsignv := X.facts.sign_eq v
  calc
    _ = _ := by rw [← hbu, ← hav, hsignu, hsignv]
    _ ≤ 1 := hdist

/-- A two-step state neighborhood stays within two sign flips. -/
theorem ctx6_twoNbr_sign_dist_le_two {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : S06.Ctx6 γ p₀ K n N E G M) (b a a' : X.State)
    (ha : a ∈ X.g.L.stNbr b) (ha' : a' ∈ X.g.L.stNbr a) :
    _root_.hammingDist (X.g.L.stSign b) (X.g.L.stSign a') ≤ 2 := by
  have h1 := ctx6_stNbr_sign_dist_le_one X b a ha
  have h2 := ctx6_stNbr_sign_dist_le_one X a a' ha'
  calc
    _ ≤ _root_.hammingDist (X.g.L.stSign b) (X.g.L.stSign a) +
        _root_.hammingDist (X.g.L.stSign a) (X.g.L.stSign a') :=
      _root_.hammingDist_triangle _ _ _
    _ ≤ 2 := by omega

/-- A three-step state neighborhood stays within three sign flips. -/
theorem ctx6_threeNbr_sign_dist_le_three {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : S06.Ctx6 γ p₀ K n N E G M) (b a a' a'' : X.State)
    (ha : a ∈ X.g.L.stNbr b) (ha' : a' ∈ X.g.L.stNbr a)
    (ha'' : a'' ∈ X.g.L.stNbr a') :
    _root_.hammingDist (X.g.L.stSign b) (X.g.L.stSign a'') ≤ 3 := by
  have h2 := ctx6_twoNbr_sign_dist_le_two X b a a' ha ha'
  have h1 := ctx6_stNbr_sign_dist_le_one X a' a'' ha''
  calc
    _ ≤ _root_.hammingDist (X.g.L.stSign b) (X.g.L.stSign a') +
        _root_.hammingDist (X.g.L.stSign a') (X.g.L.stSign a'') :=
      _root_.hammingDist_triangle _ _ _
    _ ≤ 3 := by omega

/-- Coarse keys reachable in at most `r` key-neighborhood steps. -/
noncomputable def keyBall6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M)
    (h : X.Key) : ℕ → Finset X.Key
  | 0 => {h}
  | r + 1 => (keyBall6 X h r).biUnion X.C

/-- The bounded degree of the coarse-key graph bounds every fixed-radius key ball. -/
theorem keyBall6_card_le {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M)
    (h : X.Key) : ∀ r, (keyBall6 X h r).card ≤ 602 ^ r := by
  intro r
  induction r with
  | zero => simp [keyBall6]
  | succ r ih =>
    have hdegree (k : X.Key) : (X.C k).card ≤ 602 := by
      simpa [S06.Ctx6.C] using X.g.flips.key_neighborhood_card k
    calc
      (keyBall6 X h (r + 1)).card ≤
          ∑ k ∈ keyBall6 X h r, (X.C k).card := by
            simp only [keyBall6]
            exact Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ keyBall6 X h r, 602 :=
        Finset.sum_le_sum fun k _ => hdegree k
      _ = (keyBall6 X h r).card * 602 := by simp [Finset.sum_const]
      _ ≤ (602 ^ r) * 602 := Nat.mul_le_mul_right 602 ih
      _ = 602 ^ (r + 1) := by rw [Nat.pow_succ]

/-- A fixed-radius Hamming ball has polynomial volume in the cube dimension. -/
theorem hammingBall_card_poly_le {m r : ℕ} (t : CubeVertex m) :
    (hammingBall t r).card ≤ (r + 1) * (m + 1) ^ r := by
  classical
  let support : CubeVertex m → Finset (Fin m) := fun u =>
    Finset.univ.filter fun i => u i ≠ t i
  let B := hammingBall t r
  let Q := (Finset.univ : Finset (Finset (Fin m))).filter fun s => s.card ≤ r
  have hdist (u : CubeVertex m) : (support u).card = hammingDist t u := by
    simp [support, hammingDist, ne_comm]
  have hinj : Set.InjOn support (B : Set (CubeVertex m)) := by
    intro x hx y hy hxy
    funext i
    have hiff : x i ≠ t i ↔ y i ≠ t i := by
      have h := congrArg (fun s : Finset (Fin m) => i ∈ s) hxy
      simpa [support] using h
    cases ht : t i <;> cases hx' : x i <;> cases hy' : y i <;> simp_all
  have hsub : B.image support ⊆ Q := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    have hu' : u ∈ hammingBall t r := by simpa [B] using hu
    have hdistle : hammingDist t u ≤ r := by
      simpa [hammingBall] using (Finset.mem_filter.mp hu').2
    rw [hdist u]
    exact hdistle
  have hQbound : Q.card ≤ (r + 1) * (m + 1) ^ r := by
    have hcover : Q ⊆ (Finset.range (r + 1)).biUnion
        (fun i => (Finset.univ : Finset (Fin m)).powersetCard i) := by
      intro s hs
      have hcard := (Finset.mem_filter.mp hs).2
      refine Finset.mem_biUnion.mpr ⟨s.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hcard), ?_⟩
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩
    calc
      Q.card ≤ ((Finset.range (r + 1)).biUnion
          (fun i => (Finset.univ : Finset (Fin m)).powersetCard i)).card :=
            Finset.card_le_card hcover
      _ ≤ ∑ i ∈ Finset.range (r + 1),
          ((Finset.univ : Finset (Fin m)).powersetCard i).card := Finset.card_biUnion_le
      _ = ∑ i ∈ Finset.range (r + 1), Nat.choose m i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.card_powersetCard]
      _ ≤ ∑ _i ∈ Finset.range (r + 1), (m + 1) ^ r := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        calc
          Nat.choose m i ≤ m ^ i := Nat.choose_le_pow _ _
          _ ≤ (m + 1) ^ i := Nat.pow_le_pow_left (by omega) i
          _ ≤ (m + 1) ^ r := Nat.pow_le_pow_right (by omega) hi'
      _ = (r + 1) * (m + 1) ^ r := by simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (hammingBall t r).card = B.card := rfl
    _ = (B.image support).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Q.card := Finset.card_le_card hsub
    _ ≤ (r + 1) * (m + 1) ^ r := hQbound

/-- A coarse superset for the hidden keys queried by one odd role's short proxy row. -/
noncomputable def proxyHidScope6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M) (u : CubeVertex n) :
    Finset X.HKey :=
  keyBall6 X (X.g.L.key u) 4 ×ˢ hammingBall (X.g.L.sign u) 4

theorem keyBall6_contains_root {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M)
    (root : X.Key) : ∀ r, root ∈ keyBall6 X root r := by
  intro r
  induction r with
  | zero => simp [keyBall6]
  | succ r ih =>
      have hself : root ∈ X.C root := by
        change root ∈ keyNeighborhood6 binAdjacent6 root
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
      change root ∈ (keyBall6 X root r).biUnion X.C
      exact Finset.mem_biUnion.mpr ⟨root, ih, hself⟩

theorem target_in_proxyHidScope6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : HypercubeRamsey.TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M)
    (u : CubeVertex n) : X.tgt (X.g.L.stateOf u) ∈ proxyHidScope6 X u := by
  classical
  have hkey := X.facts.key_eq u
  have hsign := X.facts.sign_eq u
  have htgt : X.tgt (X.g.L.stateOf u) = (X.g.L.key u, X.g.L.sign u) := by
    simp [Ctx6.tgt, ChunkLayout6.stTarget, hkey, hsign]
  rw [htgt]
  apply Finset.mem_product.mpr
  constructor
  · exact keyBall6_contains_root X (X.g.L.key u) 4
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [HypercubeRamsey.hammingBall, HypercubeRamsey.hammingDist]

/-- A coarse superset for hidden keys read by a stage-3 bad group. -/
noncomputable def bad3HidScope6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M)
    (gr : X.Bin × CubeVertex X.m) : Finset X.HKey :=
  keyBall6 X (gr.1, KeyFlag6.interior) 4 ×ˢ
    hammingBall (show CubeVertex X.g.L.m from gr.2) 4

/-- Both radius-four hidden scopes have polynomial size. -/
theorem proxyHidScope6_card_le {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M) (u : CubeVertex n) :
    (proxyHidScope6 X u).card ≤ 602 ^ 4 * (5 * (X.m + 1) ^ 4) := by
  rw [proxyHidScope6, Finset.card_product]
  calc
    _ ≤ 602 ^ 4 * ((4 + 1) * (X.m + 1) ^ 4) :=
      Nat.mul_le_mul (keyBall6_card_le X (X.g.L.key u) 4)
        (hammingBall_card_poly_le (r := 4) (X.g.L.sign u))
    _ = 602 ^ 4 * (5 * (X.m + 1) ^ 4) := by norm_num

theorem bad3HidScope6_card_le {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M)
    (gr : X.Bin × CubeVertex X.m) :
    (bad3HidScope6 X gr).card ≤ 602 ^ 4 * (5 * (X.m + 1) ^ 4) := by
  rw [bad3HidScope6, Finset.card_product]
  calc
    _ ≤ 602 ^ 4 * ((4 + 1) * (X.m + 1) ^ 4) :=
      Nat.mul_le_mul (keyBall6_card_le X (gr.1, KeyFlag6.interior) 4)
        (hammingBall_card_poly_le (r := 4) (show CubeVertex X.g.L.m from gr.2))
    _ = 602 ^ 4 * (5 * (X.m + 1) ^ 4) := by norm_num

/-- Sign-separated roles have disjoint radius-four hidden scopes. -/
theorem proxyHidScope6_disjoint {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : S06.Ctx6 γ p₀ K n N E G M)
    (u u' : CubeVertex n)
    (hFar : 100 * (Nat.sqrt X.m + 1) < _root_.hammingDist (X.g.L.sign u) (X.g.L.sign u')) :
    Disjoint (proxyHidScope6 X u) (proxyHidScope6 X u') := by
  classical
  rw [Finset.disjoint_left]
  intro ℓ hℓ hℓ'
  rcases Finset.mem_product.mp hℓ with ⟨_, hsign⟩
  rcases Finset.mem_product.mp hℓ' with ⟨_, hsign'⟩
  have h1 : _root_.hammingDist (X.g.L.sign u) ℓ.2 ≤ 4 := by
    simpa [proxyHidScope6, hammingBall, _root_.hammingDist, hammingDist] using
      (Finset.mem_filter.mp hsign).2
  have h2 : _root_.hammingDist (X.g.L.sign u') ℓ.2 ≤ 4 := by
    simpa [proxyHidScope6, hammingBall, _root_.hammingDist, hammingDist] using
      (Finset.mem_filter.mp hsign').2
  have htriangle := _root_.hammingDist_triangle (X.g.L.sign u) ℓ.2 (X.g.L.sign u')
  have hcomm : _root_.hammingDist ℓ.2 (X.g.L.sign u') =
      _root_.hammingDist (X.g.L.sign u') ℓ.2 := hammingDist_comm _ _
  rw [hcomm] at htriangle
  have hsmall : _root_.hammingDist (X.g.L.sign u) (X.g.L.sign u') ≤ 8 := by omega
  have hrad : 8 < 100 * (Nat.sqrt X.m + 1) := by omega
  omega

/-- Proxy rows are nonnegative even away from the admitted-history support. -/
theorem Ctx6.proxyRow_nonneg {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (C : X.Centre) (u : CubeVertex n) (y : Fin N) :
    0 ≤ X.proxyRow H C u y := by
  unfold Ctx6.proxyRow Ctx6.oddRowAt
  by_cases hv : X.OddValid H C X.Rshort (X.g.L.stateOf u)
  · simp only [hv, if_pos]
    cases hm : X.stMode (X.g.L.stateOf u) with
    | low => exact (X.lowRow H (X.pos C) (X.g.L.stateOf u)
        (X.actDesc H C X.Rshort (X.g.L.stateOf u)) (X.tup C)).nonneg y
    | high => exact (X.s3Post H (X.g.L.stateOf u)
        (X.actDesc H C X.Rshort (X.g.L.stateOf u)) (X.tup C)).nonneg y
  · simp [hv]

/-- In a parity class with uniform signs, the roles whose signs lie in a Hamming ball
are bounded by the ball volume times the class size divided by the sign-space size. -/
theorem sign_ball_card_le {n : ℕ} {α : ℝ} (g : ChunkGeometry6 n α) (p : Bool)
    (t : CubeVertex g.L.m) (r : ℕ) :
    (((parityFiber6 (n := n) p).filter fun x => _root_.hammingDist (g.L.sign x) t ≤ r).card : ℝ) ≤
      ((hammingBall t r).card : ℝ) *
        (((parityFiber6 (n := n) p).card : ℝ) / (2 : ℝ) ^ g.L.m) := by
  let signs : Finset (CubeVertex g.L.m) := hammingBall t r
  let roles : Finset (CubeVertex n) := (parityFiber6 (n := n) p).filter
    fun x => _root_.hammingDist (g.L.sign x) t ≤ r
  have hsub : roles ⊆ signs.biUnion (fun s => signFiber6 g.L p s) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hpar, hdist⟩
    refine Finset.mem_biUnion.mpr ⟨g.L.sign x, ?_, ?_⟩
    · change g.L.sign x ∈ hammingBall t r
      rw [hammingBall]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      calc
        _root_.hammingDist t (g.L.sign x) = _root_.hammingDist (g.L.sign x) t :=
          hammingDist_comm t (g.L.sign x)
        _ ≤ r := hdist
    · simpa [signFiber6, parityFiber6] using hpar
  have hball : ((roles.card : ℕ) : ℝ) ≤
      ∑ s ∈ signs, ((signFiber6 g.L p s).card : ℝ) := by
    calc
      ((roles.card : ℕ) : ℝ) ≤
          (((signs.biUnion fun s => signFiber6 g.L p s).card : ℕ) : ℝ) := by
            exact_mod_cast (Finset.card_le_card hsub)
      _ ≤ ∑ s ∈ signs, ((signFiber6 g.L p s).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := signs)
          (t := fun s => signFiber6 g.L p s))
  have hfiber (s : CubeVertex g.L.m) :
      ((signFiber6 g.L p s).card : ℝ) =
        ((parityFiber6 (n := n) p).card : ℝ) / (2 : ℝ) ^ g.L.m := by
    have hu := g.sign_uniform p s
    have hpow : (2 : ℝ) ^ g.L.m ≠ 0 := by positivity
    calc
      ((signFiber6 g.L p s).card : ℝ) =
          (((signFiber6 g.L p s).card : ℝ) * (2 : ℝ) ^ g.L.m) /
            (2 : ℝ) ^ g.L.m := by field_simp
      _ = ((parityFiber6 (n := n) p).card : ℝ) / (2 : ℝ) ^ g.L.m := by rw [hu]
  calc
    ((roles.card : ℕ) : ℝ) ≤ ∑ s ∈ signs, ((signFiber6 g.L p s).card : ℝ) := hball
    _ = ∑ s ∈ signs,
        (((parityFiber6 (n := n) p).card : ℝ) / (2 : ℝ) ^ g.L.m) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [hfiber]
    _ = ((hammingBall t r).card : ℝ) *
        (((parityFiber6 (n := n) p).card : ℝ) / (2 : ℝ) ^ g.L.m) := by
          simp [signs, Finset.sum_const, nsmul_eq_mul]

/-- A sign ball occupies a `2 * ball / 2^m` fraction of the full role cube. -/
theorem sign_near_card_le {n : ℕ} {α : ℝ} (g : ChunkGeometry6 n α)
    (t : CubeVertex g.L.m) (r : ℕ) :
    (((Finset.univ : Finset (CubeVertex n)).filter
      fun x => _root_.hammingDist (g.L.sign x) t ≤ r).card : ℝ) ≤
      (2 * (hammingBall t r).card / (2 : ℝ) ^ g.L.m) * (2 : ℝ) ^ n := by
  let near : Finset (CubeVertex n) := Finset.univ.filter
    fun x => _root_.hammingDist (g.L.sign x) t ≤ r
  have hsplit : near.card = (near.filter IsEvenRole).card +
      (near.filter fun x => ¬ IsEvenRole x).card := by
    simpa using (Finset.card_filter_add_card_filter_not (s := near) IsEvenRole).symm
  have heven : ((near.filter IsEvenRole).card : ℝ) ≤
      ((hammingBall t r).card : ℝ) *
        (((parityFiber6 (n := n) true).card : ℝ) / (2 : ℝ) ^ g.L.m) := by
    have h := sign_ball_card_le g true t r
    simpa [near, parityFiber6, Finset.filter_filter, and_comm, and_left_comm, and_assoc] using h
  have hodd : ((near.filter fun x => ¬ IsEvenRole x).card : ℝ) ≤
      ((hammingBall t r).card : ℝ) *
        (((parityFiber6 (n := n) false).card : ℝ) / (2 : ℝ) ^ g.L.m) := by
    have h := sign_ball_card_le g false t r
    simpa [near, parityFiber6, Finset.filter_filter, and_comm, and_left_comm, and_assoc] using h
  have hpar (p : Bool) : ((parityFiber6 (n := n) p).card : ℝ) ≤ (2 : ℝ) ^ n := by
    calc
      ((parityFiber6 (n := n) p).card : ℝ) ≤ (Fintype.card (CubeVertex n) : ℝ) := by
        exact_mod_cast Finset.card_le_univ (parityFiber6 (n := n) p)
      _ = (2 : ℝ) ^ n := by simp
  have hpow : 0 < (2 : ℝ) ^ g.L.m := by positivity
  have hball0 : 0 ≤ ((hammingBall t r).card : ℝ) := by positivity
  have hE : ((near.filter IsEvenRole).card : ℝ) ≤
      ((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ g.L.m := by
    calc
      _ ≤ ((hammingBall t r).card : ℝ) *
          (((parityFiber6 (n := n) true).card : ℝ) / (2 : ℝ) ^ g.L.m) := heven
      _ = (((hammingBall t r).card : ℝ) *
          ((parityFiber6 (n := n) true).card : ℝ)) / (2 : ℝ) ^ g.L.m := by ring
      _ ≤ (((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n) / (2 : ℝ) ^ g.L.m :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hpar true) hball0) hpow.le
      _ = ((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ g.L.m := rfl
  have hO : ((near.filter fun x => ¬ IsEvenRole x).card : ℝ) ≤
      ((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ g.L.m := by
    calc
      _ ≤ ((hammingBall t r).card : ℝ) *
          (((parityFiber6 (n := n) false).card : ℝ) / (2 : ℝ) ^ g.L.m) := hodd
      _ = (((hammingBall t r).card : ℝ) *
          ((parityFiber6 (n := n) false).card : ℝ)) / (2 : ℝ) ^ g.L.m := by ring
      _ ≤ (((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n) / (2 : ℝ) ^ g.L.m :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hpar false) hball0) hpow.le
      _ = ((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ g.L.m := rfl
  have hnear : (near.card : ℝ) ≤
      2 * ((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ g.L.m := by
    calc
      (near.card : ℝ) = (near.filter IsEvenRole).card +
          (near.filter fun x => ¬ IsEvenRole x).card := by exact_mod_cast hsplit
      _ ≤ ((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ g.L.m +
          ((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ g.L.m := add_le_add hE hO
      _ = 2 * ((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ g.L.m := by ring
  dsimp [near] at hnear ⊢
  calc
    _ ≤ 2 * ((hammingBall t r).card : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ g.L.m := hnear
    _ = (2 * (hammingBall t r).card / (2 : ℝ) ^ g.L.m) * (2 : ℝ) ^ n := by ring

/-- Once the number of fine chunks is large, a sign ball is small enough for the
low-row moment cap, uniformly whenever `m ≥ n^α`. -/
theorem sign_moment_parameters (α : ℝ) (hα : 0 < α) :
    ∃ m₀ : ℕ, ∀ n m : ℕ, m₀ ≤ m → (n : ℝ) ^ α ≤ (m : ℝ) →
      let r : ℕ := 100 * (Nat.sqrt m + 1)
      r ≤ m / 2 ∧ ((r : ℝ) / (m : ℝ) ≤ 1 / 4) ∧
        20 ≤ Nat.floor ((m : ℝ) ^ (1 / 25 : ℝ)) ∧
        (n : ℝ) *
          (2 * Real.exp (Real.binEntropy (1 / 4 : ℝ) * m) / (2 : ℝ) ^ m) *
            Real.exp ((m : ℝ) ^ (15 / 100 : ℝ)) ≤ 1 := by
  let gap : ℝ := Real.log 2 - Real.binEntropy (1 / 4 : ℝ)
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr (Real.binEntropy_lt_log_two.mpr (by norm_num))
  let s : ℝ := α⁻¹
  have hs : 0 < s := by dsimp [s]; exact inv_pos.mpr hα
  have hpowDecay :
      Tendsto (fun m : ℕ => (m : ℝ) ^ (- (85 / 100 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 85 / 100)).comp
      tendsto_natCast_atTop_atTop
  have hpowGrowth :
      Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / 25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 25)).comp
      tendsto_natCast_atTop_atTop
  have hexpSmall :
      Tendsto (fun m : ℕ => (m : ℝ) ^ s * Real.exp (- (gap / 2) * (m : ℝ)))
        atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s (gap / 2)
      (by positivity)).comp tendsto_natCast_atTop_atTop
  have eLarge : ∀ᶠ m : ℕ in atTop, (1 : ℝ) ≤ (m : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with m hm
    exact_mod_cast hm
  have eSqrt : ∀ᶠ m : ℕ in atTop, (1000000 : ℝ) ≤ (m : ℝ) := by
    exact (tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (1000000 : ℝ)))
  have eGrowth : ∀ᶠ m : ℕ in atTop, 21 ≤ (m : ℝ) ^ (1 / 25 : ℝ) :=
    hpowGrowth.eventually (Filter.eventually_ge_atTop (21 : ℝ))
  have eDecay : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ (- (85 / 100 : ℝ)) ≤ gap / 2 := by
    exact hpowDecay.eventually (Iic_mem_nhds (by positivity : (0 : ℝ) < gap / 2))
  have eExp : ∀ᶠ m : ℕ in atTop,
      2 * (m : ℝ) ^ s * Real.exp (- (gap / 2) * (m : ℝ)) ≤ 1 := by
    exact hexpSmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)) |>.mono
      (fun m hm => by linarith)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1
    (eLarge.and (eSqrt.and (eGrowth.and (eDecay.and eExp))))
  refine ⟨m₀, ?_⟩
  intro n m hm hnm
  rcases hm₀ m hm with ⟨hmOne, hmHuge, hmPower, hmDecay, hmTail⟩
  have hsqrt : (Nat.sqrt m : ℝ) ≤ Real.sqrt (m : ℝ) := nat_sqrt_le_real_sqrt
  have hsqrtm : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hmOne
  have hradiusReal : (100 * (Nat.sqrt m + 1 : ℕ) : ℝ) ≤ 200 * Real.sqrt (m : ℝ) := by
    push_cast
    nlinarith [hsqrt]
  have hsqrtLarge : 800 ≤ Real.sqrt (m : ℝ) := by
    have hmNat : 1000000 ≤ m := by exact_mod_cast hmHuge
    have h800 : (800 : ℝ) ^ 2 ≤ (m : ℝ) := by
      have hm640 : 640000 ≤ m := by omega
      exact_mod_cast hm640
    calc
      (800 : ℝ) = Real.sqrt ((800 : ℝ) ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt h800
  have hradiusFrac :
      (100 * (Nat.sqrt m + 1 : ℕ) : ℝ) / (m : ℝ) ≤ 1 / 4 := by
    have hmpos : 0 < (m : ℝ) := by positivity
    rw [div_le_iff₀ hmpos]
    have hsqrtSq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = m := by
      rw [Real.mul_self_sqrt (by positivity)]
    calc
      (100 * (Nat.sqrt m + 1 : ℕ) : ℝ) ≤ 200 * Real.sqrt (m : ℝ) := hradiusReal
      _ ≤ (1 / 4 : ℝ) * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by
        nlinarith [hsqrtLarge]
      _ = (1 / 4 : ℝ) * m := by rw [hsqrtSq]
  have hradius : 100 * (Nat.sqrt m + 1) ≤ m / 2 := by
    have htwiceReal : (2 : ℝ) * (100 * (Nat.sqrt m + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
      have hmpos : 0 < (m : ℝ) := by positivity
      have h := (div_le_iff₀ hmpos).mp hradiusFrac
      nlinarith
    have htwiceNat : 2 * (100 * (Nat.sqrt m + 1)) ≤ m := by exact_mod_cast htwiceReal
    omega
  have hJreal : 21 ≤ (m : ℝ) ^ (1 / 25 : ℝ) := by
    exact hmPower
  have hJ : 20 ≤ Nat.floor ((m : ℝ) ^ (1 / 25 : ℝ)) := by
    have := Nat.floor_mono hJreal
    norm_num at this ⊢
    omega
  have hmpos : 0 < (m : ℝ) := by positivity
  have hdecay : (m : ℝ) ^ (- (85 / 100 : ℝ)) ≤ gap / 2 := hmDecay
  have hcap : (m : ℝ) ^ (15 / 100 : ℝ) ≤ (gap / 2) * (m : ℝ) := by
    have heq : (m : ℝ) ^ (15 / 100 : ℝ) =
        (m : ℝ) * (m : ℝ) ^ (- (85 / 100 : ℝ)) := by
      calc
        (m : ℝ) ^ (15 / 100 : ℝ) = (m : ℝ) ^ (1 : ℝ) *
            (m : ℝ) ^ (- (85 / 100 : ℝ)) := by
              rw [← Real.rpow_add hmpos]
              congr 1 <;> norm_num
        _ = (m : ℝ) * (m : ℝ) ^ (- (85 / 100 : ℝ)) := by rw [Real.rpow_one]
    rw [heq]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hdecay hmpos.le
  have hpowN : (n : ℝ) ≤ (m : ℝ) ^ s := by
    by_cases hn0 : n = 0
    · subst n
      simpa using (Real.rpow_nonneg (Nat.cast_nonneg m) s)
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    have hmono := Real.rpow_le_rpow (by positivity : 0 ≤ (n : ℝ) ^ α) hnm (le_of_lt hs)
    have hmul : α * s = 1 := by dsimp [s]; field_simp
    calc
      (n : ℝ) = ((n : ℝ) ^ α) ^ s := by
        rw [← Real.rpow_mul hnpos.le, hmul, Real.rpow_one]
      _ ≤ (m : ℝ) ^ s := hmono
  have htail : 2 * (m : ℝ) ^ s * Real.exp (- (gap / 2) * (m : ℝ)) ≤ 1 := hmTail
  have htwo : (2 : ℝ) ^ m = Real.exp (Real.log 2 * (m : ℝ)) := by
    calc
      (2 : ℝ) ^ m = (Real.exp (Real.log 2)) ^ m := by rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((m : ℝ) * Real.log 2) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (Real.log 2 * (m : ℝ)) := by congr 1 <;> ring
  have hball : (hammingBall (fun _ => false : CubeVertex m)
      (100 * (Nat.sqrt m + 1))).card ≤
        Real.exp (Real.binEntropy
          (((100 * (Nat.sqrt m + 1) : ℕ) : ℝ) / (m : ℝ)) * (m : ℝ)) := by
    apply hammingBall_volume_bound (v := fun _ => false)
    · omega
    · exact hradius
  have hq : (((100 * (Nat.sqrt m + 1) : ℕ) : ℝ) / (m : ℝ)) ≤ 1 / 4 := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hradiusFrac
  have hqmem : (((100 * (Nat.sqrt m + 1) : ℕ) : ℝ) / (m : ℝ)) ∈ Set.Icc 0 (2⁻¹ : ℝ) :=
    ⟨by positivity, by linarith⟩
  have hquarter : (1 / 4 : ℝ) ∈ Set.Icc 0 (2⁻¹ : ℝ) := by norm_num
  have hEntropy := Real.binEntropy_strictMonoOn.monotoneOn hqmem hquarter hq
  have hball' : ((hammingBall (fun _ => false : CubeVertex m)
      (100 * (Nat.sqrt m + 1))).card : ℝ) ≤
        Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) := by
    calc
      _ ≤ Real.exp (Real.binEntropy
          (((100 * (Nat.sqrt m + 1) : ℕ) : ℝ) / (m : ℝ)) * (m : ℝ)) := hball
      _ ≤ Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hEntropy (by positivity)
  have hpowPos : 0 < (2 : ℝ) ^ m := by positivity
  have hratio :
      2 * (hammingBall (fun _ => false : CubeVertex m)
        (100 * (Nat.sqrt m + 1))).card / (2 : ℝ) ^ m ≤
        2 * Real.exp (-gap * (m : ℝ)) := by
    calc
      _ ≤ 2 * Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) /
          (2 : ℝ) ^ m := by
        apply div_le_div_of_nonneg_right ?_ hpowPos.le
        exact mul_le_mul_of_nonneg_left hball' (by norm_num)
      _ = 2 * (Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) /
          Real.exp (Real.log 2 * (m : ℝ))) := by rw [htwo]; ring
      _ = 2 * Real.exp (-gap * (m : ℝ)) := by
        have hExp : Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) /
            Real.exp (Real.log 2 * (m : ℝ)) = Real.exp (-gap * (m : ℝ)) := by
          rw [← Real.exp_sub]
          congr 1
          dsimp [gap]
          ring
        rw [hExp]
  have hEntropyRatio :
      2 * Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) / (2 : ℝ) ^ m =
        2 * Real.exp (-gap * (m : ℝ)) := by
    rw [htwo]
    have hExp : Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) /
        Real.exp (Real.log 2 * (m : ℝ)) = Real.exp (-gap * (m : ℝ)) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [gap]
      ring
    calc
      _ = 2 * (Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) /
          Real.exp (Real.log 2 * (m : ℝ))) := by ring
      _ = 2 * Real.exp (-gap * (m : ℝ)) := by rw [hExp]
  have htarget : (n : ℝ) *
      (2 * Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) / (2 : ℝ) ^ m) *
        Real.exp ((m : ℝ) ^ (15 / 100 : ℝ)) ≤ 1 := by
    calc
      _ = ((n : ℝ) * (2 * Real.exp (Real.binEntropy (1 / 4 : ℝ) * (m : ℝ)) /
          (2 : ℝ) ^ m)) * Real.exp ((m : ℝ) ^ (15 / 100 : ℝ)) := by ring
      _ = (2 * (n : ℝ) * Real.exp (-gap * (m : ℝ))) *
          Real.exp ((m : ℝ) ^ (15 / 100 : ℝ)) := by
        rw [hEntropyRatio]
        ring
      _ = 2 * (n : ℝ) * Real.exp (-gap * (m : ℝ) + (m : ℝ) ^ (15 / 100 : ℝ)) := by
        calc
          _ = 2 * (n : ℝ) *
              (Real.exp (-gap * (m : ℝ)) * Real.exp ((m : ℝ) ^ (15 / 100 : ℝ))) := by ring
          _ = _ := by rw [← Real.exp_add]
      _ ≤ 2 * (n : ℝ) * Real.exp (- (gap / 2) * (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [hcap]
      _ ≤ 2 * (m : ℝ) ^ s * Real.exp (- (gap / 2) * (m : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_right hpowN (Real.exp_nonneg (- (gap / 2) * (m : ℝ)))
        calc
          _ = 2 * ((n : ℝ) * Real.exp (- (gap / 2) * (m : ℝ))) := by ring
          _ ≤ 2 * ((m : ℝ) ^ s * Real.exp (- (gap / 2) * (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
          _ = _ := by ring
      _ ≤ 1 := htail
  exact ⟨hradius, (by simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hradiusFrac), hJ, htarget⟩

/-- The label-union remainder is below one percent from dimension ten onward. -/
theorem nat_two_pow_union_tail {n : ℕ} (hn : 10 ≤ n) :
    (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n ≤ 1 / 100 := by
  have hpow : ∀ k : ℕ, 10 ≤ k → 100 * k ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
        have hstep : 100 * (k + 1) ≤ 2 * (100 * k) := by omega
        calc
          100 * (k + 1) ≤ 2 * (100 * k) := hstep
          _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hpowReal : 100 * (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hpow n hn
  have hfour : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    calc
      (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by norm_num
      _ = (2 : ℝ) ^ (2 * n) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (n + n) := by congr 1 <;> omega
      _ = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [pow_add]
  have hEq : (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n =
      (n : ℝ) / (2 : ℝ) ^ n := by
    rw [div_pow, one_pow, hfour]
    field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
    <;> ring
  rw [hEq]
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).2
  nlinarith

end Lane_q_s06_loads
end HypercubeRamsey

namespace Lane_q_s06_loads

/-- A scope-local weight is independent of avoidance constraints with disjoint scopes under a product law. -/
theorem product_weight_avoid_factor {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : ∀ v, α v → ℝ) (hq0 : ∀ v a, 0 ≤ q v a) (hq1 : ∀ v, ∑ a, q v a = 1)
    (E : I → Finset (∀ v, α v)) (scope : I → Finset V)
    (hscope : ∀ i (ω ω' : ∀ v, α v), (∀ v ∈ scope i, ω v = ω' v) →
      (ω ∈ E i ↔ ω' ∈ E i))
    (U : Finset V) (W : (∀ v, α v) → ℝ)
    (hW : ∀ ω ω', (∀ v ∈ U, ω v = ω' v) → W ω = W ω')
    (S : Finset I) (hS : ∀ i ∈ S, Disjoint U (scope i)) :
    (∑ ω ∈ HypercubeRamsey.LocalLemma.avoid E S, (∏ v, q v (ω v)) * W ω) =
      (∑ ω, (∏ v, q v (ω v)) * W ω) *
        HypercubeRamsey.LocalLemma.mass (fun ω => ∏ v, q v (ω v))
          (HypercubeRamsey.LocalLemma.avoid E S) := by
  classical
  let w : (∀ v, α v) → ℝ := fun ω => ∏ v, q v (ω v)
  let levels : Finset ℝ := Finset.univ.image W
  let levelEvent (t : ℝ) : Finset (∀ v, α v) :=
    Finset.univ.filter fun ω => W ω = t
  have hlevelSum (ω : ∀ v, α v) :
      (∑ t ∈ levels, if W ω = t then t else 0) = W ω := by
    rw [Finset.sum_eq_single (W ω)]
    · simp
    · intro t ht hne
      simp only [if_neg (fun heq : W ω = t => hne heq.symm)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩))
  have hweightSum (A : Finset (∀ v, α v)) :
      (∑ ω ∈ A, w ω * W ω) =
        ∑ t ∈ levels, t * HypercubeRamsey.LocalLemma.mass w (levelEvent t ∩ A) := by
    calc
      (∑ ω ∈ A, w ω * W ω) =
          ∑ ω ∈ A, ∑ t ∈ levels, if W ω = t then w ω * t else 0 := by
            apply Finset.sum_congr rfl
            intro ω hω
            calc
              w ω * W ω = w ω * (∑ t ∈ levels, if W ω = t then t else 0) := by
                congr 1
                exact (hlevelSum ω).symm
              _ = ∑ t ∈ levels, if W ω = t then w ω * t else 0 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro t ht
                by_cases h : W ω = t <;> simp [h]
      _ = ∑ t ∈ levels, ∑ ω ∈ A, if W ω = t then w ω * t else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ t ∈ levels, t * HypercubeRamsey.LocalLemma.mass w (levelEvent t ∩ A) := by
            apply Finset.sum_congr rfl
            intro t ht
            have hfilter : A.filter (fun ω => W ω = t) = levelEvent t ∩ A := by
              ext ω
              simp [levelEvent, and_comm]
            calc
              (∑ ω ∈ A, if W ω = t then w ω * t else 0) =
                  ∑ ω ∈ A.filter (fun ω => W ω = t), w ω * t := by
                    rw [← Finset.sum_filter]
              _ = (∑ ω ∈ A.filter (fun ω => W ω = t), w ω) * t := by
                    rw [Finset.sum_mul]
              _ = t * HypercubeRamsey.LocalLemma.mass w (levelEvent t ∩ A) := by
                  rw [HypercubeRamsey.LocalLemma.mass, hfilter]
                  ring
  let Level := {t : ℝ // t ∈ levels}
  let Id' := I ⊕ Level
  let E' : Id' → Finset (∀ v, α v) := Sum.elim E (fun t => levelEvent t.1)
  let scope' : Id' → Finset V := Sum.elim scope (fun _ => U)
  let S' : Finset Id' := S.image (Sum.inl : I → Id')
  have hscope' : ∀ i (ω ω' : ∀ v, α v), (∀ v ∈ scope' i, ω v = ω' v) →
      (ω ∈ E' i ↔ ω' ∈ E' i) := by
    intro i ω ω' heq
    cases i with
    | inl j =>
        apply hscope j ω ω'
        intro v hv
        exact heq v (by simp [scope', hv])
    | inr t =>
        have hval : W ω = W ω' := hW ω ω' (by
          intro v hv
          exact heq v (by simp [scope', hv]))
        dsimp [E', levelEvent]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact hval.symm.trans h
        · intro h
          exact hval.trans h
  have havoid' : HypercubeRamsey.LocalLemma.avoid E' S' =
      HypercubeRamsey.LocalLemma.avoid E S := by
    ext ω
    simp only [HypercubeRamsey.LocalLemma.avoid, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h i hi
      have hmem : Sum.inl i ∈ S' := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      exact h (Sum.inl i) hmem
    · intro h i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact h j hj
  have hlocalFactor (t : Level) :
      HypercubeRamsey.LocalLemma.mass w (levelEvent t.1 ∩
        HypercubeRamsey.LocalLemma.avoid E S) =
        HypercubeRamsey.LocalLemma.mass w (levelEvent t.1) *
          HypercubeRamsey.LocalLemma.mass w (HypercubeRamsey.LocalLemma.avoid E S) := by
    have hdis : ∀ j ∈ S', Disjoint (scope' (Sum.inr t)) (scope' j) := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      change Disjoint U (scope i)
      exact hS i hi
    have h := HypercubeRamsey.LocalLemma.mass_inter_avoid_of_disjoint_scopes q hq0 hq1 E' scope'
      hscope' (Sum.inr t) S' hdis
    rw [havoid'] at h
    simpa [E', levelEvent] using h
  have havoidSum := hweightSum (HypercubeRamsey.LocalLemma.avoid E S)
  have hrawSum := hweightSum Finset.univ
  have hrawSum' : (∑ ω, w ω * W ω) =
      ∑ t ∈ levels, t * HypercubeRamsey.LocalLemma.mass w (levelEvent t) := by
    simpa [HypercubeRamsey.LocalLemma.mass] using hrawSum
  have hfactorSum :
      (∑ t ∈ levels, t * HypercubeRamsey.LocalLemma.mass w
          (levelEvent t ∩ HypercubeRamsey.LocalLemma.avoid E S)) =
        (∑ t ∈ levels, t * HypercubeRamsey.LocalLemma.mass w (levelEvent t)) *
          HypercubeRamsey.LocalLemma.mass w (HypercubeRamsey.LocalLemma.avoid E S) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hlocalFactor ⟨t, ht⟩]
    ring
  calc
    (∑ ω ∈ HypercubeRamsey.LocalLemma.avoid E S, w ω * W ω) =
        (∑ t ∈ levels, t * HypercubeRamsey.LocalLemma.mass w
          (levelEvent t ∩ HypercubeRamsey.LocalLemma.avoid E S)) := havoidSum
    _ = (∑ t ∈ levels, t * HypercubeRamsey.LocalLemma.mass w (levelEvent t)) *
          HypercubeRamsey.LocalLemma.mass w (HypercubeRamsey.LocalLemma.avoid E S) := hfactorSum
    _ = (∑ ω, (∏ v, q v (ω v)) * W ω) *
          HypercubeRamsey.LocalLemma.mass (fun ω => ∏ v, q v (ω v))
            (HypercubeRamsey.LocalLemma.avoid E S) := by
          exact congrArg (fun z : ℝ => z *
            HypercubeRamsey.LocalLemma.mass w (HypercubeRamsey.LocalLemma.avoid E S)) hrawSum'.symm

end Lane_q_s06_loads

namespace Lane_q_s06_loads

/-- Positive mass of avoiding any subset follows by monotonicity from full avoidance. -/
theorem avoid_mass_positive_subset {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [DecidableEq I] {w : Ω → ℝ} {E : I → Finset Ω} {xmax : ℝ}
    (cert : HypercubeRamsey.S06.AvoidCert6 w E xmax)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (hxmax : xmax < 1) (S : Finset I) :
    0 < HypercubeRamsey.LocalLemma.mass w (HypercubeRamsey.LocalLemma.avoid E S) := by
  classical
  have hfull : 0 < HypercubeRamsey.LocalLemma.mass w
      (HypercubeRamsey.LocalLemma.avoid E Finset.univ) :=
    HypercubeRamsey.Lane_q_s06_loads.S06.AvoidCert6.mass_avoid_pos cert hw hw1 hxmax
  have hsub : HypercubeRamsey.LocalLemma.avoid E Finset.univ ⊆
      HypercubeRamsey.LocalLemma.avoid E S := by
    intro ω hω
    have hall : ∀ i ∈ Finset.univ, ω ∉ E i := by
      simpa [HypercubeRamsey.LocalLemma.avoid] using hω
    have hs : ∀ i ∈ S, ω ∉ E i := fun i hi => hall i (Finset.mem_univ _)
    simpa [HypercubeRamsey.LocalLemma.avoid] using hs
  have hmono : HypercubeRamsey.LocalLemma.mass w
      (HypercubeRamsey.LocalLemma.avoid E Finset.univ) ≤
        HypercubeRamsey.LocalLemma.mass w (HypercubeRamsey.LocalLemma.avoid E S) := by
    unfold HypercubeRamsey.LocalLemma.mass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ => hw ω
  exact lt_of_lt_of_le hfull hmono

/-- Products of functions on pairwise disjoint coordinate scopes factor under a product law. -/
theorem pi_expect_prod_pairwise_disjoint {ι U : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype U] [DecidableEq U] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinProb (Ω i)) (s : Finset U) (scope : U → Finset ι)
    (f : U → (∀ i, Ω i) → ℝ)
    (hf : ∀ u, HypercubeRamsey.FinProb.DependsOn (f u) (scope u))
    (hdis : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (scope u) (scope v)) :
    (HypercubeRamsey.FinProb.pi P).expect (fun ω => ∏ u ∈ s, f u ω) =
      ∏ u ∈ s, (HypercubeRamsey.FinProb.pi P).expect (f u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HypercubeRamsey.FinProb.expect_const]
  | @insert u s hu ih =>
      let g : (∀ i, Ω i) → ℝ := fun ω => ∏ v ∈ s, f v ω
      have hg : HypercubeRamsey.FinProb.DependsOn g (s.biUnion scope) := by
        intro ω ω' heq
        apply Finset.prod_congr rfl
        intro v hv
        apply hf v
        intro i hi
        exact heq i (Finset.mem_biUnion.mpr ⟨v, hv, hi⟩)
      have hdu : Disjoint (scope u) (s.biUnion scope) := by
        apply Finset.disjoint_left.mpr
        intro i hiU hiS
        rcases Finset.mem_biUnion.mp hiS with ⟨v, hv, hvi⟩
        have huv : u ≠ v := by
          intro h
          subst v
          exact hu hv
        exact Finset.disjoint_left.mp (hdis u (Finset.mem_insert_self _ _) v
          (Finset.mem_insert_of_mem hv) huv) hiU hvi
      have hmul := HypercubeRamsey.FinProb.pi_expect_mul_of_disjoint P (f u) g
        (scope u) (s.biUnion scope) (hf u) hg hdu
      have hpair : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → Disjoint (scope v) (scope w) := by
        intro v hv w hw hvw
        exact hdis v (Finset.mem_insert_of_mem hv) w (Finset.mem_insert_of_mem hw) hvw
      have hrec := ih hpair
      have hpoint (ω : ∀ i, Ω i) :
          (∏ v ∈ insert u s, f v ω) = f u ω * g ω := by
        rw [Finset.prod_insert hu]
      have hfun : (fun ω => ∏ v ∈ insert u s, f v ω) = (fun ω => f u ω * g ω) :=
        funext hpoint
      rw [hfun, Finset.prod_insert hu]
      calc
        (HypercubeRamsey.FinProb.pi P).expect (fun ω => f u ω * g ω) =
            (HypercubeRamsey.FinProb.pi P).expect (f u) *
              (HypercubeRamsey.FinProb.pi P).expect g := hmul
        _ = (HypercubeRamsey.FinProb.pi P).expect (f u) *
            ∏ v ∈ s, (HypercubeRamsey.FinProb.pi P).expect (f v) := by
            rw [← hrec]

end Lane_q_s06_loads

namespace Lane_q_s06_loads

/-- A local nonnegative weight under certified avoidance costs only the charges touching its scope. -/
theorem conditional_avoid_product_local {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : ∀ v, α v → ℝ) (hq0 : ∀ v a, 0 ≤ q v a) (hq1 : ∀ v, ∑ a, q v a = 1)
    (E : I → Finset (∀ v, α v)) (scope : I → Finset V)
    (hscope : ∀ i (ω ω' : ∀ v, α v), (∀ v ∈ scope i, ω v = ω' v) →
      (ω ∈ E i ↔ ω' ∈ E i))
    (xmax : ℝ) (cert : HypercubeRamsey.S06.AvoidCert6 (fun ω => ∏ v, q v (ω v)) E xmax)
    (hxmax : xmax < 1) (U : Finset V) (W : (∀ v, α v) → ℝ)
    (hW : ∀ ω ω', (∀ v ∈ U, ω v = ω' v) → W ω = W ω')
    (hW0 : ∀ ω, 0 ≤ W ω) (S T : Finset I) (hST : Disjoint S T)
    (hS : ∀ i ∈ S, Disjoint U (scope i)) :
    (∑ ω ∈ HypercubeRamsey.LocalLemma.avoid E (S ∪ T),
        (∏ v, q v (ω v)) * W ω) /
      HypercubeRamsey.LocalLemma.mass (fun ω => ∏ v, q v (ω v))
        (HypercubeRamsey.LocalLemma.avoid E (S ∪ T)) ≤
      (∏ i ∈ T, (1 - cert.x i))⁻¹ *
        (∑ ω, (∏ v, q v (ω v)) * W ω) := by
  classical
  let w : (∀ v, α v) → ℝ := fun ω => ∏ v, q v (ω v)
  have hw : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact Finset.prod_nonneg fun v _ => hq0 v (ω v)
  have hw1 : ∑ ω, w ω = 1 := by
    simpa [w] using (HypercubeRamsey.LocalLemma.sum_prod_weights q hq1)
  let p : I → ℝ := fun i =>
    cert.x i * ∏ j ∈ Finset.univ.filter (cert.adj i), (1 - cert.x j)
  have hx0 : ∀ i, 0 ≤ cert.x i := cert.x_nonneg
  have hx1 : ∀ i, cert.x i < 1 := fun i => (cert.x_le i).trans_lt hxmax
  have hpx : ∀ i, p i ≤ cert.x i *
      ∏ j ∈ Finset.univ.filter (cert.adj i), (1 - cert.x j) := by
    intro i
    rfl
  have havoid := HypercubeRamsey.LocalLemma.conditional_avoidance w hw hw1 E cert.adj
    cert.adj_symm cert.adj_irrefl p cert.x cert.local_bound hx0 hx1 hpx
  have hcompare := havoid.2.2.1 S T hST W hW0
  have hfactor := product_weight_avoid_factor q hq0 hq1 E scope hscope U W hW S hS
  have hmassPos := avoid_mass_positive_subset
    cert hw hw1 hxmax S
  have hratio :
      (∑ ω ∈ HypercubeRamsey.LocalLemma.avoid E S, w ω * W ω) /
          HypercubeRamsey.LocalLemma.mass w (HypercubeRamsey.LocalLemma.avoid E S) =
        ∑ ω, w ω * W ω := by
    rw [hfactor]
    have hne : HypercubeRamsey.LocalLemma.mass w
        (HypercubeRamsey.LocalLemma.avoid E S) ≠ 0 := ne_of_gt hmassPos
    field_simp [hne]
    <;> ring
  calc
    (∑ ω ∈ HypercubeRamsey.LocalLemma.avoid E (S ∪ T), w ω * W ω) /
        HypercubeRamsey.LocalLemma.mass w
          (HypercubeRamsey.LocalLemma.avoid E (S ∪ T)) ≤
      (∏ i ∈ T, (1 - cert.x i))⁻¹ *
        ((∑ ω ∈ HypercubeRamsey.LocalLemma.avoid E S, w ω * W ω) /
          HypercubeRamsey.LocalLemma.mass w (HypercubeRamsey.LocalLemma.avoid E S)) := hcompare
    _ = (∏ i ∈ T, (1 - cert.x i))⁻¹ * (∑ ω, w ω * W ω) := by rw [hratio]

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

/-- Hidden agreement on a product's observation list preserves its tag weight. -/
theorem tagWeight_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M)
    (b : X.Base) (Z Z' : X.Hid) (β : X.Ty) (S : Finset X.HKey) (i : X.ι)
    (hS : S ⊆ β.obs) (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.tagWeight (b, Z) β S i = X.tagWeight (b, Z') β S i := by
  classical
  unfold Ctx6.tagWeight
  have hprod :
      (∏ ℓ ∈ S, safeRatio6 ((X.hidPostRep b ℓ.1 β.key i).w (Z ℓ))
        ((X.hidPostDel b ℓ.1 β.key).w (Z ℓ))) =
      ∏ ℓ ∈ S, safeRatio6 ((X.hidPostRep b ℓ.1 β.key i).w (Z' ℓ))
        ((X.hidPostDel b ℓ.1 β.key).w (Z' ℓ)) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [hobs ℓ (hS hℓ)]
  rw [hprod]

theorem tagPost_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.Base) (Z Z' : X.Hid)
    (β : X.Ty) (S : Finset X.HKey) (hS : S ⊆ β.obs)
    (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.tagPost (b, Z) β S = X.tagPost (b, Z') β S := by
  classical
  change Ctx6.tagPost X (b, Z) β S = Ctx6.tagPost X (b, Z') β S
  unfold Ctx6.tagPost
  congr 1
  funext i
  exact tagWeight_congr_hid X b Z Z' β S i hS hobs

theorem Tβ_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M)
    (b : X.Base) (Z Z' : X.Hid) (β : X.Ty)
    (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.Tβ (b, Z) β = X.Tβ (b, Z') β := by
  classical
  exact tagPost_congr_hid X b Z Z' β β.obs (by intro ℓ hℓ; exact hℓ) hobs

/-- The product-label support test depends on a history only through values of its named variables. -/
theorem reqNbhd_congr_varVal {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M)
    (H H' : X.Hist) (S : Finset X.Name)
    (hval : ∀ nm ∈ S, X.varVal H nm = X.varVal H' nm) :
    X.reqNbhd H S = X.reqNbhd H' S := by
  classical
  ext y
  simp only [Ctx6.reqNbhd, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h nm hnm
    exact (by simpa only [hval nm hnm] using h nm hnm)
  · intro h nm hnm
    exact (by simpa only [(hval nm hnm).symm] using h nm hnm)

theorem labelLaw_congr_varVal {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M)
    (H H' : X.Hist) (S : Finset X.Name) (i : X.ι)
    (hval : ∀ nm ∈ S, X.varVal H nm = X.varVal H' nm) :
    X.labelLaw H S i = X.labelLaw H' S i := by
  unfold Ctx6.labelLaw
  rw [reqNbhd_congr_varVal X H H' S hval]

private theorem finProb_ext {Ω : Type*} [Fintype Ω]
    {P Q : HypercubeRamsey.FinProb Ω} (hw : ∀ ω, P.w ω = Q.w ω) : P = Q := by
  cases P with
  | mk pw pnon psum =>
      cases Q with
      | mk qw qnon qsum =>
          have hfun : pw = qw := funext hw
          subst qw
          cases Subsingleton.elim pnon qnon
          cases Subsingleton.elim psum qsum
          rfl

theorem tupleLawOn_congr_varVal {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M)
    (H H' : X.Hist) (S : Finset X.Name) (T : HypercubeRamsey.FinProb X.ι)
    (hval : ∀ nm ∈ S, X.varVal H nm = X.varVal H' nm) :
    X.tupleLawOn H S T = X.tupleLawOn H' S T := by
  classical
  have hlabel (i : X.ι) : X.labelLaw H S i = X.labelLaw H' S i :=
    labelLaw_congr_varVal X H H' S i hval
  have hkernel (i : X.ι) :
      HypercubeRamsey.FinProb.pi (fun _ : Fin X.k => X.labelLaw H S i) =
        HypercubeRamsey.FinProb.pi (fun _ : Fin X.k => X.labelLaw H' S i) := by
    congr 1
    funext r
    exact hlabel i
  apply finProb_ext
  intro o
  simp [Ctx6.tupleLawOn, HypercubeRamsey.FinProb.bind, hkernel]

theorem tupleLaw_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M)
    (b : X.Base) (Z Z' : X.Hid) (β : X.Ty)
    (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.tupleLaw (b, Z) β = X.tupleLaw (b, Z') β := by
  classical
  have hT := Tβ_congr_hid X b Z Z' β hobs
  have hval : ∀ nm ∈ reqNames6 β,
      X.varVal (b, Z) nm = X.varVal (b, Z') nm := by
    intro nm hnm
    cases nm with
    | par p => rfl
    | hid ℓ =>
        have hℓ : ℓ ∈ β.obs := by
          have hmem : ℓ ∈ β.obs ∨ VarName6.hid ℓ ∈
              (if β.mode = Mode6.high then
                ({VarName6.par (otherPrimaryName6 β.key)} : Finset X.Name)
              else (∅ : Finset X.Name)) := by
            simpa [reqNames6] using hnm
          rcases hmem with hmem | hmem
          · exact hmem
          · by_cases hm : β.mode = Mode6.high <;> simp [hm] at hmem
        exact hobs ℓ hℓ
  change X.tupleLawOn (b, Z) (reqNames6 β) (X.Tβ (b, Z) β) =
    X.tupleLawOn (b, Z') (reqNames6 β) (X.Tβ (b, Z') β)
  rw [hT]
  exact tupleLawOn_congr_varVal X (b, Z) (b, Z') (reqNames6 β)
    (X.Tβ (b, Z') β) hval

theorem dataLaw_expect_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    {Id : Type} [Fintype Id] [DecidableEq Id]
    (X : Ctx6 γ p₀ K n N E G M) (b : X.Base) (Z Z' : X.Hid)
    (D : Finset (Id × X.Ty)) (F : X.Data Id → ℝ)
    (hdep : HypercubeRamsey.FinProb.DependsOn F D)
    (hobs : ∀ e ∈ D, ∀ ℓ ∈ e.2.obs, Z ℓ = Z' ℓ) :
    (X.dataLaw Id (b, Z)).expect F = (X.dataLaw Id (b, Z')).expect F := by
  classical
  let P : (Id × X.Ty) → HypercubeRamsey.FinProb X.Tuple :=
    fun e => X.tupleLaw (b, Z) e.2
  let Q : (Id × X.Ty) → HypercubeRamsey.FinProb X.Tuple :=
    fun e => X.tupleLaw (b, Z') e.2
  have hP (e : Id × X.Ty) (he : e ∈ D) : P e = Q e := by
    dsimp [P, Q]
    exact tupleLaw_congr_hid X b Z Z' e.2 (hobs e he)
  have hsub :
      HypercubeRamsey.FinProb.pi (fun e : {e // e ∈ D} => P e.1) =
        HypercubeRamsey.FinProb.pi (fun e : {e // e ∈ D} => Q e.1) := by
    apply finProb_ext
    intro a
    change (∏ e : {e // e ∈ D}, (P e.1).w (a e)) =
      ∏ e : {e // e ∈ D}, (Q e.1).w (a e)
    apply Finset.prod_congr rfl
    intro e he
    exact congrArg (fun R : HypercubeRamsey.FinProb X.Tuple => R.w (a e))
      (hP e.1 e.2)
  let ω₀ : ∀ e : Id × X.Ty, X.Tuple := fun _ => (X.i₀, fun _ => X.y₀)
  have hMarg := HypercubeRamsey.FinProb.pi_expect_depends P D F ω₀ hdep
  have hMarg' := HypercubeRamsey.FinProb.pi_expect_depends Q D F ω₀ hdep
  calc
    (X.dataLaw Id (b, Z)).expect F = (HypercubeRamsey.FinProb.pi P).expect F := rfl
    _ = (HypercubeRamsey.FinProb.pi (fun e : {e // e ∈ D} => P e.1)).expect
        (fun a => F ((Equiv.piEquivPiSubtypeProd (fun e : Id × X.Ty => e ∈ D)
          (fun _ => X.Tuple)).symm (a, fun e => ω₀ e.1))) := hMarg
    _ = (HypercubeRamsey.FinProb.pi (fun e : {e // e ∈ D} => Q e.1)).expect
        (fun a => F ((Equiv.piEquivPiSubtypeProd (fun e : Id × X.Ty => e ∈ D)
          (fun _ => X.Tuple)).symm (a, fun e => ω₀ e.1))) := by rw [hsub]
    _ = (HypercubeRamsey.FinProb.pi Q).expect F := hMarg'.symm
    _ = (X.dataLaw Id (b, Z')).expect F := rfl

theorem finProb_prod_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : HypercubeRamsey.FinProb α) (Q : HypercubeRamsey.FinProb β)
    (f : α × β → ℝ) :
    (HypercubeRamsey.FinProb.prod P Q).expect f =
      P.expect (fun a => Q.expect (fun b => f (a, b))) := by
  classical
  simp only [HypercubeRamsey.FinProb.expect, HypercubeRamsey.FinProb.prod]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem centreLaw_expect_as_position_and_proxy {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour}
    {M : HypercubeRamsey.TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (f : X.Centre → ℝ) :
    (X.centreLaw H).expect f =
      (X.hp.posLaw).expect (fun P => (X.proxyLaw H).expect
        (fun ω => f (X.assemble P ω))) := by
  classical
  calc
    (X.centreLaw H).expect f =
        (X.hp.posLaw).expect (fun P => (X.dataLaw X.Loc H).expect
          (fun d => X.hp.actLaw.expect (fun a => X.hp.tieLaw.expect
            (fun τ => f (((P, d), a), τ))))) := by
              unfold Ctx6.centreLaw
              rw [finProb_prod_expect, finProb_prod_expect, finProb_prod_expect]
    _ = (X.hp.posLaw).expect (fun P => (X.proxyLaw H).expect
          (fun ω => f (X.assemble P ω))) := by
              apply congrArg (fun g : (X.Loc → Bool) → ℝ => X.hp.posLaw.expect g)
              funext P
              unfold Ctx6.proxyLaw
              rw [finProb_prod_expect, finProb_prod_expect]
              rfl

private theorem pi_weight_split6 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, HypercubeRamsey.FinProb (Ω i))
    (s : Finset ι) (ω : ∀ i, Ω i) :
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
    _ = (∏ i : {i // i ∈ s}, f i.1) *
          (∏ i : {i // i ∉ s}, f i.1) := by rw [← hs, ← hnot]

theorem pi_expect_split6 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinProb (Ω i)) (s : Finset ι)
    (f : (∀ i, Ω i) → ℝ) :
    (HypercubeRamsey.FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (HypercubeRamsey.FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (HypercubeRamsey.FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
              f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [pi_weight_split6 P s (e.symm (a, b))]
  change ((∏ i : {i // i ∈ s}, (P i.1).w (e.symm (a, b) i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (e.symm (a, b) i.1))) * f (e.symm (a, b)) = _
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [hleft, hright]
  rfl

theorem pi_expect_le_of_fiber_bound6 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinProb (Ω i)) (s : Finset ι)
    (f : (∀ i, Ω i) → ℝ) (C : ℝ)
    (hfiber : ∀ b : ∀ i : {i // i ∉ s}, Ω i.1,
      ∑ a : ∀ i : {i // i ∈ s}, Ω i.1,
        (HypercubeRamsey.FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
          f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) ≤ C) :
    (HypercubeRamsey.FinProb.pi P).expect f ≤ C := by
  classical
  let Ps := HypercubeRamsey.FinProb.pi (fun i : {i // i ∈ s} => P i.1)
  let Pc := HypercubeRamsey.FinProb.pi (fun i : {i // i ∉ s} => P i.1)
  rw [pi_expect_split6 P s f, Finset.sum_comm]
  calc
    (∑ b, ∑ a, Ps.w a * Pc.w b *
        f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b))) =
        ∑ b, Pc.w b * ∑ a, Ps.w a *
          f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
            apply Fintype.sum_congr
            intro b
            rw [Finset.mul_sum]
            apply Fintype.sum_congr
            intro a
            ring
    _ ≤ ∑ b, Pc.w b * C := by
          apply Finset.sum_le_sum
          intro b hb
          change Pc.w b * _ ≤ Pc.w b * C
          exact mul_le_mul_of_nonneg_left (hfiber b) (Pc.nonneg b)
    _ = C := by
          simpa [HypercubeRamsey.FinProb.expect] using
            (HypercubeRamsey.FinProb.expect_const Pc C)

noncomputable def singletonPiEquiv6 {ι Ω : Type*} [DecidableEq ι]
    (i : ι) : ({j // j ∈ ({i} : Finset ι)} → Ω) ≃ Ω := by
  letI : Unique {j // j ∈ ({i} : Finset ι)} := {
    default := ⟨i, Finset.mem_singleton_self i⟩
    uniq := by
      intro j
      apply Subtype.ext
      exact Finset.mem_singleton.mp j.property
  }
  exact {
    toFun := fun a => a default
    invFun := fun x _ => x
    left_inv := by
      intro a
      funext j
      have hj : j = default := Subsingleton.elim _ _
      rw [hj]
    right_inv := by intro x; rfl
  }

theorem sum_singletonPi6 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (i : ι) (f : ({j // j ∈ ({i} : Finset ι)} → Ω) → ℝ) :
    (∑ a, f a) = ∑ x, f ((singletonPiEquiv6 i).symm x) := by
  classical
  exact Fintype.sum_equiv (singletonPiEquiv6 i) f _ (by
    intro a
    rw [(singletonPiEquiv6 i).symm_apply_apply])

theorem pi_singleton_weight6 {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (P : ι → HypercubeRamsey.FinProb Ω) (i : ι)
    (a : {j // j ∈ ({i} : Finset ι)} → Ω) :
    (HypercubeRamsey.FinProb.pi (fun j : {j // j ∈ ({i} : Finset ι)} => P j.1)).w a =
      (P i).w (a ⟨i, Finset.mem_singleton_self i⟩) := by
  classical
  letI : Unique {j // j ∈ ({i} : Finset ι)} := {
    default := ⟨i, Finset.mem_singleton_self i⟩
    uniq := by
      intro j
      apply Subtype.ext
      exact Finset.mem_singleton.mp j.property
  }
  have hdefault : (default : {j // j ∈ ({i} : Finset ι)}) =
      ⟨i, Finset.mem_singleton_self i⟩ := Subtype.ext rfl
  simp [HypercubeRamsey.FinProb.pi, hdefault]

theorem tupleRatio_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.Base) (Z Z' : X.Hid) (β : X.Ty)
    (refTag : HypercubeRamsey.FinProb X.ι) (drop : X.Name) (o : X.Tuple)
    (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.tupleRatio (b, Z) (b, Z') β refTag drop o =
      X.tupleRatio (b, Z') (b, Z') β refTag drop o := by
  classical
  have hT := Tβ_congr_hid X b Z Z' β hobs
  have hval : ∀ nm ∈ reqNames6 β,
      X.varVal (b, Z) nm = X.varVal (b, Z') nm := by
    intro nm hnm
    cases nm with
    | par p => rfl
    | hid ℓ =>
        have hmem : ℓ ∈ β.obs ∨ VarName6.hid ℓ ∈
            (if β.mode = Mode6.high then
              ({VarName6.par (otherPrimaryName6 β.key)} : Finset X.Name)
            else (∅ : Finset X.Name)) := by
          simpa [reqNames6] using hnm
        rcases hmem with hmem | hmem
        · exact hobs ℓ hmem
        · by_cases hm : β.mode = Mode6.high <;> simp [hm] at hmem
  have hlabel (S : Finset X.Name) (hS : S ⊆ reqNames6 β) (i : X.ι) :
      X.labelLaw (b, Z) S i = X.labelLaw (b, Z') S i :=
    labelLaw_congr_varVal X (b, Z) (b, Z') S i (fun nm hnm => hval nm (hS hnm))
  unfold Ctx6.tupleRatio
  rw [hT, hlabel (reqNames6 β) (Finset.Subset.rfl) o.1]

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem tupleRef_congr_varVal {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H H' : X.Hist) (β : X.Ty)
    (T T' : HypercubeRamsey.FinProb X.ι) (drop : X.Name)
    (hT : T = T')
    (hval : ∀ nm ∈ (reqNames6 β).erase drop,
      X.varVal H nm = X.varVal H' nm) :
    X.tupleRef H β T drop = X.tupleRef H' β T' drop := by
  unfold Ctx6.tupleRef
  rw [hT]
  exact tupleLawOn_congr_varVal X H H' ((reqNames6 β).erase drop) T' hval

theorem tupleRatio_congr_varVal {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (Hc Hc' Hr Hr' : X.Hist) (β : X.Ty)
    (refTag refTag' : HypercubeRamsey.FinProb X.ι) (drop : X.Name) (o : X.Tuple)
    (hT : X.Tβ Hc β = X.Tβ Hc' β) (href : refTag = refTag')
    (hcVal : ∀ nm ∈ reqNames6 β, X.varVal Hc nm = X.varVal Hc' nm)
    (hrVal : ∀ nm ∈ (reqNames6 β).erase drop,
      X.varVal Hr nm = X.varVal Hr' nm) :
    X.tupleRatio Hc Hr β refTag drop o = X.tupleRatio Hc' Hr' β refTag' drop o := by
  have hcLabel (i : X.ι) : X.labelLaw Hc (reqNames6 β) i =
      X.labelLaw Hc' (reqNames6 β) i :=
    labelLaw_congr_varVal X Hc Hc' (reqNames6 β) i hcVal
  have hrLabel (i : X.ι) : X.labelLaw Hr ((reqNames6 β).erase drop) i =
      X.labelLaw Hr' ((reqNames6 β).erase drop) i :=
    labelLaw_congr_varVal X Hr Hr' ((reqNames6 β).erase drop) i hrVal
  unfold Ctx6.tupleRatio
  rw [hT, href, hcLabel, hrLabel]

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem reqNames_varVal_congr_hid {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.Base) (Z Z' : X.Hid) (β : X.Ty)
    (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    ∀ nm ∈ reqNames6 β, X.varVal (b, Z) nm = X.varVal (b, Z') nm := by
  intro nm hnm
  cases nm with
  | par p => rfl
  | hid ℓ =>
      have hmem : ℓ ∈ β.obs ∨ VarName6.hid ℓ ∈
          (if β.mode = Mode6.high then
            ({VarName6.par (otherPrimaryName6 β.key)} : Finset X.Name)
          else (∅ : Finset X.Name)) := by
        simpa [reqNames6] using hnm
      rcases hmem with hmem | hmem
      · exact hobs ℓ hmem
      · by_cases hm : β.mode = Mode6.high <;> simp [hm] at hmem

theorem lowRef_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State)
    (β : X.Ty) (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.lowRef (b₀, Z) b β = X.lowRef (b₀, Z') b β := by
  unfold Ctx6.lowRef
  apply tupleRef_congr_varVal X (b₀, Z) (b₀, Z') β
    (X.TβDel (b₀, Z) β (X.tgt b)) (X.TβDel (b₀, Z') β (X.tgt b))
    (.hid (X.tgt b)) ?_ ?_
  · exact tagPost_congr_hid X b₀ Z Z' β (β.obs.erase (X.tgt b))
      (Finset.erase_subset _ _) hobs
  · intro nm hnm
    exact reqNames_varVal_congr_hid X b₀ Z Z' β hobs nm
      ((Finset.erase_subset _ _) hnm)

theorem highRef_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State)
    (β : X.Ty) (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.highRef (b₀, Z) b β = X.highRef (b₀, Z') b β := by
  unfold Ctx6.highRef
  apply tupleRef_congr_varVal X (b₀, Z) (b₀, Z') β
    (tagLaw6 M) (tagLaw6 M) (.par (X.tgtName b)) rfl
  intro nm hnm
  exact reqNames_varVal_congr_hid X b₀ Z Z' β hobs nm
    ((Finset.erase_subset _ _) hnm)

theorem highLik_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State)
    (ξ : Fin N) (β : X.Ty) (o : X.Tuple)
    (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.highLik (b₀, Z) b ξ β o = X.highLik (b₀, Z') b ξ β o := by
  unfold Ctx6.highLik
  apply tupleRatio_congr_varVal X
    (X.withParH (b₀, Z) (X.tgtName b) ξ)
    (X.withParH (b₀, Z') (X.tgtName b) ξ)
    (b₀, Z) (b₀, Z') β (tagLaw6 M) (tagLaw6 M) (.par (X.tgtName b)) o
  · exact Tβ_congr_hid X (X.withPar (b₀) (X.tgtName b) ξ) Z Z' β hobs
  · rfl
  · exact reqNames_varVal_congr_hid X (X.withPar b₀ (X.tgtName b) ξ) Z Z' β hobs
  · intro nm hnm
    exact reqNames_varVal_congr_hid X b₀ Z Z' β hobs nm
      ((Finset.erase_subset _ _) hnm)

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem lowLik_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State)
    (ξ : Fin N) (β : X.Ty) (o : X.Tuple)
    (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.lowLik (b₀, Z) b ξ β o = X.lowLik (b₀, Z') b ξ β o := by
  classical
  let H : X.Hist := (b₀, Z)
  let H' : X.Hist := (b₀, Z')
  let Hξ : X.Hist := X.withHid H (X.tgt b) ξ
  let Hξ' : X.Hist := X.withHid H' (X.tgt b) ξ
  have hobsξ : ∀ ℓ ∈ β.obs, Hξ.2 ℓ = Hξ'.2 ℓ := by
    intro ℓ hℓ
    by_cases heq : ℓ = X.tgt b
    · simp [Hξ, Hξ', H, H', Ctx6.withHid, heq]
    · simp [Hξ, Hξ', H, H', Ctx6.withHid, heq, hobs ℓ hℓ]
  have hT : X.Tβ Hξ β = X.Tβ Hξ' β :=
    Tβ_congr_hid X b₀ Hξ.2 Hξ'.2 β hobsξ
  have hRef : X.TβDel H β (X.tgt b) = X.TβDel H' β (X.tgt b) := by
    change X.tagPost H β (β.obs.erase (X.tgt b)) =
      X.tagPost H' β (β.obs.erase (X.tgt b))
    exact tagPost_congr_hid X b₀ Z Z' β (β.obs.erase (X.tgt b))
      (Finset.erase_subset _ _) hobs
  have hcVal : ∀ nm ∈ reqNames6 β, X.varVal Hξ nm = X.varVal Hξ' nm := by
    intro nm hnm
    exact reqNames_varVal_congr_hid X b₀ Hξ.2 Hξ'.2 β hobsξ nm hnm
  have hrVal : ∀ nm ∈ (reqNames6 β).erase (.hid (X.tgt b)),
      X.varVal H nm = X.varVal H' nm := by
    intro nm hnm
    exact reqNames_varVal_congr_hid X b₀ Z Z' β hobs nm
      ((Finset.erase_subset _ _) hnm)
  unfold Ctx6.lowLik
  exact tupleRatio_congr_varVal X Hξ Hξ' H H' β
    (X.TβDel H β (X.tgt b)) (X.TβDel H' β (X.tgt b))
    (.hid (X.tgt b)) o hT hRef hcVal hrVal

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

/-- Every type listed in a descriptor reads only hidden scalars in `locHid`. -/
theorem locHid_agree_on_type {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (D : Finset (Id × X.Ty)) (Z Z' : X.Hid)
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) (e : Id × X.Ty) (he : e ∈ D) :
    ∀ ℓ ∈ e.2.obs, Z ℓ = Z' ℓ := by
  intro ℓ hℓ
  exact hobs ℓ (Finset.mem_biUnion.mpr ⟨e, he, hℓ⟩)

theorem lowGate_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) :
    X.LowGate (b₀, Z) b D ξ ↔ X.LowGate (b₀, Z') b D ξ := by
  classical
  unfold Ctx6.LowGate
  constructor
  · rintro ⟨hp, hcap, htests⟩
    refine ⟨hp, hcap, ?_⟩
    intro e he
    have hobsξ : ∀ ℓ ∈ e.2.obs,
        (X.withHid (b₀, Z) (X.tgt b) ξ).2 ℓ =
          (X.withHid (b₀, Z') (X.tgt b) ξ).2 ℓ := by
      intro ℓ hℓ
      by_cases heq : ℓ = X.tgt b
      · simp [Ctx6.withHid, heq]
      · simp [Ctx6.withHid, heq,
          locHid_agree_on_type X D Z Z' hobs e he ℓ hℓ]
    have hiff := HypercubeRamsey.Lane_q_s06_loads.step2Tests_congr_hid X
      (X.withHid (b₀, Z) (X.tgt b) ξ).1
      (X.withHid (b₀, Z) (X.tgt b) ξ).2
      (X.withHid (b₀, Z') (X.tgt b) ξ).2 e.2 hobsξ
    exact hiff.mp (htests e he)
  · rintro ⟨hp, hcap, htests⟩
    refine ⟨hp, hcap, ?_⟩
    intro e he
    have hobsξ : ∀ ℓ ∈ e.2.obs,
        (X.withHid (b₀, Z) (X.tgt b) ξ).2 ℓ =
          (X.withHid (b₀, Z') (X.tgt b) ξ).2 ℓ := by
      intro ℓ hℓ
      by_cases heq : ℓ = X.tgt b
      · simp [Ctx6.withHid, heq]
      · simp [Ctx6.withHid, heq,
          locHid_agree_on_type X D Z Z' hobs e he ℓ hℓ]
    have hiff := HypercubeRamsey.Lane_q_s06_loads.step2Tests_congr_hid X
      (X.withHid (b₀, Z) (X.tgt b) ξ).1
      (X.withHid (b₀, Z) (X.tgt b) ξ).2
      (X.withHid (b₀, Z') (X.tgt b) ξ).2 e.2 hobsξ
    exact hiff.mpr (htests e he)

theorem highGate_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) :
    X.HighGate (b₀, Z) b D ξ ↔ X.HighGate (b₀, Z') b D ξ := by
  classical
  unfold Ctx6.HighGate
  constructor
  · rintro ⟨hp, hstep1, hstep2⟩
    refine ⟨hp, ?_, ?_⟩
    · intro ℓ hℓ
      exact hstep1 ℓ hℓ
    · intro e he
      have hiff := HypercubeRamsey.Lane_q_s06_loads.step2Tests_congr_hid X
        (X.withParH (b₀, Z) (X.tgtName b) ξ).1 Z Z' e.2
        (locHid_agree_on_type X D Z Z' hobs e he)
      exact hiff.mp (hstep2 e he)
  · rintro ⟨hp, hstep1, hstep2⟩
    refine ⟨hp, ?_, ?_⟩
    · intro ℓ hℓ
      exact hstep1 ℓ hℓ
    · intro e he
      have hiff := HypercubeRamsey.Lane_q_s06_loads.step2Tests_congr_hid X
        (X.withParH (b₀, Z) (X.tgtName b) ξ).1 Z Z' e.2
        (locHid_agree_on_type X D Z Z' hobs e he)
      exact hiff.mpr (hstep2 e he)

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem locDensity_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (nm : ParentName6 X.Bin)
    (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) :
    X.locDensity (b₀, Z) nm D ξ = X.locDensity (b₀, Z') nm D ξ := by
  classical
  unfold Ctx6.locDensity
  let b' := X.withPar b₀ nm ξ
  change
    (∏ u ∈ X.locBins D nm, (N : ℝ) * (X.candLaw b'.1).w (b₀.2.1 u)) *
      (∏ s ∈ X.locKeys D,
        safeRatio6 ((X.tagLawAt (X.parOf b') s).w (b₀.2.2 s)) (M.Λ (b₀.2.2 s))) *
      ∏ ℓ ∈ X.locHid D, (N : ℝ) * (X.hidPost b' ℓ.1).w (Z ℓ) =
    (∏ u ∈ X.locBins D nm, (N : ℝ) * (X.candLaw b'.1).w (b₀.2.1 u)) *
      (∏ s ∈ X.locKeys D,
        safeRatio6 ((X.tagLawAt (X.parOf b') s).w (b₀.2.2 s)) (M.Λ (b₀.2.2 s))) *
      ∏ ℓ ∈ X.locHid D, (N : ℝ) * (X.hidPost b' ℓ.1).w (Z' ℓ)
  have hprod :
      (∏ ℓ ∈ X.locHid D, (N : ℝ) * (X.hidPost b' ℓ.1).w (Z ℓ)) =
        ∏ ℓ ∈ X.locHid D, (N : ℝ) * (X.hidPost b' ℓ.1).w (Z' ℓ) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [hobs ℓ hℓ]
  rw [hprod]

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem lowWeight_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State) (D : Finset (Id × X.Ty))
    (o : X.Data Id) (drop : Option (Id × X.Ty)) (ξ : Fin N)
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) :
    X.lowWeight (b₀, Z) b D o drop ξ = X.lowWeight (b₀, Z') b D o drop ξ := by
  classical
  have hgate := lowGate_congr_hid X b₀ Z Z' b D ξ hobs
  have hprod :
      (∏ e ∈ D, if drop = some e then 1 else X.lowLik (b₀, Z) b ξ e.2 (o e)) =
        ∏ e ∈ D, if drop = some e then 1 else X.lowLik (b₀, Z') b ξ e.2 (o e) := by
    apply Finset.prod_congr rfl
    intro e he
    by_cases hd : drop = some e
    · simp [hd]
    · rw [if_neg hd, if_neg hd]
      exact lowLik_congr_hid X b₀ Z Z' b ξ e.2 (o e)
        (locHid_agree_on_type X D Z Z' hobs e he)
  unfold Ctx6.lowWeight
  rw [propext hgate, hprod]

theorem highWeight_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State) (D : Finset (Id × X.Ty))
    (o : X.Data Id) (drop : Option (Id × X.Ty)) (ξ : Fin N)
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) :
    X.highWeight (b₀, Z) b D o drop ξ = X.highWeight (b₀, Z') b D o drop ξ := by
  classical
  have hgate := highGate_congr_hid X b₀ Z Z' b D ξ hobs
  have hden := locDensity_congr_hid X b₀ Z Z' (X.tgtName b) D ξ hobs
  have hprod :
      (∏ e ∈ D, if drop = some e then 1 else X.highLik (b₀, Z) b ξ e.2 (o e)) =
        ∏ e ∈ D, if drop = some e then 1 else X.highLik (b₀, Z') b ξ e.2 (o e) := by
    apply Finset.prod_congr rfl
    intro e he
    by_cases hd : drop = some e
    · simp [hd]
    · rw [if_neg hd, if_neg hd]
      exact highLik_congr_hid X b₀ Z Z' b ξ e.2 (o e)
        (locHid_agree_on_type X D Z Z' hobs e he)
  unfold Ctx6.highWeight
  rw [propext hgate, hden, hprod]
  rfl

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem s3Weight_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State) (D : Finset (Id × X.Ty))
    (o : X.Data Id) (drop : Option (Id × X.Ty)) (ξ : Fin N)
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) :
    X.s3Weight (b₀, Z) b D o drop ξ = X.s3Weight (b₀, Z') b D o drop ξ := by
  classical
  cases hm : X.stMode b with
  | low =>
      simp [Ctx6.s3Weight, hm, lowWeight_congr_hid X b₀ Z Z' b D o drop ξ hobs]
  | high =>
      simp [Ctx6.s3Weight, hm, highWeight_congr_hid X b₀ Z Z' b D o drop ξ hobs]

theorem s3Mass_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State) (D : Finset (Id × X.Ty))
    (o : X.Data Id) (drop : Option (Id × X.Ty))
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) :
    X.s3Mass (b₀, Z) b D o drop = X.s3Mass (b₀, Z') b D o drop := by
  unfold Ctx6.s3Mass
  apply Finset.sum_congr rfl
  intro ξ hξ
  exact s3Weight_congr_hid X b₀ Z Z' b D o drop ξ hobs

theorem S3Tests_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State) (D : Finset (Id × X.Ty))
    (o : X.Data Id) (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) :
    X.S3Tests (b₀, Z) b D o ↔ X.S3Tests (b₀, Z') b D o := by
  unfold Ctx6.S3Tests
  rw [s3Mass_congr_hid X b₀ Z Z' b D o none hobs]
  constructor
  · rintro ⟨hpos, hthr, hdel⟩
    refine ⟨hpos, hthr, ?_⟩
    intro c hc hm
    rw [← s3Mass_congr_hid X b₀ Z Z' b D o (some c) hobs]
    exact hdel c hc hm
  · rintro ⟨hpos, hthr, hdel⟩
    refine ⟨hpos, hthr, ?_⟩
    intro c hc hm
    rw [s3Mass_congr_hid X b₀ Z Z' b D o (some c) hobs]
    exact hdel c hc hm

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem S3TrueGate_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State) (D : Finset (Id × X.Ty))
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ)
    (htarget : Z (X.tgt b) = Z' (X.tgt b)) :
    X.S3TrueGate (b₀, Z) b D ↔ X.S3TrueGate (b₀, Z') b D := by
  classical
  cases hm : X.stMode b with
  | low =>
      have ht : X.trueTarget (b₀, Z) b = X.trueTarget (b₀, Z') b := by
        simp [Ctx6.trueTarget, hm, htarget]
      simp only [Ctx6.S3TrueGate, hm]
      rw [ht]
      exact lowGate_congr_hid X b₀ Z Z' b D (X.trueTarget (b₀, Z') b) hobs
  | high =>
      simp only [Ctx6.S3TrueGate, hm, Ctx6.trueTarget]
      exact highGate_congr_hid X b₀ Z Z' b D ((X.parOf b₀).val (X.tgtName b)) hobs

theorem S3Fail_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State) (D : Finset (Id × X.Ty))
    (o : X.Data Id) (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ)
    (htarget : Z (X.tgt b) = Z' (X.tgt b)) :
    X.S3Fail (b₀, Z) b D o ↔ X.S3Fail (b₀, Z') b D o := by
  unfold Ctx6.S3Fail
  have hg := S3TrueGate_congr_hid X b₀ Z Z' b D hobs htarget
  have ht := S3Tests_congr_hid X b₀ Z Z' b D o hobs
  constructor
  · rintro ⟨hg0, hfail⟩
    refine ⟨hg.mp hg0, ?_⟩
    intro htests
    exact hfail (ht.mpr htests)
  · rintro ⟨hg0, hfail⟩
    refine ⟨hg.mpr hg0, ?_⟩
    intro htests
    exact hfail (ht.mp htests)

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem lowWeight_congr_data {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o o' : X.Data Id)
    (drop : Option (Id × X.Ty)) (ξ : Fin N)
    (hO : ∀ e ∈ D, o e = o' e) :
    X.lowWeight H b D o drop ξ = X.lowWeight H b D o' drop ξ := by
  classical
  have hprod :
      (∏ e ∈ D, if drop = some e then 1 else X.lowLik H b ξ e.2 (o e)) =
        ∏ e ∈ D, if drop = some e then 1 else X.lowLik H b ξ e.2 (o' e) := by
    apply Finset.prod_congr rfl
    intro e he
    by_cases hd : drop = some e
    · simp [hd]
    · simp [hd, hO e he]
  unfold Ctx6.lowWeight
  rw [hprod]

theorem highWeight_congr_data {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o o' : X.Data Id)
    (drop : Option (Id × X.Ty)) (ξ : Fin N)
    (hO : ∀ e ∈ D, o e = o' e) :
    X.highWeight H b D o drop ξ = X.highWeight H b D o' drop ξ := by
  classical
  have hprod :
      (∏ e ∈ D, if drop = some e then 1 else X.highLik H b ξ e.2 (o e)) =
        ∏ e ∈ D, if drop = some e then 1 else X.highLik H b ξ e.2 (o' e) := by
    apply Finset.prod_congr rfl
    intro e he
    by_cases hd : drop = some e
    · simp [hd]
    · simp [hd, hO e he]
  unfold Ctx6.highWeight
  rw [hprod]

theorem s3Weight_congr_data {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o o' : X.Data Id)
    (drop : Option (Id × X.Ty)) (ξ : Fin N)
    (hO : ∀ e ∈ D, o e = o' e) :
    X.s3Weight H b D o drop ξ = X.s3Weight H b D o' drop ξ := by
  classical
  cases hm : X.stMode b with
  | low => simp [Ctx6.s3Weight, hm, lowWeight_congr_data X H b D o o' drop ξ hO]
  | high => simp [Ctx6.s3Weight, hm, highWeight_congr_data X H b D o o' drop ξ hO]

theorem s3Mass_congr_data {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o o' : X.Data Id)
    (drop : Option (Id × X.Ty)) (hO : ∀ e ∈ D, o e = o' e) :
    X.s3Mass H b D o drop = X.s3Mass H b D o' drop := by
  unfold Ctx6.s3Mass
  apply Finset.sum_congr rfl
  intro ξ hξ
  exact s3Weight_congr_data X H b D o o' drop ξ hO

theorem S3Tests_congr_data {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o o' : X.Data Id)
    (hO : ∀ e ∈ D, o e = o' e) :
    X.S3Tests H b D o ↔ X.S3Tests H b D o' := by
  unfold Ctx6.S3Tests
  rw [s3Mass_congr_data X H b D o o' none hO]
  constructor
  · rintro ⟨hpos, hthr, hdel⟩
    refine ⟨hpos, hthr, ?_⟩
    intro c hc hm
    rw [← s3Mass_congr_data X H b D o o' (some c) hO]
    exact hdel c hc hm
  · rintro ⟨hpos, hthr, hdel⟩
    refine ⟨hpos, hthr, ?_⟩
    intro c hc hm
    rw [s3Mass_congr_data X H b D o o' (some c) hO]
    exact hdel c hc hm

theorem S3Fail_congr_data {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o o' : X.Data Id)
    (hO : ∀ e ∈ D, o e = o' e) :
    X.S3Fail H b D o ↔ X.S3Fail H b D o' := by
  unfold Ctx6.S3Fail
  simp only [S3Tests_congr_data X H b D o o' hO]

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

private theorem finProb_pr_expect_ite {Ω : Type*} [Fintype Ω]
    (P : HypercubeRamsey.FinProb Ω) (A : Ω → Prop) [DecidablePred A] :
    P.pr A = P.expect (fun ω => if A ω then 1 else 0) := by
  classical
  unfold HypercubeRamsey.FinProb.pr HypercubeRamsey.FinProb.expect
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h]

theorem rate3_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base) (Z Z' : X.Hid)
    (b : X.State) (D : Finset (Fin X.T × X.Ty))
    (hobs : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ)
    (htarget : Z (X.tgt b) = Z' (X.tgt b)) :
    X.rate3 (b₀, Z) b D = X.rate3 (b₀, Z') b D := by
  classical
  let H : X.Hist := (b₀, Z)
  let H' : X.Hist := (b₀, Z')
  let P : (Fin X.T × X.Ty) → HypercubeRamsey.FinProb X.Tuple :=
    fun e => X.tupleLaw H e.2
  let Q : (Fin X.T × X.Ty) → HypercubeRamsey.FinProb X.Tuple :=
    fun e => X.tupleLaw H' e.2
  let F : X.Data (Fin X.T) → ℝ := fun o => if X.S3Fail H b D o then 1 else 0
  let F' : X.Data (Fin X.T) → ℝ := fun o => if X.S3Fail H' b D o then 1 else 0
  have hdep : HypercubeRamsey.FinProb.DependsOn F D := by
    intro o o' hEq
    have hiff := S3Fail_congr_data X H b D o o' hEq
    simp [F, hiff]
  have hdep' : HypercubeRamsey.FinProb.DependsOn F' D := by
    intro o o' hEq
    have hiff := S3Fail_congr_data X H' b D o o' hEq
    simp [F', hiff]
  have hF : F = F' := by
    funext o
    change (if X.S3Fail H b D o then 1 else 0) =
      (if X.S3Fail H' b D o then 1 else 0)
    rw [S3Fail_congr_hid X b₀ Z Z' b D o hobs htarget]
  have hP (e : Fin X.T × X.Ty) (he : e ∈ D) : P e = Q e := by
    dsimp [P, Q]
    exact tupleLaw_congr_hid X b₀ Z Z' e.2
      (locHid_agree_on_type X D Z Z' hobs e he)
  have hsub :
      HypercubeRamsey.FinProb.pi (fun e : {e // e ∈ D} => P e.1) =
        HypercubeRamsey.FinProb.pi (fun e : {e // e ∈ D} => Q e.1) := by
    apply finProb_ext
    intro a
    change (∏ e : {e // e ∈ D}, (P e.1).w (a e)) =
      ∏ e : {e // e ∈ D}, (Q e.1).w (a e)
    apply Finset.prod_congr rfl
    intro e he
    exact congrArg (fun R : HypercubeRamsey.FinProb X.Tuple => R.w (a e)) (hP e.1 e.2)
  let ω₀ : ∀ e : Fin X.T × X.Ty, X.Tuple := fun _ => (X.i₀, fun _ => X.y₀)
  have hrate : X.rate3 H b D = (HypercubeRamsey.FinProb.pi P).expect F := by
    unfold Ctx6.rate3
    rw [finProb_pr_expect_ite]
    rfl
  have hrate' : X.rate3 H' b D = (HypercubeRamsey.FinProb.pi Q).expect F' := by
    unfold Ctx6.rate3
    rw [finProb_pr_expect_ite]
    rfl
  have hMarg := HypercubeRamsey.FinProb.pi_expect_depends P D F ω₀ hdep
  have hMarg' := HypercubeRamsey.FinProb.pi_expect_depends Q D F' ω₀ hdep'
  have hRestr :
      (fun a : ∀ e : {e // e ∈ D}, X.Tuple =>
        F ((Equiv.piEquivPiSubtypeProd (fun e : Fin X.T × X.Ty => e ∈ D)
          (fun _ => X.Tuple)).symm (a, fun e => ω₀ e.1))) =
      (fun a : ∀ e : {e // e ∈ D}, X.Tuple =>
        F' ((Equiv.piEquivPiSubtypeProd (fun e : Fin X.T × X.Ty => e ∈ D)
          (fun _ => X.Tuple)).symm (a, fun e => ω₀ e.1))) := by
    funext a
    exact congrArg (fun f : X.Data (Fin X.T) → ℝ =>
      f ((Equiv.piEquivPiSubtypeProd (fun e : Fin X.T × X.Ty => e ∈ D)
        (fun _ => X.Tuple)).symm (a, fun e => ω₀ e.1))) hF
  calc
    X.rate3 H b D = (HypercubeRamsey.FinProb.pi P).expect F := hrate
    _ = (HypercubeRamsey.FinProb.pi (fun e : {e // e ∈ D} => P e.1)).expect
        (fun a => F ((Equiv.piEquivPiSubtypeProd (fun e : Fin X.T × X.Ty => e ∈ D)
          (fun _ => X.Tuple)).symm (a, fun e => ω₀ e.1))) := hMarg
    _ = (HypercubeRamsey.FinProb.pi (fun e : {e // e ∈ D} => Q e.1)).expect
        (fun a => F' ((Equiv.piEquivPiSubtypeProd (fun e : Fin X.T × X.Ty => e ∈ D)
          (fun _ => X.Tuple)).symm (a, fun e => ω₀ e.1))) := by
          rw [hsub, hRestr]
    _ = (HypercubeRamsey.FinProb.pi Q).expect F' := hMarg'.symm
    _ = X.rate3 H' b D := hrate'.symm

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem Step2Fail_congr_hid {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base) (Z Z' : X.Hid) (β : X.Ty)
    (hobs : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.Step2Fail (b₀, Z) β ↔ X.Step2Fail (b₀, Z') β := by
  unfold Ctx6.Step2Fail
  simp only [HypercubeRamsey.Lane_q_s06_loads.step2Tests_congr_hid X b₀ Z Z' β hobs]

theorem Bad3_congr_of_scopes {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base) (gr : X.Bin × CubeVertex X.m)
    (Z Z' : X.Hid) (S : Finset X.HKey)
    (hZ : ∀ ℓ ∈ S, Z ℓ = Z' ℓ)
    (hStep2 : ∀ x, HypercubeRamsey.IsEvenRole x → (X.g.L.key x).1 = gr.1 →
      X.g.L.sign x = gr.2 → ∀ ℓ ∈ (X.evenType x).obs, ℓ ∈ S)
    (hRate : ∀ b ∈ X.g.L.oddStates, (X.g.L.stKey b).1 = gr.1 →
      X.g.L.stSign b = gr.2 → ∀ D ∈ X.absDescs b,
        X.locHid D ⊆ S ∧ X.tgt b ∈ S) :
    X.Bad3 b₀ gr Z ↔ X.Bad3 b₀ gr Z' := by
  constructor
  · rintro (⟨x, hEven, hbin, hsign, hfail⟩ |
      ⟨b, hb, hbin, hsign, D, hD, hrate⟩)
    · left
      refine ⟨x, hEven, hbin, hsign, ?_⟩
      exact (Step2Fail_congr_hid X b₀ Z Z' (X.evenType x)
        (fun ℓ hℓ => hZ ℓ (hStep2 x hEven hbin hsign ℓ hℓ))).mp hfail
    · right
      refine ⟨b, hb, hbin, hsign, D, hD, ?_⟩
      have hloc := hRate b hb hbin hsign D hD
      have hrateEq := rate3_congr_hid X b₀ Z Z' b D
        (fun ℓ hℓ => hZ ℓ (hloc.1 hℓ)) (hZ (X.tgt b) hloc.2)
      rw [← hrateEq]
      exact hrate
  · rintro (⟨x, hEven, hbin, hsign, hfail⟩ |
      ⟨b, hb, hbin, hsign, D, hD, hrate⟩)
    · left
      refine ⟨x, hEven, hbin, hsign, ?_⟩
      exact (Step2Fail_congr_hid X b₀ Z Z' (X.evenType x)
        (fun ℓ hℓ => hZ ℓ (hStep2 x hEven hbin hsign ℓ hℓ))).mpr hfail
    · right
      refine ⟨b, hb, hbin, hsign, D, hD, ?_⟩
      have hloc := hRate b hb hbin hsign D hD
      have hrateEq := rate3_congr_hid X b₀ Z Z' b D
        (fun ℓ hℓ => hZ ℓ (hloc.1 hℓ)) (hZ (X.tgt b) hloc.2)
      rw [hrateEq]
      exact hrate

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem hammingDist_update_le_one {m : ℕ} (t : CubeVertex m) (a : Fin m) :
    HypercubeRamsey.hammingDist t (Function.update t a (!t a)) ≤ 1 := by
  classical
  change (Finset.univ.filter fun j : Fin m =>
    t j ≠ Function.update t a (!t a) j).card ≤ 1
  have hsub : (Finset.univ.filter fun j : Fin m =>
      t j ≠ Function.update t a (!t a) j) ⊆ {a} := by
    intro j hj
    by_cases hja : j = a
    · simp [hja]
    · have heq : t j = Function.update t a (!t a) j := by simp [hja]
      exact False.elim ((Finset.mem_filter.mp hj).2 heq)
  calc
    _ ≤ ({a} : Finset (Fin m)).card := Finset.card_le_card hsub
    _ = 1 := by simp

theorem lowObservations6_scope {W : Type*} [Fintype W] {m : ℕ}
    (binAdjacent : W → W → Prop) (h : CoarseKey6 W) (t : CubeVertex m)
    (F : Finset (Fin m)) (ℓ : HiddenKey6 W m)
    (hℓ : ℓ ∈ lowObservations6 binAdjacent h t F) :
    (ℓ.1 = h ∨ ℓ.1 ∈ keyNeighborhood6 binAdjacent h) ∧
      HypercubeRamsey.hammingDist t ℓ.2 ≤ 1 := by
  classical
  rcases Finset.mem_union.mp hℓ with hfirst | hsecond
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hfirst
    exact ⟨Or.inr hs, by simp [HypercubeRamsey.hammingDist]⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hsecond
    exact ⟨Or.inl rfl, hammingDist_update_le_one t a⟩

theorem highObservations6_scope {W : Type*} {m : ℕ}
    (h : CoarseKey6 W) (t : CubeVertex m) (j J : ℕ)
    (ℓ : HiddenKey6 W m) (hℓ : ℓ ∈ highObservations6 h t j J) :
    ℓ.1 = h ∧
      HypercubeRamsey.hammingDist t ℓ.2 ≤ 1 := by
  classical
  by_cases hj : j = J + 1
  · simp [highObservations6, hj] at hℓ
    rcases hℓ with rfl
    exact ⟨rfl, by simp [HypercubeRamsey.hammingDist]⟩
  · simp [highObservations6, hj] at hℓ

theorem makeType6_obs_scope {W : Type*} [Fintype W] {m : ℕ}
    (binAdjacent : W → W → Prop) (h : CoarseKey6 W) (t : CubeVertex m)
    (F : Finset (Fin m)) (j J : ℕ) (ℓ : HiddenKey6 W m)
    (hℓ : ℓ ∈ (makeType6 binAdjacent h t F j J).obs) :
    (ℓ.1 = h ∨ ℓ.1 ∈ keyNeighborhood6 binAdjacent h) ∧
      HypercubeRamsey.hammingDist t ℓ.2 ≤ 1 := by
  classical
  by_cases hlow : j ≤ J
  · have hℓlow : ℓ ∈ lowObservations6 binAdjacent h t F := by
      simpa [makeType6, Type6.obs, hlow] using hℓ
    exact lowObservations6_scope binAdjacent h t F ℓ hℓlow
  · have hh := highObservations6_scope h t j J ℓ (by
      simpa [makeType6, Type6.obs, hlow] using hℓ)
    rcases hh with ⟨hk, hdist⟩
    exact ⟨Or.inl hk, hdist⟩

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem keyBall6_step {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (root k : X.Key) (r : ℕ)
    (hk : k ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root r)
    (hnext : k ∈ X.C k) :
    k ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root (r + 1) := by
  change k ∈ (HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root r).biUnion X.C
  exact Finset.mem_biUnion.mpr ⟨k, hk, hnext⟩

theorem keyBall6_extend_C {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (root k k' : X.Key) (r : ℕ)
    (hk : k ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root r)
    (hC : k' ∈ X.C k) :
    k' ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root (r + 1) := by
  change k' ∈ (HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root r).biUnion X.C
  exact Finset.mem_biUnion.mpr ⟨k, hk, hC⟩

theorem adjacent_key_relation {n : ℕ} {α : ℝ} (g : ChunkGeometry6 n α)
    {x y : CubeVertex n} (hxy : (cube n).Adj x y) :
    keyAdjacent6 binAdjacent6 (g.L.key x) (g.L.key y) := by
  classical
  by_cases hflip : ∃ i a, a ∈ g.L.coarseChunks i ∧ x a ≠ y a
  · obtain ⟨i, a, hai, haxy⟩ := hflip
    exact g.flips.coarse_flip_key x y hxy ⟨i, a, hai, haxy⟩
  · have hagree : ∀ i a, a ∈ g.L.coarseChunks i → x a = y a := by
      intro i a hai
      by_contra hne
      exact hflip ⟨i, a, hai, hne⟩
    have heq := g.flips.noncoarse_flip_key x y hxy hagree
    exact heq ▸ Or.inl rfl

theorem ctx6_stNbr_key_adjacent {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b a : X.State) (ha : a ∈ X.g.L.stNbr b) :
    keyAdjacent6 binAdjacent6 (X.g.L.stKey b) (X.g.L.stKey a) := by
  classical
  simp only [ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  rcases ha with ⟨u, v, hodd, heven, hbu, hav, huv⟩
  rw [← hbu, ← hav, X.facts.key_eq u, X.facts.key_eq v]
  exact adjacent_key_relation X.g huv

theorem absDesc_type_mem_stNbr {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.State) (D : Finset (Fin X.T × X.Ty))
    (hD : D ∈ X.absDescs b) (e : Fin X.T × X.Ty) (he : e ∈ D) :
    ∃ a ∈ X.g.L.stNbr b, e.2 = X.stType a := by
  classical
  unfold Ctx6.absDescs Ctx6.descsIn at hD
  rcases Finset.mem_image.mp hD with ⟨φ, hφ, rfl⟩
  unfold Ctx6.descOf at he
  rcases Finset.mem_image.mp he with ⟨a, ha, hea⟩
  refine ⟨a.1, a.property, ?_⟩
  exact (congrArg Prod.snd hea).symm

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

/-- Every key stays in the next radius because `C` contains the key itself. -/
theorem keyBall6_pad_self {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (root k : X.Key) (r : ℕ)
    (hk : k ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root r) :
    k ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root (r + 1) := by
  apply keyBall6_step X root k r hk
  change k ∈ keyNeighborhood6 binAdjacent6 k
  simp [keyNeighborhood6, keyAdjacent6]

theorem keyBall6_contains_same_bin {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (gr : X.Bin × CubeVertex X.m) (k : X.Key)
    (hbin : k.1 = gr.1) :
    k ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X (gr.1, KeyFlag6.interior) 1 := by
  let root : X.Key := (gr.1, KeyFlag6.interior)
  classical
  have hrel : keyAdjacent6 binAdjacent6 root k := Or.inr (Or.inl hbin.symm)
  have hC : k ∈ X.C root := by
    change k ∈ keyNeighborhood6 binAdjacent6 root
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel⟩
  have hroot : root ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root 0 := by
    simp [HypercubeRamsey.Lane_q_s06_loads.keyBall6]
  exact keyBall6_extend_C X root root k 0 hroot hC

theorem evenType_obs_subset_bad3Scope {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (gr : X.Bin × CubeVertex X.m)
    (x : CubeVertex n) (hbin : (X.g.L.key x).1 = gr.1)
    (hsign : X.g.L.sign x = gr.2) :
    (X.evenType x).obs ⊆ HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr := by
  intro ℓ hℓ
  have hgeom := makeType6_obs_scope binAdjacent6 (X.g.L.key x) (X.g.L.sign x)
    (X.g.L.flippable x) (X.g.L.severity x) X.J ℓ (by
      simpa [Ctx6.evenType] using hℓ)
  have hroot := keyBall6_contains_same_bin X gr (X.g.L.key x) hbin
  have hk2 : ℓ.1 ∈
      HypercubeRamsey.Lane_q_s06_loads.keyBall6 X (gr.1, KeyFlag6.interior) 2 := by
    rcases hgeom.1 with hEq | hC
    · rw [hEq]
      exact keyBall6_pad_self X (gr.1, KeyFlag6.interior) (X.g.L.key x) 1 hroot
    · exact keyBall6_extend_C X
        (gr.1, KeyFlag6.interior) (X.g.L.key x) ℓ.1 1 hroot (by
          simpa [Ctx6.C] using hC)
  have hk3 := keyBall6_pad_self X (gr.1, KeyFlag6.interior) ℓ.1 2 hk2
  have hk4 := keyBall6_pad_self X (gr.1, KeyFlag6.interior) ℓ.1 3 hk3
  have hdist4' : HypercubeRamsey.hammingDist (X.g.L.sign x) ℓ.2 ≤ 4 := by
    exact le_trans hgeom.2 (by omega)
  have hsballSign : ℓ.2 ∈ HypercubeRamsey.hammingBall (X.g.L.sign x) 4 := by
    letI : DecidablePred (fun u : CubeVertex X.g.L.m =>
        HypercubeRamsey.hammingDist (X.g.L.sign x) u ≤ 4) := fun u => Nat.decLe _ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist4'⟩
  have hsball : ℓ.2 ∈ HypercubeRamsey.hammingBall
      (show CubeVertex X.g.L.m from gr.2) 4 := by
    simpa [hsign] using hsballSign
  unfold HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6
  exact Finset.mem_product.mpr ⟨hk4, hsball⟩

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem stType_obs_subset_bad3Scope {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (gr : X.Bin × CubeVertex X.m)
    (b a : X.State) (ha : a ∈ X.g.L.stNbr b)
    (hbin : (X.g.L.stKey b).1 = gr.1) (hsign : X.g.L.stSign b = gr.2) :
    (X.stType a).obs ⊆ HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr := by
  classical
  intro ℓ hℓ
  have hgeom := makeType6_obs_scope binAdjacent6 (X.g.L.stKey a) (X.g.L.stSign a)
    (X.g.L.stFlippable a) (X.g.L.stSeverity a) X.J ℓ (by
      simpa [Ctx6.stType, ChunkLayout6.stType] using hℓ)
  have hroot := keyBall6_contains_same_bin X gr (X.g.L.stKey b) hbin
  have hAdj := ctx6_stNbr_key_adjacent X b a ha
  have hC : X.g.L.stKey a ∈ X.C (X.g.L.stKey b) := by
    change X.g.L.stKey a ∈ keyNeighborhood6 binAdjacent6 (X.g.L.stKey b)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAdj⟩
  have ha2 := keyBall6_extend_C X (gr.1, KeyFlag6.interior)
    (X.g.L.stKey b) (X.g.L.stKey a) 1 hroot hC
  have hk3 : ℓ.1 ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X
      (gr.1, KeyFlag6.interior) 3 := by
    rcases hgeom.1 with heq | hC'
    · rw [heq]
      exact keyBall6_pad_self X (gr.1, KeyFlag6.interior) (X.g.L.stKey a) 2 ha2
    · exact keyBall6_extend_C X (gr.1, KeyFlag6.interior)
        (X.g.L.stKey a) ℓ.1 2 ha2 (by simpa [Ctx6.C] using hC')
  have hk4 := keyBall6_pad_self X (gr.1, KeyFlag6.interior) ℓ.1 3 hk3
  have hdist4 : HypercubeRamsey.hammingDist gr.2 ℓ.2 ≤ 4 := by
    have htri := HypercubeRamsey.hammingDist_triangle
      (X.g.L.stSign b) (X.g.L.stSign a) ℓ.2
    calc
      HypercubeRamsey.hammingDist gr.2 ℓ.2 =
          HypercubeRamsey.hammingDist (X.g.L.stSign b) ℓ.2 := by rw [← hsign]; rfl
      _ ≤ HypercubeRamsey.hammingDist (X.g.L.stSign b) (X.g.L.stSign a) +
          HypercubeRamsey.hammingDist (X.g.L.stSign a) ℓ.2 := htri
      _ ≤ 1 + 1 := Nat.add_le_add
        (HypercubeRamsey.Lane_q_s06_loads.ctx6_stNbr_sign_dist_le_one X b a ha) hgeom.2
      _ ≤ 4 := by omega
  have hsball : ℓ.2 ∈ HypercubeRamsey.hammingBall
      (show CubeVertex X.g.L.m from gr.2) 4 := by
    letI : DecidablePred (fun u : CubeVertex X.g.L.m =>
        HypercubeRamsey.hammingDist (show CubeVertex X.g.L.m from gr.2) u ≤ 4) :=
      fun u => Nat.decLe _ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist4⟩
  have hbad : ℓ ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X
      (gr.1, KeyFlag6.interior) 4 ×ˢ HypercubeRamsey.hammingBall
        (show CubeVertex X.g.L.m from gr.2) 4 :=
    Finset.mem_product.mpr ⟨hk4, hsball⟩
  simpa [HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6] using hbad

theorem target_in_bad3Scope {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (gr : X.Bin × CubeVertex X.m)
    (b : X.State) (hbin : (X.g.L.stKey b).1 = gr.1)
    (hsign : X.g.L.stSign b = gr.2) :
    X.tgt b ∈ HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr := by
  classical
  have hroot := keyBall6_contains_same_bin X gr (X.g.L.stKey b) hbin
  have hk2 := keyBall6_pad_self X (gr.1, KeyFlag6.interior) (X.g.L.stKey b) 1 hroot
  have hk3 := keyBall6_pad_self X (gr.1, KeyFlag6.interior) (X.g.L.stKey b) 2 hk2
  have hk4 := keyBall6_pad_self X (gr.1, KeyFlag6.interior) (X.g.L.stKey b) 3 hk3
  have hdist : HypercubeRamsey.hammingDist (show CubeVertex X.g.L.m from gr.2)
      (X.g.L.stSign b) = 0 := by rw [hsign]; simp [HypercubeRamsey.hammingDist]
  have hsball : (X.g.L.stSign b) ∈ HypercubeRamsey.hammingBall
      (show CubeVertex X.g.L.m from gr.2) 4 := by
    letI : DecidablePred (fun u : CubeVertex X.g.L.m =>
        HypercubeRamsey.hammingDist (show CubeVertex X.g.L.m from gr.2) u ≤ 4) :=
      fun u => Nat.decLe _ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  change X.g.L.stTarget b ∈ _
  have hprod : X.g.L.stTarget b ∈
      HypercubeRamsey.Lane_q_s06_loads.keyBall6 X (gr.1, KeyFlag6.interior) 4 ×ˢ
        HypercubeRamsey.hammingBall (show CubeVertex X.g.L.m from gr.2) 4 :=
    Finset.mem_product.mpr ⟨hk4, hsball⟩
  simpa [Ctx6.tgt, ChunkLayout6.stTarget,
    HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6] using hprod

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem bad3_congr_hidScope {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base)
    (gr : X.Bin × CubeVertex X.m) (Z Z' : X.Hid)
    (hobs : ∀ ℓ ∈ HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr,
      Z ℓ = Z' ℓ) :
    X.Bad3 b₀ gr Z ↔ X.Bad3 b₀ gr Z' := by
  apply Bad3_congr_of_scopes X b₀ gr Z Z'
    (HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr) hobs
  · intro x heven hbin hsign ℓ hℓ
    exact evenType_obs_subset_bad3Scope X gr x hbin hsign hℓ
  · intro b hb hbin hsign D hD
    have htgt := target_in_bad3Scope X gr b hbin hsign
    have hloc : X.locHid D ⊆ HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr := by
      intro ℓ hℓ
      rcases Finset.mem_biUnion.mp hℓ with ⟨e, he, hℓ⟩
      obtain ⟨a, ha, htype⟩ := absDesc_type_mem_stNbr X b D hD e he
      have hℓ' : ℓ ∈ (X.stType a).obs := by simpa [htype] using hℓ
      exact stType_obs_subset_bad3Scope X gr b a ha hbin hsign hℓ'
    exact ⟨hloc, htgt⟩

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem binAdjacent6_symm {n : ℕ} {u v : BinVector6 n}
    (h : binAdjacent6 u v) : binAdjacent6 v u := by
  rcases h with ⟨i, hrest, hdist⟩
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    exact (hrest j hj).symm
  · simpa [Nat.dist_comm] using hdist

theorem keyAdjacent6_symm {n : ℕ} {k k' : CoarseKey6 (BinVector6 n)}
    (h : keyAdjacent6 binAdjacent6 k k') : keyAdjacent6 binAdjacent6 k' k := by
  rcases h with heq | hbin | ⟨hflag, hflag', hadj⟩
  · exact Or.inl heq.symm
  · exact Or.inr (Or.inl hbin.symm)
  · exact Or.inr (Or.inr ⟨hflag', hflag, binAdjacent6_symm hadj⟩)

theorem keyBall6_concat {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (r s : ℕ) (root mid dst : X.Key)
    (hm : mid ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root r)
    (hd : dst ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X mid s) :
    dst ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root (r + s) := by
  revert r root mid dst
  induction s with
  | zero =>
      intro r root mid dst hm hd
      simp [HypercubeRamsey.Lane_q_s06_loads.keyBall6] at hd
      subst dst
      simpa using hm
  | succ s ih =>
      intro r root mid dst hm hd
      simp only [HypercubeRamsey.Lane_q_s06_loads.keyBall6, Finset.mem_biUnion] at hd
      rcases hd with ⟨v, hv, hC⟩
      have hvpath := ih r root mid v hm hv
      have hfinal := keyBall6_extend_C X root v dst (r + s) hvpath hC
      simpa [Nat.add_assoc] using hfinal

theorem keyBall6_symm {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) :
    ∀ r root k, k ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X root r →
      root ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X k r := by
  classical
  intro r
  induction r with
  | zero =>
      intro root k hk
      simp [HypercubeRamsey.Lane_q_s06_loads.keyBall6] at hk
      subst k
      simp [HypercubeRamsey.Lane_q_s06_loads.keyBall6]
  | succ r ih =>
      intro root k hk
      simp only [HypercubeRamsey.Lane_q_s06_loads.keyBall6, Finset.mem_biUnion] at hk
      rcases hk with ⟨v, hv, hC⟩
      have hvSym : root ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X v r := ih root v hv
      have hCrel : keyAdjacent6 binAdjacent6 v k := by
        simpa [Ctx6.C, keyNeighborhood6] using hC
      have hC' : v ∈ X.C k := by
        change v ∈ keyNeighborhood6 binAdjacent6 k
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, keyAdjacent6_symm hCrel⟩
      have hvBall1 : v ∈ HypercubeRamsey.Lane_q_s06_loads.keyBall6 X k 1 := by
        apply keyBall6_extend_C X k k v 0 (by simp [HypercubeRamsey.Lane_q_s06_loads.keyBall6]) hC'
      have hconcat := keyBall6_concat X 1 r k v root hvBall1 hvSym
      simpa [Nat.add_comm] using hconcat

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

noncomputable def bad3GroupsTouchProxyScope6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour}
    {M : HypercubeRamsey.TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (u : CubeVertex n) : Finset (X.Bin × CubeVertex X.m) := by
  classical
  exact Finset.univ.filter fun gr =>
    ¬ Disjoint (HypercubeRamsey.Lane_q_s06_loads.proxyHidScope6 X u)
      (HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr)

set_option maxHeartbeats 1000000 in
theorem bad3_touch_subset_radius8 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour}
    {M : HypercubeRamsey.TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (u : CubeVertex n) (gr : X.Bin × CubeVertex X.m)
    (hgr : gr ∈ bad3GroupsTouchProxyScope6 X u) :
    (gr.1, KeyFlag6.interior) ∈
        HypercubeRamsey.Lane_q_s06_loads.keyBall6 X (X.g.L.key u) 8 ∧
      (show CubeVertex X.g.L.m from gr.2) ∈
        HypercubeRamsey.hammingBall (X.g.L.sign u) 8 := by
  classical
  have hnot : ¬ Disjoint (HypercubeRamsey.Lane_q_s06_loads.proxyHidScope6 X u)
      (HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr) :=
    (Finset.mem_filter.mp hgr).2
  have hex : ∃ ℓ, ℓ ∈ HypercubeRamsey.Lane_q_s06_loads.proxyHidScope6 X u ∧
      ℓ ∈ HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr := by
    by_contra h
    apply hnot
    apply Finset.disjoint_left.mpr
    intro ℓ hℓ hℓ'
    exact h ⟨ℓ, hℓ, hℓ'⟩
  rcases hex with ⟨ℓ, hProxy, hBad⟩
  rcases Finset.mem_product.mp hProxy with ⟨hProxyKey, hProxySign⟩
  rcases Finset.mem_product.mp (by
      simpa [HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6] using hBad) with
    ⟨hBadKey, hBadSign⟩
  have hBadKeyRev := keyBall6_symm X 4 (gr.1, KeyFlag6.interior) ℓ.1 hBadKey
  have hKey8 := keyBall6_concat X 4 4 (X.g.L.key u) ℓ.1
    (gr.1, KeyFlag6.interior) hProxyKey hBadKeyRev
  let t : CubeVertex X.g.L.m := X.g.L.sign u
  let grSign : CubeVertex X.g.L.m := show CubeVertex X.g.L.m from gr.2
  have hProxyDist : HypercubeRamsey.hammingDist t ℓ.2 ≤ 4 :=
    (Finset.mem_filter.mp hProxySign).2
  have hBadDist : HypercubeRamsey.hammingDist grSign ℓ.2 ≤ 4 := by
    simpa [HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6] using
      (Finset.mem_filter.mp hBadSign).2
  have hBadDist' : HypercubeRamsey.hammingDist ℓ.2 grSign ≤ 4 := by
    simpa [HypercubeRamsey.hammingDist, ne_comm] using hBadDist
  have hdist8 : HypercubeRamsey.hammingDist t grSign ≤ 8 := by
    calc
      HypercubeRamsey.hammingDist t grSign ≤
          HypercubeRamsey.hammingDist t ℓ.2 + HypercubeRamsey.hammingDist ℓ.2 grSign :=
        HypercubeRamsey.hammingDist_triangle t ℓ.2 grSign
      _ ≤ 4 + 4 := by
        apply Nat.add_le_add hProxyDist
        exact hBadDist'
      _ ≤ 8 := by omega
  have hBall : grSign ∈ HypercubeRamsey.hammingBall t 8 := by
    change grSign ∈ Finset.univ.filter
      (fun v : CubeVertex X.g.L.m => HypercubeRamsey.hammingDist t v ≤ 8)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist8⟩
  constructor
  · exact hKey8
  · simpa [t, grSign] using hBall

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

set_option maxHeartbeats 1000000 in
theorem bad3GroupsTouchProxy_card_le {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour}
    {M : HypercubeRamsey.TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (u : CubeVertex n) :
    (bad3GroupsTouchProxyScope6 X u).card ≤ 602 ^ 8 * (9 * (X.m + 1) ^ 8) := by
  classical
  let keySet := HypercubeRamsey.Lane_q_s06_loads.keyBall6 X (X.g.L.key u) 8
  let signSet := HypercubeRamsey.hammingBall (X.g.L.sign u) 8
  let large : Finset (X.Bin × CubeVertex X.m) := Finset.univ.filter fun gr =>
    (gr.1, KeyFlag6.interior) ∈ keySet ∧
      (show CubeVertex X.g.L.m from gr.2) ∈ signSet
  have hsub : bad3GroupsTouchProxyScope6 X u ⊆ large := by
    intro gr hgr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [large, keySet, signSet] using bad3_touch_subset_radius8 X u gr hgr
  let f : X.Bin × CubeVertex X.m → X.Key × CubeVertex X.m :=
    fun gr => ((gr.1, KeyFlag6.interior), show CubeVertex X.g.L.m from gr.2)
  have hinj : Set.InjOn f (bad3GroupsTouchProxyScope6 X u : Set (X.Bin × CubeVertex X.m)) := by
    intro gr hgr gr' hgr' heq
    rcases gr with ⟨w, s⟩
    rcases gr' with ⟨w', s'⟩
    simp only [f, Prod.mk.injEq] at heq
    rcases heq with ⟨hbin, hsign⟩
    rcases hbin with ⟨hbin, _⟩
    subst w'
    subst s'
    rfl
  have himage :
      (bad3GroupsTouchProxyScope6 X u).image f ⊆ keySet ×ˢ signSet := by
    intro pair hpair
    rcases Finset.mem_image.mp hpair with ⟨gr, hgr, rfl⟩
    have hlarge := hsub hgr
    rcases (Finset.mem_filter.mp hlarge).2 with ⟨hkey, hsign⟩
    exact Finset.mem_product.mpr ⟨hkey, hsign⟩
  have hkey : keySet.card ≤ 602 ^ 8 := by
    simpa [keySet] using HypercubeRamsey.Lane_q_s06_loads.keyBall6_card_le X
      (X.g.L.key u) 8
  have hsign : signSet.card ≤ 9 * (X.m + 1) ^ 8 := by
    simpa [signSet, Ctx6.m] using
      (HypercubeRamsey.Lane_q_s06_loads.hammingBall_card_poly_le
        (r := 8) (X.g.L.sign u))
  calc
    (bad3GroupsTouchProxyScope6 X u).card =
        ((bad3GroupsTouchProxyScope6 X u).image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (keySet ×ˢ signSet).card := Finset.card_le_card himage
    _ = keySet.card * signSet.card := by rw [Finset.card_product]
    _ ≤ 602 ^ 8 * (9 * (X.m + 1) ^ 8) := Nat.mul_le_mul hkey hsign

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey
open Filter
open scoped Topology

private theorem inv_one_sub_le_exp_two {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hden : 0 < 1 - x := by linarith
  have hy : 0 < (1 - x)⁻¹ := inv_pos.mpr hden
  have hlog : Real.log ((1 - x)⁻¹) ≤ 2 * x := by
    have hlog' := Real.log_le_sub_one_of_pos hy
    have heq : (1 - x)⁻¹ - 1 = x / (1 - x) := by
      field_simp [ne_of_gt hden]
      <;> ring
    calc
      Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 := hlog'
      _ = x / (1 - x) := heq
      _ ≤ 2 * x := by
        apply (div_le_iff₀ hden).2
        nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]
  exact (Real.log_le_iff_le_exp hy).1 hlog

private theorem exp_nat_pow (x : ℝ) : ∀ k : ℕ,
    Real.exp x ^ k = Real.exp ((k : ℝ) * x) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        Real.exp x ^ (k + 1) = Real.exp x ^ k * Real.exp x := by rw [pow_succ]
        _ = Real.exp x ^ (k : ℝ) * Real.exp x := by rw [Real.rpow_natCast]
        _ = Real.exp (x * (k : ℝ)) * Real.exp x := by rw [← Real.exp_mul]
        _ = Real.exp ((k : ℝ) * x) * Real.exp x := by rw [mul_comm x]
        _ = Real.exp ((k : ℝ) * x + x) := by rw [Real.exp_add]
        _ = Real.exp (((k + 1 : ℕ) : ℝ) * x) := by
          have hargs : (k : ℝ) * x + x = ((k + 1 : ℕ) : ℝ) * x := by
            rw [Nat.cast_succ]
            ring
          exact congrArg Real.exp hargs

theorem avoidance_charge_product_le_two_pow {I : Type*} [Fintype I] [DecidableEq I]
    (T : Finset I) (x : I → ℝ) (xmax : ℝ) (k B : ℕ)
    (hx0 : 0 ≤ xmax) (hxhalf : xmax ≤ 1 / 2)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ xmax)
    (hcard : T.card ≤ k * B)
    (hsmall : 2 * xmax * (B : ℝ) ≤ Real.log 2) :
    (∏ i ∈ T, (1 - x i)⁻¹) ≤ (2 : ℝ) ^ k := by
  classical
  have hFactor (i : I) (hi : i ∈ T) : (1 - x i)⁻¹ ≤ Real.exp (2 * xmax) := by
    have hden : 0 < 1 - x i := by linarith [(hx i).2, hxhalf]
    have hdenMax : 0 < 1 - xmax := by linarith
    have hinv : (1 - x i)⁻¹ ≤ (1 - xmax)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hdenMax (by linarith [(hx i).2])
    exact hinv.trans (inv_one_sub_le_exp_two hx0 hxhalf)
  have hprod :
      (∏ i ∈ T, (1 - x i)⁻¹) ≤ (Real.exp (2 * xmax)) ^ T.card := by
    calc
      (∏ i ∈ T, (1 - x i)⁻¹) ≤ ∏ i ∈ T, Real.exp (2 * xmax) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact inv_nonneg.mpr (sub_nonneg.mpr (by linarith [(hx i).2, hxhalf]))
        · intro i hi
          exact hFactor i hi
      _ = (Real.exp (2 * xmax)) ^ T.card := by simp
  have hbase : 1 ≤ Real.exp (2 * xmax) := by
    have h := Real.add_one_le_exp (2 * xmax)
    exact le_trans (by linarith) h
  have hpow : (Real.exp (2 * xmax)) ^ T.card ≤
      (Real.exp (2 * xmax)) ^ (k * B) := pow_le_pow_right₀ hbase hcard
  have hbaseB : (Real.exp (2 * xmax)) ^ B ≤ 2 := by
    rw [exp_nat_pow]
    have hexp : (B : ℝ) * (2 * xmax) ≤ Real.log 2 := by nlinarith [hsmall]
    calc
      Real.exp ((B : ℝ) * (2 * xmax)) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = 2 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (Real.exp (2 * xmax)) ^ T.card := hprod
    _ ≤ (Real.exp (2 * xmax)) ^ (k * B) := hpow
    _ = ((Real.exp (2 * xmax)) ^ B) ^ k := by
      rw [Nat.mul_comm, pow_mul]
    _ ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hbaseB k

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

noncomputable def proxyHidScopeUnion6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour}
    {M : HypercubeRamsey.TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (U : Finset (CubeVertex n)) : Finset X.HKey :=
  U.biUnion (HypercubeRamsey.Lane_q_s06_loads.proxyHidScope6 X)

noncomputable def bad3GroupsTouchProxyUnion6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour}
    {M : HypercubeRamsey.TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (U : Finset (CubeVertex n)) : Finset (X.Bin × CubeVertex X.m) := by
  classical
  exact Finset.univ.filter fun gr =>
    ¬ Disjoint (proxyHidScopeUnion6 X U)
      (HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr)

set_option maxHeartbeats 1000000 in
theorem bad3GroupsTouchProxyUnion6_card_le {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour}
    {M : HypercubeRamsey.TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (U : Finset (CubeVertex n)) :
    (bad3GroupsTouchProxyUnion6 X U).card ≤
      U.card * (602 ^ 8 * (9 * (X.m + 1) ^ 8)) := by
  classical
  let allTouch := U.biUnion (fun u => bad3GroupsTouchProxyScope6 X u)
  have hsub : bad3GroupsTouchProxyUnion6 X U ⊆ allTouch := by
    intro gr hgr
    have hnot : ¬ Disjoint (proxyHidScopeUnion6 X U)
        (HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr) :=
      (Finset.mem_filter.mp hgr).2
    have hex : ∃ ℓ, ℓ ∈ proxyHidScopeUnion6 X U ∧
        ℓ ∈ HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr :=
      Finset.not_disjoint_iff.mp hnot
    rcases hex with ⟨ℓ, hℓ, hbad⟩
    rcases Finset.mem_biUnion.mp hℓ with ⟨u, hu, hproxy⟩
    have hnotu : ¬ Disjoint (HypercubeRamsey.Lane_q_s06_loads.proxyHidScope6 X u)
        (HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X gr) :=
      Finset.not_disjoint_iff.mpr ⟨ℓ, hproxy, hbad⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨u, hu, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotu⟩
  have hcard := Finset.card_biUnion_le (s := U)
    (t := fun u => bad3GroupsTouchProxyScope6 X u)
  calc
    (bad3GroupsTouchProxyUnion6 X U).card ≤ allTouch.card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ U, (bad3GroupsTouchProxyScope6 X u).card := by simpa [allTouch] using hcard
    _ ≤ ∑ u ∈ U, (602 ^ 8 * (9 * (X.m + 1) ^ 8)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact bad3GroupsTouchProxy_card_le X u
    _ = U.card * (602 ^ 8 * (9 * (X.m + 1) ^ 8)) := by
      simp [Finset.sum_const, nsmul_eq_mul]

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

/-- The explicit per-scope touch factor times a Step 3 LLL charge tends to zero. -/
theorem bad3_touch_charge_small_eventually {α : ℝ} (hα : 0 < α)
    (hαsmall : α ≤ 1 / 10 ^ 12) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      2 * (n : ℝ) ^ (-(δ₂ / 128)) *
        (602 ^ 8 * (9 * (Nat.ceil ((n : ℝ) ^ α) + 1) ^ 8) : ℝ) ≤ Real.log 2 := by
  let ε : ℝ := δ₂ / 128 - 8 / 10 ^ 12
  have hε : 0 < ε := by norm_num [ε, δ₂]
  let C : ℝ := 2 * (602 : ℝ) ^ 8 * 9 * 3 ^ 8
  have hC : 0 < C := by positivity
  have hdecay : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  have hEventually : ∀ᶠ n : ℕ in Filter.atTop, C * (n : ℝ) ^ (-ε) < Real.log 2 := by
    have hthreshold : 0 < Real.log 2 / C := by positivity
    filter_upwards [hdecay.eventually (Iio_mem_nhds hthreshold)] with n hn
    have hmul := mul_lt_mul_of_pos_left hn hC
    have hEq : C * (Real.log 2 / C) = Real.log 2 := by
      field_simp [ne_of_gt hC]
    exact hEq ▸ hmul
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hEventually
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hn₀' : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n from le_trans (Nat.le_max_right _ _) hn)
  have hpow : 1 ≤ (n : ℝ) ^ α := Real.one_le_rpow hn1 (le_of_lt hα)
  have hceil : (Nat.ceil ((n : ℝ) ^ α) : ℝ) < (n : ℝ) ^ α + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) α)
  have hM : ((Nat.ceil ((n : ℝ) ^ α) + 1 : ℕ) : ℝ) ≤ 3 * (n : ℝ) ^ α := by
    have hcast : ((Nat.ceil ((n : ℝ) ^ α) + 1 : ℕ) : ℝ) =
        (Nat.ceil ((n : ℝ) ^ α) : ℝ) + 1 := by simp
    rw [hcast]
    linarith
  have hMpow :
      ((Nat.ceil ((n : ℝ) ^ α) + 1 : ℕ) : ℝ) ^ 8 ≤ (3 * (n : ℝ) ^ α) ^ 8 :=
    pow_le_pow_left₀ (by positivity) hM 8
  have hAlpha8 : ((n : ℝ) ^ α) ^ 8 = (n : ℝ) ^ (8 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ))]
    congr 1
    ring
  have hexp : 8 * α - δ₂ / 128 ≤ -ε := by
    dsimp [ε]
    nlinarith [hαsmall]
  have hExpPower : (n : ℝ) ^ (-(δ₂ / 128)) * ((n : ℝ) ^ α) ^ 8 ≤
      (n : ℝ) ^ (-ε) := by
    rw [hAlpha8, ← Real.rpow_add (by positivity : 0 < (n : ℝ))]
    have hexp' : -(δ₂ / 128) + 8 * α ≤ -ε := by nlinarith [hexp]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hexp'
  have hconstant :
      2 * (n : ℝ) ^ (-(δ₂ / 128)) *
        (602 ^ 8 * (9 * (Nat.ceil ((n : ℝ) ^ α) + 1) ^ 8) : ℝ) ≤
      C * (n : ℝ) ^ (-ε) := by
    have hMpow' :
        ((Nat.ceil ((n : ℝ) ^ α) : ℝ) + 1) ^ 8 ≤ (3 * (n : ℝ) ^ α) ^ 8 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hMpow
    have hmul := mul_le_mul_of_nonneg_left hMpow'
      (by positivity : 0 ≤ 2 * (n : ℝ) ^ (-(δ₂ / 128)) * (602 : ℝ) ^ 8 * 9)
    calc
      _ = (2 * (n : ℝ) ^ (-(δ₂ / 128)) * (602 : ℝ) ^ 8 * 9) *
          ((Nat.ceil ((n : ℝ) ^ α) : ℝ) + 1) ^ 8 := by
            push_cast
            <;> ring
      _ ≤ (2 * (n : ℝ) ^ (-(δ₂ / 128)) * (602 : ℝ) ^ 8 * 9) *
          ((3 : ℝ) * (n : ℝ) ^ α) ^ 8 := hmul
      _ = C * ((n : ℝ) ^ (-(δ₂ / 128)) * ((n : ℝ) ^ α) ^ 8) := by
            dsimp [C]
            rw [mul_pow]
            <;> ring
      _ ≤ C * (n : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_left hExpPower (by positivity)
  have hsmall := hn₀ n hn₀'
  calc
    _ ≤ C * (n : ℝ) ^ (-ε) := hconstant
    _ ≤ Real.log 2 := le_of_lt hsmall

end Lane_q_s06_loads

namespace Lane_q_s06_loads
open _root_.HypercubeRamsey.S06
open OAI.HypercubeRamsey

theorem ctx6_targets_ne_of_signFar {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : HypercubeRamsey.Colour} {M : HypercubeRamsey.TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (u u' : CubeVertex n)
    (hFar : 100 * (Nat.sqrt X.m + 1) <
      _root_.hammingDist (X.g.L.sign u) (X.g.L.sign u')) :
    X.tgt (X.g.L.stateOf u) ≠ X.tgt (X.g.L.stateOf u') := by
  intro hEq
  have hsign : X.g.L.sign u = X.g.L.sign u' := by
    have h := congrArg Prod.snd hEq
    simpa [Ctx6.tgt, ChunkLayout6.stTarget, X.facts.sign_eq] using h
  rw [hsign] at hFar
  simp [HypercubeRamsey.hammingDist] at hFar

end Lane_q_s06_loads
