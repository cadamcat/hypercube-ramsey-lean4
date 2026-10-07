import HypercubeRamsey.S05.History
import HypercubeRamsey.S05.Selection
import HypercubeRamsey.S03.Height.Selection

namespace HypercubeRamsey.Lane_sol_s05_centres

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology

set_option maxHeartbeats 400000

noncomputable section

theorem local_average_tail
    {I U : Type*} [Fintype I] [DecidableEq I]
    [Fintype U] [DecidableEq U] [Nonempty U]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (P : ∀ i, FinProb (A i)) (Z : U → (∀ i, A i) → ℝ)
    (scope : U → Finset I) (hlocal : ∀ u, FinProb.DependsOn (Z u) (scope u))
    (hZ : ∀ u ω, 0 ≤ Z u ω) (L : ℝ) (hL : 0 ≤ L) (hcap : ∀ u ω, Z u ω ≤ L)
    (near : U → Finset U) (hself : ∀ u, u ∈ near u)
    (hfar : ∀ u v, v ∉ near u → Disjoint (scope u) (scope v))
    (f : ℝ) (hnear : ∀ u, ((near u).card : ℝ) ≤ f * Fintype.card U)
    (q : ℕ) (B : ℝ) (hB : 0 < B)
    (hmean : (Fintype.card U : ℝ)⁻¹ * ∑ u, (FinProb.pi P).expect (Z u) ≤ B)
    (hsmall : (q : ℝ) * f * L ≤ B) :
    (FinProb.pi P).pr (fun ω => 8 * B < (Fintype.card U : ℝ)⁻¹ * ∑ u, Z u ω) ≤
      (1 / 4 : ℝ) ^ q := by
  let μ := FinProb.pi P
  let d : U → ℝ := fun u => μ.expect (Z u)
  have hd : ∀ u, 0 ≤ d u := by
    intro u
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (hZ u ω)
  have hJoint : ∀ m : ℕ, m ≤ q → ∀ s : Fin m → U,
      (∀ i j, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ (Finset.univ : Finset (∀ i, A i)), μ.w ω * ∏ i, Z (s i) ω ≤
          (1 : ℝ) ^ m * ∏ i, d (s i) := by
    intro m _ s hsep
    have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        ∀ j ∈ (Finset.univ : Finset (Fin m)), i ≠ j →
          Disjoint (scope (s i)) (scope (s j)) := by
      intro i _ j _ hij
      rcases lt_or_gt_of_ne hij with hij' | hji'
      · exact hfar (s i) (s j) (hsep j i hij')
      · exact (hfar (s j) (s i) (hsep i j hji')).symm
    have heq := Lane_sol_s05_h5l.pi_expect_prod_disjoint P Finset.univ
      (fun i => scope (s i)) (fun i ω => Z (s i) ω)
      (fun i _ => hlocal (s i)) (fun i hi j hj hij => hdisj i hi j hj hij)
    simpa [μ, d, FinProb.expect] using heq.le
  have hMoment := scattered_moments μ.w μ.nonneg Finset.univ Z hZ L hL
    (fun u ω _ => hcap u ω) near hself f hnear q 1 (by norm_num) d hd hJoint
  let avg : (∀ i, A i) → ℝ := fun ω => (Fintype.card U : ℝ)⁻¹ * ∑ u, Z u ω
  have havg : ∀ ω, 0 ≤ avg ω := by
    intro ω
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun u _ => hZ u ω)
  have hbase : 0 ≤ (Fintype.card U : ℝ)⁻¹ * ∑ u, d u + (q : ℝ) * f * L := by
    have hf : 0 ≤ f := by
      have hc := hnear (Classical.choice (inferInstance : Nonempty U))
      have hcard : (0 : ℝ) < Fintype.card U := Nat.cast_pos.mpr Fintype.card_pos
      have hc0 : (0 : ℝ) ≤ (near (Classical.choice (inferInstance : Nonempty U))).card :=
        Nat.cast_nonneg _
      nlinarith
    exact add_nonneg
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun u _ => hd u))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hf) hL)
  have hb : (Fintype.card U : ℝ)⁻¹ * ∑ u, d u + (q : ℝ) * f * L ≤ 2 * B := by
    change (Fintype.card U : ℝ)⁻¹ * ∑ u, μ.expect (Z u) + _ ≤ _
    linarith
  have hm : μ.expect (fun ω => avg ω ^ q) ≤ (2 * B) ^ q := by
    have hm' : μ.expect (fun ω => avg ω ^ q) ≤
        ((Fintype.card U : ℝ)⁻¹ * ∑ u, d u + (q : ℝ) * f * L) ^ q := by
      simpa [μ, avg, FinProb.expect] using hMoment
    exact hm'.trans (pow_le_pow_left₀ hbase hb q)
  have hMarkov := FinProb.markov μ (fun ω => avg ω ^ q) ((8 * B) ^ q)
    (fun ω => pow_nonneg (havg ω) q) (by positivity)
  calc
    μ.pr (fun ω => 8 * B < avg ω) ≤ μ.pr (fun ω => (8 * B) ^ q ≤ avg ω ^ q) :=
      FinProb.pr_mono μ _ _ (fun ω hω => pow_le_pow_left₀ (by positivity) hω.le q)
    _ ≤ μ.expect (fun ω => avg ω ^ q) / (8 * B) ^ q := hMarkov
    _ ≤ (2 * B) ^ q / (8 * B) ^ q := div_le_div_of_nonneg_right hm (by positivity)
    _ = (1 / 4 : ℝ) ^ q := by
      rw [← div_pow]
      congr 1
      field_simp
      <;> ring

theorem odd_card (n : ℕ) (hn : 0 < n) : Fintype.card (OddRole5 n) = 2 ^ (n - 1) := by
  have hset : Fintype.card (OddRole5 n) = (Finset.univ \ evenRoleSet n).card := by
    have he : OddRole5 n ≃ {x : CubeVertex n // x ∈ Finset.univ \ evenRoleSet n} := {
      toFun := fun x => ⟨x.1, by simpa [evenRoleSet] using x.2⟩
      invFun := fun x => ⟨x.1, by simpa [evenRoleSet] using x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
    exact (Fintype.card_congr he).trans (Fintype.card_coe _)
  exact hset.trans (parity_class_card hn).2

theorem residual_complement {n m : ℕ} (g : ChunkGeometry5 n m) :
    Finset.univ \ g.residual =
      (Finset.univ.biUnion g.coarseChunks) ∪ (Finset.univ.biUnion g.fineChunks) := by
  ext i
  constructor
  · intro hi
    have h : i ∈ Finset.univ := Finset.mem_univ _
    rw [← g.chunks_cover] at h
    exact (Finset.mem_union.mp h).resolve_right (Finset.mem_sdiff.mp hi).2
  · intro hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hr
    rcases Finset.mem_union.mp hi with hc | hf
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hc
      exact Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 j) hj hr
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hf
      exact Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 j) hj hr

theorem hamming_le_residual_add {n m : ℕ} (g : ChunkGeometry5 n m) (v w : CubeVertex n) :
    hammingDist v w ≤ g.residualDist v w + (Finset.univ \ g.residual).card := by
  let D : Finset (Fin n) := Finset.univ.filter fun i => v i ≠ w i
  have hsplit := Finset.card_filter_add_card_filter_not (s := D) (p := fun i => i ∈ g.residual)
  have hres : (D.filter fun i => i ∈ g.residual).card = g.residualDist v w := by
    congr 1
    ext i
    simp [D, ChunkGeometry5.residualDist, and_comm]
  have hother : (D.filter fun i => i ∉ g.residual).card ≤ (Finset.univ \ g.residual).card :=
    Finset.card_le_card (by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
  change D.card ≤ _
  omega

theorem residual_le_embedding {n m J : ℕ} {g : ChunkGeometry5 n m}
    (S : CubeStates5 g J) (v w : CubeVertex n) :
    g.residualDist v w ≤ hammingDist (S.oneHot (S.stateOf v)) (S.oneHot (S.stateOf w)) := by
  have hcard : (g.residual.filter fun i => v i ≠ w i).card =
      ((g.residual.filter fun i => v i ≠ w i).attach.image (fun i =>
        S.resCoord ⟨i.1, (Finset.mem_filter.mp i.2).1⟩)).card := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      apply Subtype.ext
      exact congrArg (fun a : g.residual => a.1) (S.resCoord_injective hij)
  unfold ChunkGeometry5.residualDist
  rw [hcard]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [S.oneHot_residual, S.oneHot_residual]
  exact (Finset.mem_filter.mp i.2).2

theorem residual_scope_disjoint {n m J H : ℕ} {g : ChunkGeometry5 n m}
    (S : CubeStates5 g J) (v w : CubeVertex n) (R : ℕ)
    (hfar : 2 * R < g.residualDist v w) :
    Disjoint (Finset.univ.filter fun l : CubeVertex S.d × Fin (H + 1) =>
      hammingDist l.1 (S.oneHot (S.stateOf v)) ≤ R)
      (Finset.univ.filter fun l : CubeVertex S.d × Fin (H + 1) =>
        hammingDist l.1 (S.oneHot (S.stateOf w)) ≤ R) := by
  apply Finset.disjoint_left.mpr
  intro l hlv hlw
  have hv := (Finset.mem_filter.mp hlv).2
  have hw := (Finset.mem_filter.mp hlw).2
  have ht := hammingDist_triangle (S.oneHot (S.stateOf v)) l.1 (S.oneHot (S.stateOf w))
  have hr := residual_le_embedding S v w
  rw [Lane_q_s05_h5l.hammingDist_symm5 (S.oneHot (S.stateOf v)) l.1] at ht
  omega

theorem odd_near_card {n m : ℕ} (g : ChunkGeometry5 n m) (v : CubeVertex n) (R : ℕ) :
    (Finset.univ.filter fun w : OddRole5 n => g.residualDist w.1 v ≤ R).card ≤
      (hammingBall v (R + (Finset.univ \ g.residual).card)).card := by
  have hmap : Function.Injective (fun w : OddRole5 n => w.1) := Subtype.val_injective
  rw [← Finset.card_image_of_injective _ hmap]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
  have h := hamming_le_residual_add g a.1 v
  have hr := (Finset.mem_filter.mp ha).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Lane_q_s05_h5l.hammingDist_symm5]
  omega

theorem odd_near_entropy {n m : ℕ} (g : ChunkGeometry5 n m) (hn : 0 < n)
    (v : CubeVertex n) (R : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1 / 2)
    (hR : (R + (Finset.univ \ g.residual).card : ℕ) ≤ q * (n : ℝ)) :
    ((Finset.univ.filter fun w : OddRole5 n => g.residualDist w.1 v ≤ R).card : ℝ) ≤
      (2 * Real.exp (-(Real.log 2 - Real.binEntropy q) * n)) * Fintype.card (OddRole5 n) := by
  let rad := R + (Finset.univ \ g.residual).card
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrhalf : rad ≤ n / 2 := by
    have hh : (2 * rad : ℕ) < n := by
      have hh' : (2 : ℝ) * rad < n := by
        have h1 := mul_lt_mul_of_pos_right hq hnpos
        dsimp [rad]
        linarith
      exact_mod_cast hh'
    omega
  have hratio : (rad : ℝ) / n ≤ q := (div_le_iff₀ hnpos).2 hR
  have hent : Real.binEntropy ((rad : ℝ) / n) ≤ Real.binEntropy q :=
    Real.binEntropy_strictMonoOn.monotoneOn
      ⟨by positivity, by linarith⟩ ⟨hq0, by norm_num; linarith⟩ hratio
  have hb := hammingBall_volume_bound hn hrhalf v
  have hc := odd_near_card g v R
  have hodd : 2 * (Fintype.card (OddRole5 n) : ℝ) = (2 : ℝ) ^ n := by
    rw [odd_card n hn]
    push_cast
    rw [← pow_succ']
    congr 1
    omega
  have hpow : (2 : ℝ) ^ n = Real.exp (Real.log 2 * n) := by
    calc
      _ = (Real.exp (Real.log 2)) ^ n := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp (Real.log 2 * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ ((hammingBall v rad).card : ℝ) := by exact_mod_cast hc
    _ ≤ Real.exp (Real.binEntropy ((rad : ℝ) / n) * n) := hb
    _ ≤ Real.exp (Real.binEntropy q * n) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hent (Nat.cast_nonneg _))
    _ = (2 * Real.exp (-(Real.log 2 - Real.binEntropy q) * n)) * Fintype.card (OddRole5 n) := by
      rw [show (2 * Real.exp (-(Real.log 2 - Real.binEntropy q) * n)) *
        Fintype.card (OddRole5 n) = Real.exp (-(Real.log 2 - Real.binEntropy q) * n) *
          (2 * (Fintype.card (OddRole5 n) : ℝ)) by ring, hodd, hpow, ← Real.exp_add]
      congr 1
      ring

end
end HypercubeRamsey.Lane_sol_s05_centres
