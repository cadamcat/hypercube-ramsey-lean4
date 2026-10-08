import HypercubeRamsey.S05.Centres_sol_s05_centres_marking

namespace HypercubeRamsey.Lane_sol_s05_centres

open Classical Filter Real OAI.HypercubeRamsey
open scoped BigOperators Topology
set_option maxHeartbeats 400000
noncomputable section
variable {γ K' χ : ℝ}

theorem height_admissible (p : Params5 γ K' χ) :
    HDAdmissible 10 (p.alpha / 10000) (p.alpha / 2000) (p.alpha / 1000000)
      (p.alpha / 100000) (1 - p.alpha / 100000) (p.alpha / 20000) (1 / 2) 2 8 := by
  have hα := p.halpha.1
  have hα' := p.halpha.2
  refine {
    hJ := by norm_num
    hb := ⟨by positivity, by linarith, by linarith⟩
    hD := by norm_num
    hsz := ⟨by positivity, by linarith, by linarith, by linarith, by linarith⟩
    ha := ⟨by linarith, by linarith, by linarith⟩
    hd := by norm_num }

def heightRegime (p : Params5 γ K' χ) : HDRegime (p.alpha / 10000) (p.alpha / 2000) 8 :=
  .lin (p.rho / 4) ⟨by have := p.hrho.1; positivity, by linarith [p.hrho.2]⟩

theorem height_regime_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, ∀ (m J : ℕ) (g : ChunkGeometry5 n m) (S : CubeStates5 g J),
      (1 / 2 : ℝ) * n ≤ S.d ∧ (S.d : ℝ) ≤ 2 * n ∧
        (heightRegime p).ok n S.d ⌊p.rho * n⌋₊ := by
  let c : ℝ := min (1 / 6) (1 - 4 * p.rho)
  have hc : 0 < c := by dsimp [c]; apply lt_min <;> linarith [p.hrho.2]
  have hρ := p.hrho.1
  have hlarge : ∀ᶠ n : ℕ in atTop, (2 / p.rho : ℝ) ≤ n :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [sublinear_power_eventually (1 / 2) c (by norm_num) hc,
    hlarge, eventually_ge_atTop (602 : ℕ)] with n hsqrt hlarge hn
  intro m J g S
  have hocc : ((Finset.univ \ g.residual).card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [residual_complement g]
    exact g.occupied_sublinear
  have hres : g.residual.card ≤ S.d := by
    simpa using Fintype.card_le_of_injective S.resCoord S.resCoord_injective
  have hcard : (Finset.univ \ g.residual).card + g.residual.card = n := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ g.residual)
  have hresR : (g.residual.card : ℝ) ≤ S.d := by exact_mod_cast hres
  have hcardR : ((Finset.univ \ g.residual).card : ℝ) + g.residual.card = n := by
    exact_mod_cast hcard
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hsmall : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (1 / 6 : ℝ) * n :=
    hsqrt.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have hsmallρ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (1 - 4 * p.rho) * n :=
    hsqrt.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hlower : (1 / 2 : ℝ) * n ≤ S.d := by linarith
  have hupper : (S.d : ℝ) ≤ 2 * n := by
    have hd := S.dimension_upper
    have hnR : (602 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨hlower, hupper, ?_⟩
  change p.rho / 4 * S.d ≤ ⌊p.rho * n⌋₊ ∧ 4 * ⌊p.rho * n⌋₊ ≤ S.d
  have hfloor : (⌊p.rho * n⌋₊ : ℝ) ≤ p.rho * n := Nat.floor_le (mul_nonneg hρ.le hn0)
  have hfloor' : p.rho * n < (⌊p.rho * n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hscale : 2 ≤ p.rho * (n : ℝ) := by
    have hh := (div_le_iff₀ hρ).1 hlarge
    nlinarith
  constructor
  · have hh := mul_le_mul_of_nonneg_left hupper (div_nonneg hρ.le (by norm_num : (0 : ℝ) ≤ 4))
    nlinarith
  · have hd : (4 : ℝ) * ⌊p.rho * n⌋₊ ≤ S.d := by linarith
    exact_mod_cast hd

theorem geometricScale_exists (R M T : ℕ) (hR : 1 ≤ R) (hM : 2 ≤ M) :
    ∃ k : ℕ, T ≤ M ^ k * R := by
  have hp : T < M ^ T := Nat.lt_pow_self (by omega : 1 < M)
  exact ⟨T, hp.le.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < R))⟩

theorem geometricScale_bound (R M T : ℕ) (hR : 1 ≤ R) (hM : 2 ≤ M) (hRT : R < T) :
    M ^ Nat.find (geometricScale_exists R M T hR hM) * R ≤ M * T := by
  let k := Nat.find (geometricScale_exists R M T hR hM)
  have hk : T ≤ M ^ k * R := Nat.find_spec (geometricScale_exists R M T hR hM)
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    simp only [pow_zero, one_mul] at hk
    omega
  have hp : M ^ (k - 1) * R < T := by
    have hh := Nat.find_min (geometricScale_exists R M T hR hM)
      (show k - 1 < k by omega)
    exact Nat.lt_of_not_ge hh
  change M ^ k * R ≤ _
  rw [show k = (k - 1) + 1 by omega, pow_succ]
  calc
    _ = M * (M ^ (k - 1) * R) := by ring
    _ ≤ M * T := Nat.mul_le_mul_left M hp.le

theorem topScale_power_bound (σ ζ : ℝ) (hσ : 0 < σ) (hζ : ζ < 1) :
    ∀ᶠ n : ℕ in atTop, (topScale n σ ζ : ℝ) ≤ 4 * (n : ℝ) ^ (1 + σ - ζ) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - ζ)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hζ)).comp tendsto_natCast_atTop_atTop
  have hl := ((isLittleO_log_rpow_rpow_atTop 2 (sub_pos.mpr hζ)).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hl, ht.eventually_ge_atTop 4, eventually_ge_atTop (1 : ℕ)] with n hlog htarget hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog' : log (n : ℝ) ^ 2 ≤ (1 / 4 : ℝ) * (n : ℝ) ^ (1 - ζ) := by
    simpa only [Function.comp_apply, rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (log (n : ℝ))), abs_of_nonneg (rpow_nonneg hnpos.le _)] using hlog
  let R : ℕ := max 1 ⌈log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let T : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hR : (R : ℝ) ≤ log (n : ℝ) ^ 2 + 1 := by
    dsimp [R]
    rw [Nat.cast_max]
    norm_num only
    apply max_le
    · nlinarith [sq_nonneg (log (n : ℝ))]
    · exact (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hT : (n : ℝ) ^ (1 - ζ) ≤ T := Nat.le_ceil _
  have hRT : R < T := by
    have hh : (R : ℝ) < T := by linarith
    exact_mod_cast hh
  have hM : (M : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
    dsimp [M]
    rw [Nat.cast_max]
    norm_num only
    have hpow : 1 ≤ (n : ℝ) ^ σ := one_le_rpow hnR hσ.le
    apply max_le
    · nlinarith
    · have hh := Nat.ceil_lt_add_one (rpow_nonneg hnpos.le σ)
      linarith
  have hT' : (T : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) := by
    have hh := Nat.ceil_lt_add_one (rpow_nonneg hnpos.le (1 - ζ))
    change (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) ≤ _
    linarith
  have hscale : topScale n σ ζ ≤ M * T := by
    unfold topScale
    exact geometricScale_bound R M T (le_max_left _ _) (le_max_left _ _) hRT
  calc
    (topScale n σ ζ : ℝ) ≤ (M : ℝ) * T := by exact_mod_cast hscale
    _ ≤ (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ)) :=
      mul_le_mul hM hT' (Nat.cast_nonneg _) (by positivity)
    _ = 4 * (n : ℝ) ^ (1 + σ - ζ) := by
      rw [show 1 + σ - ζ = σ + (1 - ζ) by ring, rpow_add hnpos]
      ring

theorem embedding_distance_upper {n m J : ℕ} {g : ChunkGeometry5 n m}
    (S : CubeStates5 g J) (x y : CubeVertex n) :
    hammingDist (S.oneHot (S.stateOf x)) (S.oneHot (S.stateOf y)) ≤
      g.residualDist x y + (S.d - g.residual.card) := by
  classical
  let I : Finset (Fin S.d) := Finset.univ.image S.resCoord
  let D : Finset (Fin S.d) := Finset.univ.filter fun i =>
    S.oneHot (S.stateOf x) i ≠ S.oneHot (S.stateOf y) i
  let M := g.residual.filter fun i => x i ≠ y i
  let f : M → Fin S.d := fun i => S.resCoord ⟨i.1, (Finset.mem_filter.mp i.2).1⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun a : g.residual => a.1) (S.resCoord_injective hij)
  have hI : I.card = g.residual.card := by
    simp [I, Finset.card_image_of_injective _ S.resCoord_injective]
  have hM : (Finset.univ.image f).card = M.card := by
    simp [Finset.card_image_of_injective _ hf]
  have hfirst : (D.filter fun i => i ∈ I).card ≤ M.card := by
    rw [← hM]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).2
    have hneq := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hxy : x a.1 ≠ y a.1 := by
      rw [← ha, S.oneHot_residual, S.oneHot_residual] at hneq
      exact hneq
    refine Finset.mem_image.mpr ⟨⟨a.1, Finset.mem_filter.mpr ⟨a.2, hxy⟩⟩, Finset.mem_univ _, ?_⟩
    exact ha
  have hlast : (D.filter fun i => i ∉ I).card ≤ S.d - g.residual.card := by
    calc
      _ ≤ (Finset.univ \ I).card := Finset.card_le_card (by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
      _ = S.d - g.residual.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, Fintype.card_fin, hI]
  have hsplit := Finset.card_filter_add_card_filter_not (s := D) (p := fun i => i ∈ I)
  change D.card ≤ M.card + _
  omega

theorem adjacent_embedding_upper {n m J : ℕ} {g : ChunkGeometry5 n m}
    (S : CubeStates5 g J) (x y : CubeVertex n) (hxy : (cube n).Adj x y) :
    (hammingDist (S.oneHot (S.stateOf x)) (S.oneHot (S.stateOf y)) : ℝ) ≤
      4 * (n : ℝ) ^ (1 / 2 : ℝ) + 302 := by
  have hdist : hammingDist x y = 1 := hxy
  have hres : g.residualDist x y ≤ 1 := by
    calc
      _ ≤ hammingDist x y := Finset.card_le_card (by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
      _ = 1 := hdist
  have hdim : g.residual.card ≤ S.d := by
    simpa using Fintype.card_le_of_injective S.resCoord S.resCoord_injective
  have hcard : (Finset.univ \ g.residual).card + g.residual.card = n := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ g.residual)
  have hocc : ((Finset.univ \ g.residual).card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [residual_complement g]
    exact g.occupied_sublinear
  have hcardR : ((Finset.univ \ g.residual).card : ℝ) + g.residual.card = n := by exact_mod_cast hcard
  have hd := S.dimension_upper
  have hupper : hammingDist (S.oneHot (S.stateOf x)) (S.oneHot (S.stateOf y)) ≤
      1 + (S.d - g.residual.card) := (embedding_distance_upper S x y).trans (Nat.add_le_add_right hres _)
  have hupperR : (hammingDist (S.oneHot (S.stateOf x)) (S.oneHot (S.stateOf y)) : ℝ) ≤
      1 + ((S.d - g.residual.card : ℕ) : ℝ) := by exact_mod_cast hupper
  rw [Nat.cast_sub hdim] at hupperR
  linarith

theorem nat_power_margin (A a b : ℝ) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop A, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh := mul_le_mul_of_nonneg_left hn (rpow_nonneg hnpos.le a)
  have he : (n : ℝ) ^ a * (n : ℝ) ^ (b - a) = (n : ℝ) ^ b := by
    rw [← rpow_add hnpos]
    congr 1
    ring
  simpa only [he, mul_comm] using hh

def centreSlack (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  32 * topScale n (p.alpha / 1000000) (p.alpha / 100000) +
    4 * ⌈(n : ℝ) ^ (1 / 2 : ℝ)⌉₊ + 333

theorem centreSlack_small_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, (centreSlack p n : ℝ) ≤ (n : ℝ) ^ (1 - 9 * p.alpha / 4000000) := by
  let a : ℝ := 1 - 9 * p.alpha / 1000000
  let b : ℝ := 1 - 9 * p.alpha / 4000000
  have hab : a < b := by dsimp [a, b]; linarith [p.halpha.1]
  have hb : 1 / 2 < b := by dsimp [b]; linarith [p.halpha.2]
  filter_upwards [topScale_power_bound (p.alpha / 1000000) (p.alpha / 100000)
    (by have := p.halpha.1; positivity) (by linarith [p.halpha.2]),
    nat_power_margin 384 a b hab, nat_power_margin 12 (1 / 2) b hb,
    nat_power_margin 1011 0 b (by linarith), eventually_ge_atTop (1 : ℕ)]
    with n htop h1 h2 h3 hn
  have hexp : 1 + p.alpha / 1000000 - p.alpha / 100000 = a := by dsimp [a]; ring
  rw [hexp] at htop
  simp only [rpow_zero, mul_one] at h3
  have hceil : (⌈(n : ℝ) ^ (1 / 2 : ℝ)⌉₊ : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (rpow_nonneg (Nat.cast_nonneg _) _)).le
  change (centreSlack p n : ℝ) ≤ (n : ℝ) ^ b
  dsimp [centreSlack]
  push_cast
  linarith

theorem centreSlack_scope (p : Params5 γ K' χ) (n : ℕ) :
    16 * topScale n (p.alpha / 1000000) (p.alpha / 100000) +
      16 + (4 * (n : ℝ) ^ (1 / 2 : ℝ) + 302) ≤ (centreSlack p n : ℝ) := by
  have hceil : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (⌈(n : ℝ) ^ (1 / 2 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have htop : (0 : ℝ) ≤ topScale n (p.alpha / 1000000) (p.alpha / 100000) := Nat.cast_nonneg _
  dsimp [centreSlack]
  push_cast
  linarith

end
end HypercubeRamsey.Lane_sol_s05_centres
