import HypercubeRamsey.S10.LocalNodes
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.Framework.Props
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.S03.ScatteredMoments
import HypercubeRamsey.S03.Mixtures
import HypercubeRamsey.S03.Height.Selection

/-!
# P10.1k helper lemmas

This file contains the exact binary chunk coordinate decomposition and finite
product estimates used in the Section 10 construction. Likelihood factors are
nonnegative, which is needed when multiplying pointwise bounds over groups.
-/

namespace HypercubeRamsey.S10

open scoped BigOperators
open Filter
open OAI.HypercubeRamsey

/-- A fixed multiplicative gap between distinct powers is eventually absorbed. -/
private theorem p10_1k_eventually_power_gap {a b c : ℝ}
    (hab : a < b) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  have hlarge := htend.eventually_gt_atTop c
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hlarge, hnlarge] with n hlarge hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

/-- A polynomial power is dominated by an exponential of any strictly larger
power. -/
private theorem p10_1k_power_exp_neg_tendsto {a b c : ℝ}
    (ha : 0 < a) (hba : b < a) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ b * Real.exp (-c * (n : ℝ) ^ a))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (_root_.tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hscaled : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ a) ^ (b / a) *
        Real.exp (-c * (n : ℝ) ^ a)) atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b / a) c hc).comp hpow
  have heq :
      (fun n : ℕ => (n : ℝ) ^ b * Real.exp (-c * (n : ℝ) ^ a)) =ᶠ[atTop]
        (fun n : ℕ => ((n : ℝ) ^ a) ^ (b / a) *
          Real.exp (-c * (n : ℝ) ^ a)) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hexp : a * (b / a) = b := by field_simp [ne_of_gt ha]
    have hpower : (n : ℝ) ^ b = ((n : ℝ) ^ a) ^ (b / a) := by
      calc
        (n : ℝ) ^ b = (n : ℝ) ^ (a * (b / a)) := by rw [hexp]
        _ = ((n : ℝ) ^ a) ^ (b / a) := Real.rpow_mul hnpos.le a (b / a)
    simp [hpower]
  exact Tendsto.congr' heq.symm hscaled

/-- A tag names one pair of sides to discard from the available patch. -/
def P10_1kTagIndex (N : ℕ) (κ : ℝ) :=
  {R : Finset (Fin N) × Finset (Fin N) //
    (R.1.card : ℝ) ≤ κ * (N : ℝ) ∧ (R.2.card : ℝ) ≤ κ * (N : ℝ)}

/-- The bounded-discard tag index is a finite type. -/
@[instance_reducible]
noncomputable def p10_1kTagIndexFintype (N : ℕ) (κ : ℝ) :
    Fintype (P10_1kTagIndex N κ) := by
  classical
  let S : Finset (Finset (Fin N) × Finset (Fin N)) := Finset.univ.filter fun R =>
    (R.1.card : ℝ) ≤ κ * (N : ℝ) ∧ (R.2.card : ℝ) ≤ κ * (N : ℝ)
  change Fintype {R : Finset (Fin N) × Finset (Fin N) //
    (R.1.card : ℝ) ≤ κ * (N : ℝ) ∧ (R.2.card : ℝ) ≤ κ * (N : ℝ)}
  exact Fintype.ofFinset S (by
    intro R
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl)

/-- A cluster patch witness that survives a fixed pair of discards. -/
structure P10_1kPatchWitness {n N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (X Y : Finset (Fin N)) (ζ δ : ℝ)
    (RX RY : Finset (Fin N)) where
  A : Finset (Fin N)
  B : Finset (Fin N)
  patch : (A, B) ∈ PCluster G ζ δ n N E
  first_subset : A ⊆ X \ RX
  second_subset : B ⊆ Y \ RY

/-- The laws and estimates encoded in a PCluster witness. -/
structure P10_1kClusterData {n N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (ζ δ : ℝ) (A B : Finset (Fin N)) where
  μ : Law N
  K : ℕ
  lam : Fin K → ℝ
  D : Fin K → Law N
  μ_supported : μ.SupportedIn A
  D_supported : ∀ j, (D j).SupportedIn B
  lam_nonneg : ∀ j, 0 ≤ lam j
  lam_sum : ∑ j, lam j = 1
  μ_width : μ.WidthLE ((n : ℝ) ^ δ)
  aggregate_width : ∀ y, ∑ j, lam j * (D j).w y ≤ Real.exp ((n : ℝ) ^ δ) / N
  D_atom : ∀ j y, (D j).w y ≤ Real.exp (-((n : ℝ) ^ ζ))
  codegree : ∀ j, 0 < lam j → ∀ y y', 0 < (D j).w y → 0 < (D j).w y' →
    1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ y y'

/-- Height-device exponents used by the Section 10 projection experiment. -/
theorem p10_1k_heightAdmissible (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : δ < (1 : ℝ) / 2000) :
    HDAdmissible 10 (50 * δ) (140 * δ) δ (8 * δ) (1 - δ) (20 * δ)
      (1 / 2) 1 6 := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hδ, hδsmall]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [hδ, hδsmall]
  · refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hδ, hδsmall]
  · exact ⟨by norm_num, by norm_num⟩

/-- The sublinear radius regime for the Section 10 height device. -/
def p10_1k_heightRegime (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : δ < (1 : ℝ) / 2000) : HDRegime (50 * δ) (140 * δ) 6 := by
  refine HDRegime.sub (10 * δ) ⟨?_, ?_, ?_⟩
  · positivity
  · nlinarith [hδsmall]
  · have hcoeff :
        (50 + ((6 : ℝ) + 1) * 10) * δ < 140 * δ :=
      mul_lt_mul_of_pos_right (by norm_num) hδ
    calc
      50 * δ + ((6 : ℝ) + 1) * (10 * δ) =
          (50 + ((6 : ℝ) + 1) * 10) * δ := by ring
      _ < 140 * δ := hcoeff

/-- Concrete height-device parameters for one residual slice. -/
noncomputable def p10_1kHeightParams (n m : ℕ) (δ : ℝ) : HDParams where
  n := n
  d := n - m
  D := 6
  r := ⌊(n : ℝ) ^ (1 - 10 * δ)⌋₊
  H := topScale n δ (8 * δ)
  lam := (n : ℝ) ^ 10
  b₀ := 50 * δ
  b := 140 * δ

/-- The concrete radius is in the sublinear height regime. -/
theorem p10_1kHeightParams_subRegime_ok (n m : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ < (1 : ℝ) / 2000) :
    (p10_1k_heightRegime δ hδ hδsmall).ok n (n - m)
      (p10_1kHeightParams n m δ).r := by
  rfl

/-- The residual dimension left after removing the special bits remains a
fixed positive fraction of the ambient dimension, eventually. -/
theorem p10_1kHeightParams_dimension_eventually (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * (n : ℝ) ≤
          (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).d ∧
        (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).d ≤ n := by
  have hscale := p10_1b_scale_separation η₀ ζ δ hη₀ hζ hδ hδsmall
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hscale, hnlarge] with n hscale hn
  have hthird : 4 * (n : ℝ) ^ (200 * δ) < (n : ℝ) ^ (1 - δ) := hscale.2.2.1
  let m : ℕ := ⌊(n : ℝ) ^ (200 * δ)⌋₊
  have hnreal : 1 ≤ (n : ℝ) := by
    exact_mod_cast (show (1 : ℕ) ≤ n by omega)
  have hpow : (n : ℝ) ^ (1 - δ) ≤ (n : ℝ) := by
    calc
      (n : ℝ) ^ (1 - δ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnreal (sub_le_self 1 hδ.le)
      _ = (n : ℝ) := by rw [Real.rpow_one]
  have hmcast : (m : ℝ) ≤ (n : ℝ) ^ (200 * δ) := by
    dsimp [m]
    exact Nat.floor_le (by positivity)
  have h4m : 4 * (m : ℝ) < (n : ℝ) := by
    calc
      4 * (m : ℝ) ≤ 4 * (n : ℝ) ^ (200 * δ) :=
        mul_le_mul_of_nonneg_left hmcast (by norm_num)
      _ < (n : ℝ) ^ (1 - δ) := hthird
      _ ≤ (n : ℝ) := hpow
  have hmle : m ≤ n := by
    exact_mod_cast (by nlinarith [h4m] : (m : ℝ) ≤ (n : ℝ))
  have hsub : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) :=
    Nat.cast_sub hmle
  constructor
  · change (1 / 2 : ℝ) * (n : ℝ) ≤ (n - m : ℕ)
    rw [hsub]
    nlinarith [h4m]
  · change (n - m : ℕ) ≤ n
    exact Nat.sub_le _ _

/-- The long height radius fits in the residual cube dimension, eventually.
This is the geometric side condition for `height_position_counts`. -/
theorem p10_1kHeightParams_radius_le_dimension_eventually (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).r ≤
        (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).d := by
  have hscale := p10_1b_scale_separation η₀ ζ δ hη₀ hζ hδ hδsmall
  have hlargeExp : ∀ᶠ n : ℕ in atTop, 2 < (n : ℝ) ^ (10 * δ) := by
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (10 * δ)) atTop atTop :=
      (_root_.tendsto_rpow_atTop (by positivity : 0 < 10 * δ)).comp
        tendsto_natCast_atTop_atTop
    exact htend.eventually_gt_atTop 2
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hscale, hlargeExp, hnlarge] with n hscale hpow hn
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by omega)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hthird : 4 * (n : ℝ) ^ (200 * δ) < (n : ℝ) ^ (1 - δ) :=
    hscale.2.2.1
  have hpowr : 2 * (n : ℝ) ^ (1 - 10 * δ) ≤ (n : ℝ) := by
    calc
      2 * (n : ℝ) ^ (1 - 10 * δ) ≤
          (n : ℝ) ^ (10 * δ) * (n : ℝ) ^ (1 - 10 * δ) :=
        mul_le_mul_of_nonneg_right hpow.le (Real.rpow_nonneg hnpos.le _)
      _ = (n : ℝ) := by
        rw [← Real.rpow_add hnpos]
        rw [show 10 * δ + (1 - 10 * δ) = (1 : ℝ) by ring, Real.rpow_one]
  let m : ℕ := ⌊(n : ℝ) ^ (200 * δ)⌋₊
  let r : ℕ := ⌊(n : ℝ) ^ (1 - 10 * δ)⌋₊
  have hmcast : (m : ℝ) ≤ (n : ℝ) ^ (200 * δ) := by
    dsimp [m]
    exact Nat.floor_le (by positivity)
  have hrcast : (r : ℝ) ≤ (n : ℝ) ^ (1 - 10 * δ) := by
    dsimp [r]
    exact Nat.floor_le (by positivity)
  have h2r : 2 * (r : ℝ) ≤ (n : ℝ) :=
    (mul_le_mul_of_nonneg_left hrcast (by norm_num : (0 : ℝ) ≤ 2)).trans hpowr
  have hpow_le_base : (n : ℝ) ^ (1 - δ) ≤ (n : ℝ) := by
    calc
      (n : ℝ) ^ (1 - δ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnreal (sub_le_self 1 hδ.le)
      _ = (n : ℝ) := by rw [Real.rpow_one]
  have h4m : 4 * (m : ℝ) < (n : ℝ) := by
    calc
      4 * (m : ℝ) ≤ 4 * (n : ℝ) ^ (200 * δ) :=
        mul_le_mul_of_nonneg_left hmcast (by norm_num)
      _ < (n : ℝ) ^ (1 - δ) := hthird
      _ ≤ (n : ℝ) := hpow_le_base
  have hsum_real : (r : ℝ) + (m : ℝ) ≤ (n : ℝ) := by
    nlinarith
  have hsum : r + m ≤ n := by exact_mod_cast hsum_real
  change r ≤ n - m
  exact Nat.le_sub_of_add_le hsum

/-- The height-device position probability is at most one, eventually. Its
radius ball contains the twentieth Hamming layer, whose volume dominates the
chosen polynomial activity parameter. -/
theorem p10_1kHeightParams_activity_le_volume_eventually (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).lam ≤
        ((p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).V : ℝ) := by
  have hdim := p10_1kHeightParams_dimension_eventually η₀ ζ δ hη₀ hζ hδ hδsmall
  have hδsmall' : δ < (1 : ℝ) / 2000 := by
    calc
      δ < min (min η₀ ζ) 1 / 2000 := hδsmall
      _ ≤ 1 / 2000 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hexp : 0 < 1 - 10 * δ := by nlinarith [hδsmall']
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - 10 * δ)) atTop atTop :=
    (_root_.tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  have hr20 : ∀ᶠ n : ℕ in atTop,
      20 ≤ ⌊(n : ℝ) ^ (1 - 10 * δ)⌋₊ := by
    filter_upwards [htend.eventually_gt_atTop 20] with n hn
    exact Nat.le_floor hn.le
  have hnlarge : ∀ᶠ n : ℕ in atTop, 100000 ≤ n :=
    Filter.eventually_atTop.mpr ⟨100000, fun _ hn => hn⟩
  filter_upwards [hdim, hr20, hnlarge] with n hdim hr20 hn
  let m : ℕ := ⌊(n : ℝ) ^ (200 * δ)⌋₊
  let p : HDParams := p10_1kHeightParams n m δ
  have hd : (1 / 2 : ℝ) * (n : ℝ) ≤ (p.d : ℝ) := by
    simpa [p, m, p10_1kHeightParams] using hdim.1
  have hr : 20 ≤ p.r := by
    simpa [p, p10_1kHeightParams] using hr20
  have hndReal : (n : ℝ) ≤ 2 * (p.d : ℝ) := by nlinarith [hd]
  have hnd : n ≤ 2 * p.d := by exact_mod_cast hndReal
  have hdlarge : 60 ≤ p.d := by omega
  have hbaseNat : n ≤ 3 * (p.d + 1 - 20) := by omega
  have hbaseCast : (n : ℝ) ≤ 3 * ((p.d + 1 - 20 : ℕ) : ℝ) := by
    exact_mod_cast hbaseNat
  have hbase : (n : ℝ) / 3 ≤ ((p.d + 1 - 20 : ℕ) : ℝ) := by nlinarith
  have hchoose :
      ((p.d + 1 - 20 : ℕ) : ℝ) ^ 20 / (Nat.factorial 20 : ℝ) ≤
        (Nat.choose p.d 20 : ℝ) := by
    exact Nat.pow_le_choose 20 p.d
  have hbig : (3 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ) ≤ (n : ℝ) ^ 10 := by
    have hncast : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc
      (3 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ) ≤ (100000 : ℝ) ^ 10 := by norm_num
      _ ≤ (n : ℝ) ^ 10 := by gcongr
  have hmul :
      (3 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ) * (n : ℝ) ^ 10 ≤
        (n : ℝ) ^ 20 := by
    have hmul' := mul_le_mul_of_nonneg_right hbig (by positivity : 0 ≤ (n : ℝ) ^ 10)
    have hpow20 : (n : ℝ) ^ 20 = ((n : ℝ) ^ 10) ^ 2 := by
      rw [← pow_mul]
    rw [hpow20]
    nlinarith [hmul']
  have hnchoose : (n : ℝ) ^ 10 ≤ ((n : ℝ) / 3) ^ 20 /
      (Nat.factorial 20 : ℝ) := by
    apply (le_div_iff₀ (by positivity : 0 < (Nat.factorial 20 : ℝ))).2
    rw [div_pow]
    apply (le_div_iff₀ (by positivity : 0 < (3 : ℝ) ^ 20)).2
    have hpow20 : (n : ℝ) ^ 20 = ((n : ℝ) ^ 10) ^ 2 := by
      rw [← pow_mul]
    rw [hpow20]
    nlinarith [hmul]
  have hbasePow : ((n : ℝ) / 3) ^ 20 ≤
      ((p.d + 1 - 20 : ℕ) : ℝ) ^ 20 := by
    gcongr
  have hchooseLower : (n : ℝ) ^ 10 ≤ (Nat.choose p.d 20 : ℝ) := by
    calc
      (n : ℝ) ^ 10 ≤ ((n : ℝ) / 3) ^ 20 /
          (Nat.factorial 20 : ℝ) := hnchoose
      _ ≤ ((p.d + 1 - 20 : ℕ) : ℝ) ^ 20 /
          (Nat.factorial 20 : ℝ) :=
        div_le_div_of_nonneg_right hbasePow (by positivity)
      _ ≤ (Nat.choose p.d 20 : ℝ) := hchoose
  have h20mem : 20 ∈ Finset.range (p.r + 1) :=
    Finset.mem_range.mpr (by omega)
  have hvolumeNat : Nat.choose p.d 20 ≤ p.V := by
    change Nat.choose p.d 20 ≤
      ∑ i ∈ Finset.range (p.r + 1), Nat.choose p.d i
    exact Finset.single_le_sum (fun i hi => Nat.zero_le _) h20mem
  have hvolume : (Nat.choose p.d 20 : ℝ) ≤ (p.V : ℝ) := by exact_mod_cast hvolumeNat
  change (n : ℝ) ^ 10 ≤ (p.V : ℝ)
  exact hchooseLower.trans hvolume

/-- The height-device uniform position-count estimate applies to every finite
site set in the projected residual cube, eventually. -/
theorem p10_1kHeightParams_position_counts_eventually (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      ∀ Sites : (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).Sites,
        (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).posLaw.pr
          (fun P => ∃ v ∈ Sites, ∃ j : Fin ((p10_1kHeightParams n
            ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).H + 1),
            let count := (Finset.univ.filter (fun u : CubeVertex
              (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).d =>
              P (u, j) = true ∧ hammingDist u v ≤
                (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).r)).card
            ((count : ℝ) < (p10_1kHeightParams n
              ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).lam / 2 ∨
              2 * (p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).lam <
                (count : ℝ))) ≤
          2 * (Sites.card : ℝ) *
            (((p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).H + 1 : ℕ) : ℝ) *
            Real.exp (-(p10_1kHeightParams n
              ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ).lam / 12) := by
  have hdim := p10_1kHeightParams_dimension_eventually η₀ ζ δ hη₀ hζ hδ hδsmall
  have hrad := p10_1kHeightParams_radius_le_dimension_eventually
    η₀ ζ δ hη₀ hζ hδ hδsmall
  have hvolume := p10_1kHeightParams_activity_le_volume_eventually
    η₀ ζ δ hη₀ hζ hδ hδsmall
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hdim, hrad, hvolume, hnlarge] with n hdim hrad hvolume hn
  let m : ℕ := ⌊(n : ℝ) ^ (200 * δ)⌋₊
  let p : HDParams := p10_1kHeightParams n m δ
  have hrad' : p.r ≤ p.d := by
    simpa [p, p10_1kHeightParams] using hrad
  have hnreal : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show (0 : ℕ) < n by omega)
  have hlam : 0 < p.lam := by
    dsimp [p, p10_1kHeightParams]
    exact pow_pos hnreal _
  have hvolume' : p.lam ≤ (p.V : ℝ) := by
    simpa [p, m, p10_1kHeightParams] using hvolume
  have hVreal : 0 < (p.V : ℝ) := lt_of_lt_of_le hlam hvolume'
  have hV : 0 < p.V := by exact_mod_cast hVreal
  have hprob : p.lam / (p.V : ℝ) ≤ 1 := (div_le_one hVreal).2 hvolume'
  intro Sites
  exact HypercubeRamsey.height_position_counts p Sites hlam hV hrad' hprob

/-- Number of prospective centers at a fixed height within distance `r` of a
projected site. -/
def p10_1kHeightPositionCount (p : HDParams) (P : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) : ℕ :=
  (Finset.univ.filter fun u : CubeVertex p.d =>
    P (u, j) = true ∧ hammingDist u v ≤ p.r).card

/-- A height-position sample fails if some queried site and level has too few
or too many prospective centers in its radius-`r` ball. -/
def p10_1kHeightBadPositions (p : HDParams) (Sites : p.Sites)
    (P : p.Loc → Bool) : Prop :=
  ∃ v ∈ Sites, ∃ j : Fin (p.H + 1),
    (p10_1kHeightPositionCount p P v j : ℝ) < p.lam / 2 ∨
      2 * p.lam < (p10_1kHeightPositionCount p P v j : ℝ)

/-- Outside the bad-position event, every queried site and level has a useful
number of eligible prospective centers. -/
theorem p10_1kHeightPositionCount_bounds_of_not_bad (p : HDParams)
    (Sites : p.Sites) (P : p.Loc → Bool)
    (hbad : ¬ p10_1kHeightBadPositions p Sites P)
    (v : CubeVertex p.d) (hv : v ∈ Sites) (j : Fin (p.H + 1)) :
    p.lam / 2 ≤ (p10_1kHeightPositionCount p P v j : ℝ) ∧
      (p10_1kHeightPositionCount p P v j : ℝ) ≤ 2 * p.lam := by
  have hlow : ¬ (p10_1kHeightPositionCount p P v j : ℝ) < p.lam / 2 := by
    intro h
    exact hbad ⟨v, hv, j, Or.inl h⟩
  have hhigh : ¬ 2 * p.lam < (p10_1kHeightPositionCount p P v j : ℝ) := by
    intro h
    exact hbad ⟨v, hv, j, Or.inr h⟩
  exact ⟨le_of_not_gt hlow, le_of_not_gt hhigh⟩

/-- Eligible height IDs at a site and level, indexed by the position sample. -/
noncomputable def p10_1kHeightEligibleIds (p : HDParams) (P : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) : Finset p.Loc := by
  classical
  exact (Finset.univ.filter fun u : CubeVertex p.d =>
    P (u, j) = true ∧ hammingDist u v ≤ p.r).image (fun u => (u, j))

/-- The eligible-ID set has exactly the position count at its site and level. -/
theorem p10_1kHeightEligibleIds_card (p : HDParams) (P : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
    (p10_1kHeightEligibleIds p P v j).card = p10_1kHeightPositionCount p P v j := by
  unfold p10_1kHeightEligibleIds p10_1kHeightPositionCount
  exact Finset.card_image_of_injective _ (fun u u' h => congrArg Prod.fst h)

/-- The height selector's prospective-ID map; the auxiliary tag can later carry
the local patch, tuple-list, and mask data. -/
noncomputable def p10_1kHeightEligibility {Aux : Type*} (p : HDParams) :
    (p.Loc → Bool) → Aux → p.EligMap := fun P _ v j =>
  p10_1kHeightEligibleIds p P v j

/-- A good position sample makes the canonical prospective-ID map legal on the
queried site set. -/
theorem p10_1kHeightEligibility_legal_of_not_bad (p : HDParams)
    (Sites : p.Sites) (P : p.Loc → Bool) (hlam : 0 ≤ p.lam)
    (hbad : ¬ p10_1kHeightBadPositions p Sites P) {Aux : Type*} (aux : Aux) :
    p.Legal P (p10_1kHeightEligibility p P aux) Sites := by
  classical
  intro v hv j
  constructor
  · intro ℓ hℓ
    obtain ⟨u, hu, hpair⟩ := Finset.mem_image.mp hℓ
    have hu' := (Finset.mem_filter.mp hu).2
    have hfirst : u = ℓ.1 := congrArg Prod.fst hpair
    have hsecond : j = ℓ.2 := congrArg Prod.snd hpair
    constructor
    · simpa [hfirst, hsecond] using hu'.1
    · constructor
      · exact hsecond.symm
      · simpa [hfirst] using hu'.2
  · change p.lam / 3 ≤
      (p10_1kHeightEligibleIds p P v j).card
    rw [p10_1kHeightEligibleIds_card]
    have hcount := p10_1kHeightPositionCount_bounds_of_not_bad p Sites P hbad v hv j
    have hthird : p.lam / 3 ≤ p.lam / 2 := by nlinarith [hlam]
    exact le_trans hthird hcount.1

/-- Event probabilities are monotone under pointwise inclusion. -/
theorem p10_1k_FinProb_pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · simp [hA, hB, P.nonneg ω]
    · simp [hA, hB]

/-- Finite probability's union bound for two events. -/
theorem p10_1k_FinProb_pr_or_le {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) : P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · by_cases hB : B ω
    · simp [hA, hB]
      linarith [P.nonneg ω]
    · simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB]

/-- Finite union bound for a family of events indexed by a finite type. -/
theorem p10_1k_FinProb_pr_exists_le {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinProb Ω) (Bad : I → Ω → Prop) :
    P.pr (fun ω => ∃ i, Bad i ω) ≤ ∑ i, P.pr (Bad i) := by
  classical
  letI : DecidablePred (fun ω : Ω => ∃ i : I, Bad i ω) :=
    fun ω => Classical.propDecidable _
  unfold FinProb.pr
  calc
    (∑ ω, if ∃ i, Bad i ω then P.w ω else 0) ≤
        ∑ ω, ∑ i, if Bad i ω then P.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hbad : ∃ i, Bad i ω
      · rw [if_pos hbad]
        obtain ⟨i, hi⟩ := hbad
        calc
          P.w ω = (if Bad i ω then P.w ω else 0) := by simp [hi]
          _ ≤ ∑ j, if Bad j ω then P.w ω else 0 := by
            have hsum := Finset.single_le_sum
              (f := fun j : I => if Bad j ω then P.w ω else 0)
              (fun j hj => by
                by_cases h : Bad j ω
                · simpa [h] using P.nonneg ω
                · simp [h])
              (Finset.mem_univ i)
            simpa [hi] using hsum
      · rw [if_neg hbad]
        apply Finset.sum_nonneg
        intro i hi
        by_cases h : Bad i ω
        · simpa [h] using P.nonneg ω
        · simp [h]
    _ = ∑ i, ∑ ω, if Bad i ω then P.w ω else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i, P.pr (Bad i) := rfl

/-- Cluster indices that pass one mass gate and every indexed ratio gate. -/
noncomputable def p10_1kTiltGoodClusterSet {q r : ℕ}
    (massBad : Fin q → Prop) (ratioBad : Fin r → Fin q → Prop) :
    Finset (Fin q) := by
  classical
  exact Finset.univ.filter fun j =>
    ¬ massBad j ∧ ∀ b, ¬ ratioBad b j

/-- A cluster fails at least one of its mass and ratio gates. -/
def p10_1kTiltBadEvent {q r : ℕ}
    (massBad : Fin q → Prop) (ratioBad : Fin r → Fin q → Prop)
    (j : Fin q) : Prop := massBad j ∨ ∃ b, ratioBad b j

/-- If the total failure probability for the mass gate and all ratio gates is
at most one half, the squared-tilt law retains at least half its cluster mass. -/
theorem p10_1kTiltGoodClusterSet_mass_ge_half {q r : ℕ}
    (P : FinProb (Fin q)) (massBad : Fin q → Prop)
    (ratioBad : Fin r → Fin q → Prop) (εmass εratio : ℝ)
    (hmass : P.pr massBad ≤ εmass)
    (hratio : ∀ b, P.pr (ratioBad b) ≤ εratio)
    (hbudget : εmass + (r : ℝ) * εratio ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ P.pr
      (fun j => j ∈ p10_1kTiltGoodClusterSet massBad ratioBad) := by
  classical
  have hbad : P.pr (p10_1kTiltBadEvent massBad ratioBad) ≤ 1 / 2 := by
    calc
      P.pr (p10_1kTiltBadEvent massBad ratioBad) ≤
          P.pr massBad + P.pr (fun j => ∃ b, ratioBad b j) := by
        exact p10_1k_FinProb_pr_or_le P massBad (fun j => ∃ b, ratioBad b j)
      _ ≤ εmass + ∑ b : Fin r, P.pr (ratioBad b) := by
        apply add_le_add hmass
        exact p10_1k_FinProb_pr_exists_le P ratioBad
      _ ≤ εmass + (r : ℝ) * εratio := by
        have hsum : (∑ b : Fin r, P.pr (ratioBad b)) ≤
            (r : ℝ) * εratio := by
          calc
            (∑ b : Fin r, P.pr (ratioBad b)) ≤ ∑ b : Fin r, εratio :=
              Finset.sum_le_sum fun b hb => hratio b
            _ = (r : ℝ) * εratio := by simp
        linarith
      _ ≤ 1 / 2 := hbudget
  have hcomp : P.pr (p10_1kTiltBadEvent massBad ratioBad) +
      P.pr (fun j => ¬ p10_1kTiltBadEvent massBad ratioBad j) = 1 := by
    classical
    letI : DecidablePred (p10_1kTiltBadEvent massBad ratioBad) :=
      fun j => Classical.propDecidable _
    letI : DecidablePred (fun j => ¬ p10_1kTiltBadEvent massBad ratioBad j) :=
      fun j => Classical.propDecidable _
    unfold FinProb.pr
    rw [← Finset.sum_add_distrib]
    calc
      (∑ j, ((if p10_1kTiltBadEvent massBad ratioBad j then P.w j else 0) +
          (if ¬ p10_1kTiltBadEvent massBad ratioBad j then P.w j else 0))) =
          ∑ j, P.w j := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : p10_1kTiltBadEvent massBad ratioBad j <;> simp [h]
      _ = 1 := P.sum_eq_one
  have hnotbad : (1 / 2 : ℝ) ≤
      P.pr (fun j => ¬ p10_1kTiltBadEvent massBad ratioBad j) := by
    linarith
  have hset : ∀ j,
      j ∈ p10_1kTiltGoodClusterSet massBad ratioBad ↔
        ¬ p10_1kTiltBadEvent massBad ratioBad j := by
    intro j
    simp [p10_1kTiltGoodClusterSet, p10_1kTiltBadEvent]
  have heq :
      P.pr (fun j => j ∈ p10_1kTiltGoodClusterSet massBad ratioBad) =
        P.pr (fun j => ¬ p10_1kTiltBadEvent massBad ratioBad j) := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j ∈ p10_1kTiltGoodClusterSet massBad ratioBad
    · have hn := (hset j).1 h
      simp [h, hn]
    · have hnotgood : ¬ ¬ p10_1kTiltBadEvent massBad ratioBad j := by
        intro hgood
        exact h ((hset j).2 hgood)
      simp [h, hnotgood]
  rw [heq]
  exact hnotbad

/-- A product-law event depending only on its first coordinate has the first
coordinate's probability. -/
theorem p10_1k_pr_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α → Prop) :
    (P.prod Q).pr (fun z => A z.1) = P.pr A := by
  classical
  unfold FinProb.pr FinProb.prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hA : A a
  · simp only [if_pos hA]
    rw [← Finset.mul_sum]
    simp [Q.sum_eq_one]
  · simp [hA]

/-- Since the eligibility map depends only on the position sample, its failure
probability under the height experiment is bounded by the position bad-event
probability. -/
theorem p10_1kHeightEligibility_not_legal_probability_bound (p : HDParams)
    (Sites : p.Sites) {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
    (hlam : 0 ≤ p.lam) (ε : ℝ)
    (hpos : p.posLaw.pr (p10_1kHeightBadPositions p Sites) ≤ ε) :
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
      ¬ p.Legal ω.1.1 (p10_1kHeightEligibility p ω.1.1 ω.1.2) Sites) ≤ ε := by
  have hsubset (ω : ((p.Loc → Bool) × Aux) × (p.Loc → Bool))
      (hnot : ¬ p.Legal ω.1.1 (p10_1kHeightEligibility p ω.1.1 ω.1.2) Sites) :
      p10_1kHeightBadPositions p Sites ω.1.1 := by
    by_contra hbad
    exact hnot (p10_1kHeightEligibility_legal_of_not_bad p Sites ω.1.1 hlam hbad ω.1.2)
  calc
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        ¬ p.Legal ω.1.1 (p10_1kHeightEligibility p ω.1.1 ω.1.2) Sites) ≤
    ((p.posLaw.prod πAux).prod p.actLaw).pr
        (fun ω => p10_1kHeightBadPositions p Sites ω.1.1) :=
      p10_1k_FinProb_pr_mono _ _ _ hsubset
    _ = p.posLaw.pr (p10_1kHeightBadPositions p Sites) := by
      calc
        ((p.posLaw.prod πAux).prod p.actLaw).pr
            (fun ω => p10_1kHeightBadPositions p Sites ω.1.1) =
            (p.posLaw.prod πAux).pr
              (fun z => p10_1kHeightBadPositions p Sites z.1) := by
          simpa using p10_1k_pr_prod_fst (p.posLaw.prod πAux) p.actLaw
            (fun z => p10_1kHeightBadPositions p Sites z.1)
        _ = p.posLaw.pr (p10_1kHeightBadPositions p Sites) := by
          simpa using p10_1k_pr_prod_fst p.posLaw πAux
            (p10_1kHeightBadPositions p Sites)
    _ ≤ ε := hpos

/-- Combine the probability of illegality with the good-height estimate, so
that every failed height sample is charged to one of the two events. -/
theorem p10_1kHeight_not_good_probability_bound {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (legal good : Ω → Prop) (εlegal εheight : ℝ)
    (hlegal : P.pr (fun ω => ¬ legal ω) ≤ εlegal)
    (hheight : P.pr (fun ω => legal ω ∧ ¬ good ω) ≤ εheight) :
    P.pr (fun ω => ¬ good ω) ≤ εlegal + εheight := by
  have hsubset (ω : Ω) (hbad : ¬ good ω) :
      ¬ legal ω ∨ (legal ω ∧ ¬ good ω) := by
    by_cases hlegalω : legal ω
    · exact Or.inr ⟨hlegalω, hbad⟩
    · exact Or.inl hlegalω
  calc
    P.pr (fun ω => ¬ good ω) ≤
        P.pr (fun ω => ¬ legal ω ∨ (legal ω ∧ ¬ good ω)) :=
      p10_1k_FinProb_pr_mono P _ _ hsubset
    _ ≤ P.pr (fun ω => ¬ legal ω) + P.pr (fun ω => legal ω ∧ ¬ good ω) :=
      p10_1k_FinProb_pr_or_le P _ _
    _ ≤ εlegal + εheight := add_le_add hlegal hheight

/-- The legal eligibility map plus the global height estimate controls the
unconditional failure probability on any site set, up to the position-count
exception. -/
theorem p10_1kHeightExperiment_not_good_probability_bound (p : HDParams)
    (Sites : p.Sites) {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
    (hlam : 0 ≤ p.lam) (εpos εheight : ℝ)
    (hpos : p.posLaw.pr (p10_1kHeightBadPositions p Sites) ≤ εpos)
    (hheight : ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
      p.Legal ω.1.1 (p10_1kHeightEligibility p ω.1.1 ω.1.2) Sites ∧
        ¬ p.GoodHeights Sites ω.1.1 ω.2
          (p10_1kHeightEligibility p ω.1.1 ω.1.2)) ≤ εheight) :
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
      ¬ p.GoodHeights Sites ω.1.1 ω.2
        (p10_1kHeightEligibility p ω.1.1 ω.1.2)) ≤ εpos + εheight := by
  let P := (p.posLaw.prod πAux).prod p.actLaw
  have hnotlegal := p10_1kHeightEligibility_not_legal_probability_bound
    p Sites πAux hlam εpos hpos
  exact p10_1kHeight_not_good_probability_bound P
    (fun ω => p.Legal ω.1.1 (p10_1kHeightEligibility p ω.1.1 ω.1.2) Sites)
    (fun ω => p.GoodHeights Sites ω.1.1 ω.2
      (p10_1kHeightEligibility p ω.1.1 ω.1.2))
    εpos εheight hnotlegal (by simpa [P] using hheight)

/-- The global good-height estimate of Lemma 3.8, instantiated on the
projected residual dimension used by Section 10. -/
theorem p10_1kHeightParams_global_heights (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : δ < (1 : ℝ) / 2000) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let p := p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ
      ∀ (Sites : p.Sites) {Aux : Type*} [Fintype Aux]
        (πAux : FinProb Aux) (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
            ¬ p.GoodHeights Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)) ≤
          Real.exp (-(p.n : ℝ) ^ (1 + c)) := by
  have hp := p10_1k_heightAdmissible δ hδ hδsmall
  let reg := p10_1k_heightRegime δ hδ hδsmall
  obtain ⟨c, hc, nGlobal, hglobal⟩ :=
    HypercubeRamsey.height_selection_global 10 (50 * δ) (140 * δ) δ (8 * δ)
      (1 - δ) (20 * δ) (1 / 2) 1 6 hp reg
  have hdimEvent := p10_1kHeightParams_dimension_eventually
    (η₀ := 1) (ζ := 1) δ (by norm_num) (by norm_num) hδ
      (by simpa using hδsmall)
  obtain ⟨nDim, hdim⟩ := Filter.eventually_atTop.mp hdimEvent
  refine ⟨c, ?_⟩
  constructor
  · exact hc
  · refine ⟨max nGlobal nDim, ?_⟩
    intro n hn
    let m : ℕ := ⌊(n : ℝ) ^ (200 * δ)⌋₊
    let p : HDParams := p10_1kHeightParams n m δ
    have hdimN := hdim n (le_trans (le_max_right _ _) hn)
    have hnGlobal : nGlobal ≤ n := le_trans (le_max_left _ _) hn
    have hreg := p10_1kHeightParams_subRegime_ok n m δ hδ hδsmall
    have hreg' : reg.ok p.n p.d p.r := by
      simpa [p, reg, p10_1kHeightParams, p10_1k_heightRegime] using hreg
    have hlam : p.lam = (p.n : ℝ) ^ (10 : ℝ) := by
      dsimp [p, p10_1kHeightParams]
      exact (Real.rpow_natCast _ 10).symm
    have hupper : (p.d : ℝ) ≤ 1 * (p.n : ℝ) := by
      simpa [p, p10_1kHeightParams] using hdimN.2
    exact hglobal p rfl rfl hlam rfl rfl hnGlobal hdimN.1 hupper hreg'

/-- The second side of a PCluster witness is nonempty because it supports a
probability law. -/
theorem p10_1kClusterData_secondSupport_nonempty {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ}
    {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B) : B.Nonempty := by
  classical
  by_contra hB
  have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
  have hK : 0 < data.K := by
    by_contra hK
    have hK0 : data.K = 0 := Nat.eq_zero_of_not_pos hK
    have hsum := data.lam_sum
    simp [hK0] at hsum
  let j : Fin data.K := ⟨0, hK⟩
  have hzero : ∀ y, (data.D j).w y = 0 := by
    intro y
    have hy : y ∉ B := by simp [hBempty]
    exact (data.D_supported j) y hy
  have hsum := (data.D j).sum_eq_one
  have hz : (∑ y, (data.D j).w y) = 0 := by simp [hzero]
  rw [hz] at hsum
  norm_num at hsum

/-- Turn the cluster weights of a selected patch into a finite probability law. -/
def p10_1kClusterPrior {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {ζ δ : ℝ} {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B) :
    FinProb (Fin data.K) where
  w := data.lam
  nonneg := data.lam_nonneg
  sum_eq_one := data.lam_sum

/-- The aggregate second-side law of a selected cluster patch. -/
noncomputable def p10_1kClusterAggregate {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ}
    {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B) : Law N :=
  Law.mix (p10_1kClusterPrior data) data.D

/-- The aggregate law retains the PCluster width bound. -/
theorem p10_1kClusterAggregate_width {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ}
    {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B) (y : Fin N) :
    (p10_1kClusterAggregate data).w y ≤ Real.exp ((n : ℝ) ^ δ) / N := by
  simpa [p10_1kClusterAggregate, p10_1kClusterPrior, Law.mix] using
    data.aggregate_width y

/-- The cluster prior tilted by the squared mass of a finite hit set. -/
noncomputable def p10_1kSquaredTiltPrior {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) : FinProb (Fin q) where
  w j := ρ.w j * (lawMassOn (D j) F) ^ 2 / squaredClusterMass ρ D F
  nonneg j := div_nonneg
    (mul_nonneg (ρ.nonneg j) (sq_nonneg _)) (le_of_lt hA)
  sum_eq_one := by
    rw [← Finset.sum_div]
    unfold squaredClusterMass
    exact div_self (ne_of_gt hA)

/-- The probability of a deletion-ratio failure under the squared-mass
cluster tilt is the corresponding bad squared weight divided by total squared
mass. This is the finite-law form of the P10.1e tail estimate. -/
theorem p10_1kSquaredTiltPrior_badRatio_pr_le {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N)
    (F Fminus : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (t : ℝ)
    (hρ : ∀ j, 0 ≤ ρ.w j)
    (hmass : ∀ j,
      0 ≤ lawMassOn (D j) F ∧
      0 ≤ lawMassOn (D j) Fminus ∧
      lawMassOn (D j) F ≤ lawMassOn (D j) Fminus)
    (ht : 0 ≤ t) :
    FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => lawMassOn (D j) F / lawMassOn (D j) Fminus < t) ≤
        t ^ 2 * squaredClusterMass ρ D Fminus / squaredClusterMass ρ D F := by
  classical
  let mass : Fin q → ℝ := fun j => lawMassOn (D j) F
  let massMinus : Fin q → ℝ := fun j => lawMassOn (D j) Fminus
  have hprob :
      FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
        (fun j => lawMassOn (D j) F / lawMassOn (D j) Fminus < t) =
        squaredTiltBadWeight ρ mass massMinus t /
          squaredClusterMass ρ D F := by
    change (∑ j, if mass j / massMinus j < t then
        ρ.w j * (mass j) ^ 2 / squaredClusterMass ρ D F else 0) =
        squaredTiltBadWeight ρ mass massMinus t /
          squaredClusterMass ρ D F
    dsimp [squaredTiltBadWeight]
    calc
      (∑ j, if mass j / massMinus j < t then
          ρ.w j * (mass j) ^ 2 / squaredClusterMass ρ D F else 0) =
          ∑ j, (if mass j / massMinus j < t then
            ρ.w j * (mass j) ^ 2 else 0) / squaredClusterMass ρ D F := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hbad : mass j / massMinus j < t <;> simp [hbad]
      _ = (∑ j, if mass j / massMinus j < t then
            ρ.w j * (mass j) ^ 2 else 0) / squaredClusterMass ρ D F :=
        by rw [Finset.sum_div]
  calc
    FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
        (fun j => lawMassOn (D j) F / lawMassOn (D j) Fminus < t) =
        squaredTiltBadWeight ρ mass massMinus t /
          squaredClusterMass ρ D F := hprob
    _ ≤ t ^ 2 * squaredClusterMass ρ D Fminus /
          squaredClusterMass ρ D F := by
      simpa [mass, massMinus, squaredClusterMass] using
        (p10_1e_squared_tilt_tail_bound ρ mass massMinus t hρ hmass ht)

/-- A lower bound on the aggregate deletion ratio turns the P10.1e squared
tilt tail into an exponential error bound. -/
theorem p10_1kSquaredTiltPrior_badRatio_pr_exp_le {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N)
    (F Fminus : Finset (Fin N)) (hFsub : F ⊆ Fminus)
    (hA : 0 < squaredClusterMass ρ D F)
    (hAminus : 0 < squaredClusterMass ρ D Fminus)
    (t s c : ℝ) (ht : 0 ≤ t)
    (hRatio : Real.exp s ≤ squaredClusterMass ρ D F /
      squaredClusterMass ρ D Fminus)
    (hTail : t ^ 2 * Real.exp (-s) ≤ Real.exp (-c)) :
    FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => lawMassOn (D j) F / lawMassOn (D j) Fminus < t) ≤
        Real.exp (-c) := by
  classical
  have hmass : ∀ j,
      0 ≤ lawMassOn (D j) F ∧
      0 ≤ lawMassOn (D j) Fminus ∧
      lawMassOn (D j) F ≤ lawMassOn (D j) Fminus := by
    intro j
    have hFnonneg : 0 ≤ lawMassOn (D j) F := by
      unfold lawMassOn
      apply Finset.sum_nonneg
      intro y hy
      exact (D j).nonneg y
    have hFminusNonneg : 0 ≤ lawMassOn (D j) Fminus := by
      unfold lawMassOn
      apply Finset.sum_nonneg
      intro y hy
      exact (D j).nonneg y
    have hFle : lawMassOn (D j) F ≤ lawMassOn (D j) Fminus := by
      unfold lawMassOn
      apply Finset.sum_le_sum_of_subset_of_nonneg hFsub
      intro y hy hnot
      exact (D j).nonneg y
    exact ⟨hFnonneg, hFminusNonneg, hFle⟩
  have hratioCross : Real.exp s * squaredClusterMass ρ D Fminus ≤
      squaredClusterMass ρ D F :=
    (le_div_iff₀ hAminus).mp hRatio
  have hExpInv : Real.exp (-s) * Real.exp s = 1 := by
    rw [← Real.exp_add]
    simp
  have hnum : t ^ 2 * squaredClusterMass ρ D Fminus ≤
      Real.exp (-c) * squaredClusterMass ρ D F := by
    calc
      t ^ 2 * squaredClusterMass ρ D Fminus =
          (t ^ 2 * Real.exp (-s)) *
            (Real.exp s * squaredClusterMass ρ D Fminus) := by
        calc
          t ^ 2 * squaredClusterMass ρ D Fminus =
              t ^ 2 * (1 * squaredClusterMass ρ D Fminus) := by ring
          _ = t ^ 2 * ((Real.exp (-s) * Real.exp s) *
              squaredClusterMass ρ D Fminus) := by rw [hExpInv]
          _ = (t ^ 2 * Real.exp (-s)) *
              (Real.exp s * squaredClusterMass ρ D Fminus) := by ring
      _ ≤ Real.exp (-c) *
          (Real.exp s * squaredClusterMass ρ D Fminus) :=
        mul_le_mul_of_nonneg_right hTail (by positivity)
      _ ≤ Real.exp (-c) * squaredClusterMass ρ D F :=
        mul_le_mul_of_nonneg_left hratioCross (Real.exp_nonneg _)
  calc
    FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => lawMassOn (D j) F / lawMassOn (D j) Fminus < t) ≤
        t ^ 2 * squaredClusterMass ρ D Fminus /
          squaredClusterMass ρ D F :=
      p10_1kSquaredTiltPrior_badRatio_pr_le ρ D F Fminus hA t
        (fun j => ρ.nonneg j) hmass ht
    _ ≤ Real.exp (-c) := (div_le_iff₀ hA).2 hnum

/-- Scalar exponent comparison for an own-block deletion gate. -/
theorem p10_1k_ownDeletionTail_scalar (k : ℕ) (gain : ℝ) :
    (Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ))) ^ 2 *
        Real.exp (-((-Real.log 4 + (2 / 5 : ℝ) * gain) * (k : ℝ))) ≤
      Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hpow (x : ℝ) : (Real.exp x) ^ 2 = Real.exp (2 * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  let x : ℝ := (-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ)
  let y : ℝ := (-Real.log 4 + (2 / 5 : ℝ) * gain) * (k : ℝ)
  change Real.exp x ^ 2 * Real.exp (-y) ≤
    Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ)))
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [x, y]
  rw [hlog4]
  ring_nf
  exact le_rfl

/-- Scalar exponent comparison for an external-block deletion gate. -/
theorem p10_1k_externalDeletionTail_scalar (k : ℕ) :
    (Real.exp (-(6 / 5 : ℝ) * (k : ℝ))) ^ 2 *
        Real.exp (-(-2 * (k : ℝ))) ≤ Real.exp (-((2 / 5 : ℝ) * (k : ℝ))) := by
  have hpow (x : ℝ) : (Real.exp x) ^ 2 = Real.exp (2 * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  ring_nf
  exact le_rfl

/-- The squared-tilt probability of an own-block deletion-ratio failure is at
most `exp (-.24 gain k)` when the aggregate test passes. -/
theorem p10_1kSquaredTiltPrior_ownDeletion_tail {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N)
    (F Fminus : Finset (Fin N)) (hFsub : F ⊆ Fminus)
    (hA : 0 < squaredClusterMass ρ D F)
    (hAminus : 0 < squaredClusterMass ρ D Fminus)
    (gain : ℝ) (k : ℕ)
    (hRatio : Real.exp ((-Real.log 4 + (2 / 5 : ℝ) * gain) * (k : ℝ)) ≤
      squaredClusterMass ρ D F / squaredClusterMass ρ D Fminus) :
    FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => lawMassOn (D j) F / lawMassOn (D j) Fminus <
        Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ))) ≤
      Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) := by
  exact p10_1kSquaredTiltPrior_badRatio_pr_exp_le ρ D F Fminus hFsub hA
    hAminus (Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ)))
    ((-Real.log 4 + (2 / 5 : ℝ) * gain) * (k : ℝ))
    ((6 / 25 : ℝ) * gain * (k : ℝ))
    (Real.exp_nonneg _) hRatio (p10_1k_ownDeletionTail_scalar k gain)

/-- The squared-tilt probability of an external-block deletion-ratio failure
is at most `exp (-.4 k)` when the external aggregate test passes. -/
theorem p10_1kSquaredTiltPrior_externalDeletion_tail {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N)
    (F Fminus : Finset (Fin N)) (hFsub : F ⊆ Fminus)
    (hA : 0 < squaredClusterMass ρ D F)
    (hAminus : 0 < squaredClusterMass ρ D Fminus) (k : ℕ)
    (hRatio : Real.exp (-2 * (k : ℝ)) ≤
      squaredClusterMass ρ D F / squaredClusterMass ρ D Fminus) :
    FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => lawMassOn (D j) F / lawMassOn (D j) Fminus <
        Real.exp (-(6 / 5 : ℝ) * (k : ℝ))) ≤
      Real.exp (-((2 / 5 : ℝ) * (k : ℝ))) := by
  exact p10_1kSquaredTiltPrior_badRatio_pr_exp_le ρ D F Fminus hFsub hA
    hAminus (Real.exp (-(6 / 5 : ℝ) * (k : ℝ)))
    (-2 * (k : ℝ)) ((2 / 5 : ℝ) * (k : ℝ))
    (Real.exp_nonneg _) hRatio (p10_1k_externalDeletionTail_scalar k)

/-- Scalar exponent comparison for the absolute hit-mass gate. -/
theorem p10_1k_absoluteMassTail_scalar (L : ℝ) :
    (Real.exp (-(3 / 2 : ℝ) * L)) ^ 2 * Real.exp (2 * L) ≤ Real.exp (-L) := by
  have hpow (x : ℝ) : (Real.exp x) ^ 2 = Real.exp (2 * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  ring_nf
  exact le_rfl

/-- The squared tilt assigns at most `exp (-k r)` mass to components whose
hit-set mass falls below `exp (-3 k r / 2)`, provided the successful-list
absolute mass bound holds. -/
theorem p10_1kSquaredTiltPrior_absoluteMass_tail {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (k r : ℕ)
    (hA_lower : Real.exp (-2 * (k : ℝ) * (r : ℝ)) ≤
      squaredClusterMass ρ D F) :
    FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => lawMassOn (D j) F <
        Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ)))) ≤
      Real.exp (-((k : ℝ) * (r : ℝ))) := by
  classical
  have hMassAll (j : Fin q) : lawMassOn (D j) (Finset.univ : Finset (Fin N)) = 1 := by
    simpa [lawMassOn] using (D j).sum_eq_one
  have hAuniv : squaredClusterMass ρ D (Finset.univ : Finset (Fin N)) = 1 := by
    unfold squaredClusterMass
    calc
      (∑ j, ρ.w j *
          (lawMassOn (D j) (Finset.univ : Finset (Fin N))) ^ 2) =
          ∑ j, ρ.w j * 1 ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hMassAll]
      _ = 1 := by simp [ρ.sum_eq_one]
  have hRatio : Real.exp (-2 * (k : ℝ) * (r : ℝ)) ≤
      squaredClusterMass ρ D F /
        squaredClusterMass ρ D (Finset.univ : Finset (Fin N)) := by
    simpa [hAuniv] using hA_lower
  have hTail :
      (Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ)))) ^ 2 *
        Real.exp (-(-2 * (k : ℝ) * (r : ℝ))) ≤
          Real.exp (-((k : ℝ) * (r : ℝ))) := by
    simpa [mul_assoc] using
      p10_1k_absoluteMassTail_scalar ((k : ℝ) * (r : ℝ))
  have hprob := p10_1kSquaredTiltPrior_badRatio_pr_exp_le ρ D F Finset.univ
    (Finset.subset_univ F) hA (by rw [hAuniv]; norm_num)
    (Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ))))
    (-2 * (k : ℝ) * (r : ℝ)) ((k : ℝ) * (r : ℝ))
    (Real.exp_nonneg _) hRatio hTail
  have hevent :
      (fun j => lawMassOn (D j) F /
          lawMassOn (D j) (Finset.univ : Finset (Fin N)) <
            Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ)))) =
        (fun j => lawMassOn (D j) F <
          Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ)))) := by
    funext j
    rw [hMassAll j, div_one]
  rw [hevent] at hprob
  exact hprob

/-- Sample a cluster with the squared-mass tilt, then a second-side label
conditioned to hit the whole list. Zero-mass clusters use an irrelevant default. -/
noncomputable def p10_1kSquaredTiltLabelLaw {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N) :
    FinProb (Fin q × Fin N) :=
  FinProb.bind (p10_1kSquaredTiltPrior ρ D F hA) (fun j =>
    if hmass : 0 < lawMassOn (D j) F then
      Law.restrict (D j) F hmass
    else Law.dirac ⟨0, hN⟩)

/-- The tilted label law is supported on the full hit set. -/
theorem p10_1kSquaredTiltLabelLaw_support {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N) :
    ∀ j y, (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, y) ≠ 0 → y ∈ F := by
  classical
  intro j y hprob
  by_cases hmass : 0 < lawMassOn (D j) F
  · have hlabel : (Law.restrict (D j) F hmass).w y ≠ 0 := by
      intro hzero
      apply hprob
      simp [p10_1kSquaredTiltLabelLaw, FinProb.bind, hmass, hzero]
    by_contra hy
    simp [Law.restrict, hy] at hlabel
  · have hmassNonneg : 0 ≤ lawMassOn (D j) F := by
      unfold lawMassOn
      exact Finset.sum_nonneg fun x hx => (D j).nonneg x
    have hmassZero : lawMassOn (D j) F = 0 :=
      le_antisymm (le_of_not_gt hmass) hmassNonneg
    have hpriorZero : (p10_1kSquaredTiltPrior ρ D F hA).w j = 0 := by
      simp [p10_1kSquaredTiltPrior, hmassZero]
    have hzero : (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, y) = 0 := by
      simp [p10_1kSquaredTiltLabelLaw, FinProb.bind, hmass, hpriorZero]
    exact (hprob hzero).elim

/-- Each atom of the squared-tilt label law is bounded by its prior weight
times the component atom cap, divided by the total squared mass. -/
theorem p10_1kSquaredTiltLabelLaw_atom_le {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N) (cap : ℝ)
    (hcap : 0 ≤ cap) (hAtom : ∀ j y, (D j).w y ≤ cap) :
    ∀ j y, (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, y) ≤
      ρ.w j * cap / squaredClusterMass ρ D F := by
  classical
  intro j y
  by_cases hmass : 0 < lawMassOn (D j) F
  · let mass : ℝ := lawMassOn (D j) F
    have hmassRaw : 0 < mass := by simpa [mass] using hmass
    have hmassle : mass ≤ 1 := by
      dsimp [mass, lawMassOn]
      calc
        (∑ z ∈ F, (D j).w z) ≤ ∑ y, (D j).w y := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
          intro z hz hnot
          exact (D j).nonneg z
        _ = 1 := (D j).sum_eq_one
    have hprior :
        (p10_1kSquaredTiltPrior ρ D F hA).w j =
          ρ.w j * mass ^ 2 / squaredClusterMass ρ D F := by
      simp [p10_1kSquaredTiltPrior, mass]
    by_cases hy : y ∈ F
    · have hkernel :
          (if h : 0 < lawMassOn (D j) F then Law.restrict (D j) F h
            else Law.dirac ⟨0, hN⟩).w y = (D j).w y / mass := by
        rw [dif_pos hmass]
        simp [Law.restrict, hy, mass, lawMassOn]
      have hlabel :
          (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, y) =
            (p10_1kSquaredTiltPrior ρ D F hA).w j * ((D j).w y / mass) := by
        simp only [p10_1kSquaredTiltLabelLaw, FinProb.bind]
        rw [hkernel]
      have hEq : (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, y) =
          ρ.w j * mass * (D j).w y / squaredClusterMass ρ D F := by
        rw [hlabel, hprior]
        field_simp [ne_of_gt hmassRaw, hA.ne'] <;> ring
      have hmassAtom : mass * (D j).w y ≤ cap := by
        calc
          mass * (D j).w y ≤ 1 * (D j).w y :=
            mul_le_mul_of_nonneg_right hmassle ((D j).nonneg y)
          _ ≤ 1 * cap := mul_le_mul_of_nonneg_left (hAtom j y) (by norm_num)
          _ = cap := by ring
      rw [hEq]
      apply div_le_div_of_nonneg_right _ hA.le
      calc
        ρ.w j * mass * (D j).w y = ρ.w j * (mass * (D j).w y) := by ring
        _ ≤ ρ.w j * cap := mul_le_mul_of_nonneg_left hmassAtom (ρ.nonneg j)
    · have hzero : (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, y) = 0 := by
        have hkernel :
            (if h : 0 < lawMassOn (D j) F then Law.restrict (D j) F h
              else Law.dirac ⟨0, hN⟩).w y = 0 := by
          rw [dif_pos hmass]
          simp [Law.restrict, hy]
        simp only [p10_1kSquaredTiltLabelLaw, FinProb.bind]
        rw [hkernel]
        simp
      rw [hzero]
      exact div_nonneg (mul_nonneg (ρ.nonneg j) hcap) hA.le
  · have hmassNonneg : 0 ≤ lawMassOn (D j) F := by
      unfold lawMassOn
      apply Finset.sum_nonneg
      intro z hz
      exact (D j).nonneg z
    have hmassZero : lawMassOn (D j) F = 0 :=
      le_antisymm (le_of_not_gt hmass) hmassNonneg
    have hpriorZero : (p10_1kSquaredTiltPrior ρ D F hA).w j = 0 := by
      simp [p10_1kSquaredTiltPrior, hmassZero]
    have hzero :
        (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, y) = 0 := by
      simp only [p10_1kSquaredTiltLabelLaw, FinProb.bind]
      rw [dif_neg hmass]
      simp [hpriorZero]
    rw [hzero]
    exact div_nonneg (mul_nonneg (ρ.nonneg j) hcap) hA.le

/-- The label marginal of the squared-tilt draw is a law supported on the hit
set. -/
noncomputable def p10_1kSquaredTiltLabelMarginal {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N) : Law N :=
  FinProb.map (p10_1kSquaredTiltLabelLaw ρ D F hA hN) Prod.snd

/-- The common-neighbor support condition survives marginalizing the cluster. -/
theorem p10_1kSquaredTiltLabelMarginal_support {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N) :
    ∀ y, (p10_1kSquaredTiltLabelMarginal ρ D F hA hN).w y ≠ 0 → y ∈ F := by
  classical
  intro y hy
  by_contra hyF
  have hzero : (p10_1kSquaredTiltLabelMarginal ρ D F hA hN).w y = 0 := by
    unfold p10_1kSquaredTiltLabelMarginal FinProb.map
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hzy : z.2 = y
    · have hjoint : (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w z = 0 := by
        by_contra hne
        have hne' : (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w z ≠ 0 := by
          simpa [hzy] using hne
        have hmem := p10_1kSquaredTiltLabelLaw_support ρ D F hA hN z.1 z.2 hne'
        exact hyF (hzy ▸ hmem)
      simp [hzy, hjoint]
    · simp [hzy]
  exact hy hzero

/-- Summing the joint atom bound over the tilted cluster index bounds each
atom of the label marginal. -/
theorem p10_1kSquaredTiltLabelMarginal_atom_le {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N) (cap : ℝ)
    (hcap : 0 ≤ cap) (hAtom : ∀ j y, (D j).w y ≤ cap) :
    ∀ y, (p10_1kSquaredTiltLabelMarginal ρ D F hA hN).w y ≤
      cap / squaredClusterMass ρ D F := by
  classical
  intro y
  change (∑ z : Fin q × Fin N,
      if z.2 = y then (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w z else 0) ≤ _
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : Fin q, ∑ z : Fin N,
        if z = y then (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, z) else 0) ≤
        ∑ j : Fin q, ρ.w j * cap / squaredClusterMass ρ D F := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (∑ z : Fin N,
            if z = y then (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, z) else 0) =
            (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, y) := by simp
        _ ≤ ρ.w j * cap / squaredClusterMass ρ D F :=
          p10_1kSquaredTiltLabelLaw_atom_le ρ D F hA hN cap hcap hAtom j y
    _ = cap / squaredClusterMass ρ D F := by
      rw [← Finset.sum_div, ← Finset.sum_mul, ρ.sum_eq_one]
      ring

/-- Conditioning a finite law on an event of mass at least one half doubles
no point mass by more than a factor of two. -/
private theorem p10_1k_FinProb_cond_atom_le_two {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (hA : (1 / 2 : ℝ) ≤ P.pr A)
    (ω : Ω) :
    (FinProb.cond P A (lt_of_lt_of_le (by norm_num) hA)).w ω ≤ 2 * P.w ω := by
  classical
  by_cases hω : A ω
  · simp only [FinProb.cond, hω]
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hA)).2
    have hone : 1 ≤ 2 * P.pr A := by linarith
    calc
      P.w ω = 1 * P.w ω := by ring
      _ ≤ (2 * P.pr A) * P.w ω :=
        mul_le_mul_of_nonneg_right hone (P.nonneg ω)
      _ = (2 * P.w ω) * P.pr A := by ring
  · simp [FinProb.cond, hω, P.nonneg]

/-- The squared-tilt label law after restricting the cluster prior to a retained
set of tilt mass at least one half. -/
noncomputable def p10_1kRetainedSquaredTiltLabelLaw {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N)
    (R : Finset (Fin q))
    (hR : (1 / 2 : ℝ) ≤ FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => j ∈ R)) : FinProb (Fin q × Fin N) :=
  FinProb.bind
    (FinProb.cond (p10_1kSquaredTiltPrior ρ D F hA) (fun j => j ∈ R)
      (lt_of_lt_of_le (by norm_num) hR))
    (fun j => if hmass : 0 < lawMassOn (D j) F then
      Law.restrict (D j) F hmass else Law.dirac ⟨0, hN⟩)

/-- Restricting the squared tilt to retained clusters preserves support of
every sampled label in the fixed-list hit set. -/
theorem p10_1kRetainedSquaredTiltLabelLaw_support {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N)
    (R : Finset (Fin q))
    (hR : (1 / 2 : ℝ) ≤ FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => j ∈ R)) :
    ∀ j y,
      (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR).w (j, y) ≠ 0 →
        y ∈ F := by
  classical
  intro j y hprob
  by_cases hmass : 0 < lawMassOn (D j) F
  · have hlabel : (Law.restrict (D j) F hmass).w y ≠ 0 := by
      intro hzero
      apply hprob
      simp [p10_1kRetainedSquaredTiltLabelLaw, FinProb.bind, hmass, hzero]
    by_contra hy
    simp [Law.restrict, hy] at hlabel
  · have hmassNonneg : 0 ≤ lawMassOn (D j) F := by
      unfold lawMassOn
      apply Finset.sum_nonneg
      intro z hz
      exact (D j).nonneg z
    have hmassZero : lawMassOn (D j) F = 0 :=
      le_antisymm (le_of_not_gt hmass) hmassNonneg
    have hpriorZero : (p10_1kSquaredTiltPrior ρ D F hA).w j = 0 := by
      simp [p10_1kSquaredTiltPrior, hmassZero]
    have hcondZero :
        (FinProb.cond (p10_1kSquaredTiltPrior ρ D F hA) (fun j => j ∈ R)
          (lt_of_lt_of_le (by norm_num) hR)).w j = 0 := by
      by_cases hj : j ∈ R
      · simp [FinProb.cond, hj, hpriorZero]
      · simp [FinProb.cond, hj]
    have hzero :
        (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR).w (j, y) = 0 := by
      simp [p10_1kRetainedSquaredTiltLabelLaw, FinProb.bind, hmass, hcondZero]
    exact (hprob hzero).elim

/-- Restricting to a retained half-mass cluster set costs at most two in each
joint cluster/label atom. -/
theorem p10_1kRetainedSquaredTiltLabelLaw_atom_le {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N)
    (R : Finset (Fin q))
    (hR : (1 / 2 : ℝ) ≤ FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => j ∈ R)) (cap : ℝ) (hcap : 0 ≤ cap)
    (hAtom : ∀ j y, (D j).w y ≤ cap) :
    ∀ j y, (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR).w (j, y) ≤
      2 * ρ.w j * cap / squaredClusterMass ρ D F := by
  classical
  intro j y
  let P := p10_1kSquaredTiltPrior ρ D F hA
  let K : Fin q → Law N := fun j =>
    if hmass : 0 < lawMassOn (D j) F then Law.restrict (D j) F hmass
    else Law.dirac ⟨0, hN⟩
  have hprior :
      (FinProb.cond P (fun j => j ∈ R)
        (lt_of_lt_of_le (by norm_num) hR)).w j ≤ 2 * P.w j := by
    exact p10_1k_FinProb_cond_atom_le_two P (fun j => j ∈ R) hR j
  have hjoint : (p10_1kSquaredTiltLabelLaw ρ D F hA hN).w (j, y) ≤
      ρ.w j * cap / squaredClusterMass ρ D F :=
    p10_1kSquaredTiltLabelLaw_atom_le ρ D F hA hN cap hcap hAtom j y
  change (FinProb.cond P (fun j => j ∈ R)
      (lt_of_lt_of_le (by norm_num) hR)).w j * (K j).w y ≤ _
  calc
    (FinProb.cond P (fun j => j ∈ R)
        (lt_of_lt_of_le (by norm_num) hR)).w j * (K j).w y ≤
        (2 * P.w j) * (K j).w y :=
      mul_le_mul_of_nonneg_right hprior ((K j).nonneg y)
    _ = 2 * (P.w j * (K j).w y) := by ring
    _ ≤ 2 * (ρ.w j * cap / squaredClusterMass ρ D F) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa [P, K, p10_1kSquaredTiltLabelLaw, FinProb.bind] using hjoint
    _ = 2 * ρ.w j * cap / squaredClusterMass ρ D F := by ring

/-- The retained squared-tilt label marginal satisfies the same atom cap up to
the factor two paid for conditioning. -/
noncomputable def p10_1kRetainedSquaredTiltLabelMarginal {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N)
    (R : Finset (Fin q))
    (hR : (1 / 2 : ℝ) ≤ FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => j ∈ R)) : Law N :=
  FinProb.map (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR) Prod.snd

/-- The label marginal of a retained squared tilt stays supported on the
fixed-list hit set. -/
theorem p10_1kRetainedSquaredTiltLabelMarginal_support {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N)
    (R : Finset (Fin q))
    (hR : (1 / 2 : ℝ) ≤ FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => j ∈ R)) :
    ∀ y, (p10_1kRetainedSquaredTiltLabelMarginal ρ D F hA hN R hR).w y ≠ 0 →
      y ∈ F := by
  classical
  intro y hy
  by_contra hyF
  have hzero : (p10_1kRetainedSquaredTiltLabelMarginal ρ D F hA hN R hR).w y = 0 := by
    unfold p10_1kRetainedSquaredTiltLabelMarginal FinProb.map
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hzy : z.2 = y
    · have hjoint :
          (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR).w z = 0 := by
        by_contra hne
        have hne' :
            (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR).w z ≠ 0 := by
          simpa [hzy] using hne
        exact hyF (hzy ▸ p10_1kRetainedSquaredTiltLabelLaw_support
          ρ D F hA hN R hR z.1 z.2 hne')
      simp [hzy, hjoint]
    · simp [hzy]
  exact hy hzero

/-- Atom cap for the retained squared-tilt label marginal. -/
theorem p10_1kRetainedSquaredTiltLabelMarginal_atom_le {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hA : 0 < squaredClusterMass ρ D F) (hN : 0 < N)
    (R : Finset (Fin q))
    (hR : (1 / 2 : ℝ) ≤ FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
      (fun j => j ∈ R)) (cap : ℝ) (hcap : 0 ≤ cap)
    (hAtom : ∀ j y, (D j).w y ≤ cap) :
    ∀ y, (p10_1kRetainedSquaredTiltLabelMarginal ρ D F hA hN R hR).w y ≤
      2 * cap / squaredClusterMass ρ D F := by
  classical
  intro y
  change (∑ z : Fin q × Fin N,
      if z.2 = y then
        (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR).w z else 0) ≤ _
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : Fin q, ∑ z : Fin N,
        if z = y then
          (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR).w (j, z) else 0) ≤
        ∑ j : Fin q, 2 * ρ.w j * cap / squaredClusterMass ρ D F := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (∑ z : Fin N, if z = y then
            (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR).w (j, z) else 0) =
            (p10_1kRetainedSquaredTiltLabelLaw ρ D F hA hN R hR).w (j, y) := by simp
        _ ≤ 2 * ρ.w j * cap / squaredClusterMass ρ D F :=
          p10_1kRetainedSquaredTiltLabelLaw_atom_le
            ρ D F hA hN R hR cap hcap hAtom j y
    _ = 2 * cap / squaredClusterMass ρ D F := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
      have hsum : (∑ j : Fin q, 2 * ρ.w j) = 2 := by
        rw [← Finset.mul_sum, ρ.sum_eq_one]
        ring
      rw [hsum]

/-- Independent tuple arrays drawn from a possibly different first-side law at
each block. -/
noncomputable def p10_1kTupleArrayLaw {N r k : ℕ} (μ : Fin r → Law N) :
    FinProb (Fin r → Fin k → Fin N) :=
  FinProb.pi (fun b : Fin r => FinProb.pi (fun _ : Fin k => μ b))

/-- The tuple-array product law has the weight used by the fixed-list test. -/
theorem p10_1kTupleArrayLaw_weight {N r k : ℕ} (μ : Fin r → Law N)
    (W : Fin r → Fin k → Fin N) :
    (p10_1kTupleArrayLaw μ).w W = tupleArrayWeight μ W := by
  rfl

/-- One prospective ID carries an independent length-`k` tuple from its
slice's first-side law. -/
noncomputable def p10_1kBlockTupleArrayLaw {N k : ℕ} (μ : Law N) :
    FinProb (Fin k → Fin N) :=
  FinProb.pi (fun _ : Fin k => μ)

/-- Weight of a single prospective-ID tuple array. -/
def p10_1kBlockTupleArrayWeight {N k : ℕ} (μ : Law N)
    (W : Fin k → Fin N) : ℝ :=
  ∏ i : Fin k, μ.w (W i)

/-- The single-ID tuple law has its defining product weight. -/
theorem p10_1kBlockTupleArrayLaw_weight {N k : ℕ} (μ : Law N)
    (W : Fin k → Fin N) :
    (p10_1kBlockTupleArrayLaw μ).w W = p10_1kBlockTupleArrayWeight μ W := by
  rfl

/-- Independent tuple arrays pre-generated at every prospective position ID. -/
noncomputable def p10_1kIdTupleArrayLaw {N k : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (μ : I → Law N) :
    FinProb (I → Fin k → Fin N) :=
  FinProb.pi (fun id => p10_1kBlockTupleArrayLaw (μ id))

/-- The prospective-ID tuple-array law has the product weight at each sample. -/
theorem p10_1kIdTupleArrayLaw_weight {N k : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (μ : I → Law N)
    (W : I → Fin k → Fin N) :
    (p10_1kIdTupleArrayLaw μ).w W =
      ∏ id : I, p10_1kBlockTupleArrayWeight (μ id) (W id) := by
  rfl

/-- Coordinatewise events factor under the independent prospective-ID law. -/
theorem p10_1kIdTupleArrayLaw_pr_all {N k : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (μ : I → Law N)
    (F : I → (Fin k → Fin N) → Prop) :
    (p10_1kIdTupleArrayLaw μ).pr (fun W => ∀ id, F id (W id)) =
      ∏ id : I, (p10_1kBlockTupleArrayLaw (μ id)).pr (F id) := by
  classical
  change (FinProb.pi (fun id => p10_1kBlockTupleArrayLaw (μ id))).pr _ = _
  simp only [FinProb.pr, FinProb.pi]
  conv_rhs => rw [Fintype.prod_sum]
  apply Fintype.sum_congr
  intro W
  by_cases hW : ∀ id, F id (W id)
  · simp [hW]
  · have hbad : ∃ id, ¬ F id (W id) := by
      by_contra h
      push_neg at h
      exact hW h
    obtain ⟨id, hid⟩ := hbad
    rw [if_neg hW]
    have hzero :
        (if F id (W id) then (p10_1kBlockTupleArrayLaw (μ id)).w (W id) else 0) = 0 := by
      simp [hid]
    exact (Finset.prod_eq_zero (s := (Finset.univ : Finset I))
      (f := fun i => if F i (W i) then (p10_1kBlockTupleArrayLaw (μ i)).w (W i) else 0)
      (Finset.mem_univ id) hzero).symm

/-- Events restricted to a finite set of IDs still factor under the product
law; coordinates outside the set carry the trivial event. -/
theorem p10_1kIdTupleArrayLaw_pr_scope {N k : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (μ : I → Law N)
    (S : Finset I) (F : I → (Fin k → Fin N) → Prop) :
    (p10_1kIdTupleArrayLaw μ).pr (fun W => ∀ id ∈ S, F id (W id)) =
      ∏ id ∈ S, (p10_1kBlockTupleArrayLaw (μ id)).pr (F id) := by
  classical
  let F' : I → (Fin k → Fin N) → Prop :=
    fun id W => id ∈ S → F id W
  have hevent :
      (fun W : I → Fin k → Fin N => ∀ id ∈ S, F id (W id)) =
        (fun W : I → Fin k → Fin N => ∀ id, F' id (W id)) := by
    funext W
    apply propext
    simp [F']
  rw [hevent, p10_1kIdTupleArrayLaw_pr_all μ F']
  calc
    (∏ id : I, (p10_1kBlockTupleArrayLaw (μ id)).pr (F' id)) =
        ∏ id : I, if id ∈ S then
          (p10_1kBlockTupleArrayLaw (μ id)).pr (F id) else 1 := by
      apply Fintype.prod_congr
      intro id
      by_cases hid : id ∈ S
      · simp [F', hid]
      · simp [F', hid, FinProb.pr, (p10_1kBlockTupleArrayLaw (μ id)).sum_eq_one]
    _ = ∏ id ∈ S, (p10_1kBlockTupleArrayLaw (μ id)).pr (F id) := by
      simpa using (Finset.prod_filter (s := (Finset.univ : Finset I))
        (p := fun id => id ∈ S)
        (f := fun id => (p10_1kBlockTupleArrayLaw (μ id)).pr (F id))).symm

/-- Union bound for an `n`-tuple of pairwise distinct failed-list indices.
The injectivity premise makes the disjointness requirement explicit, so a
repeated list cannot be counted as an independent failure. -/
theorem p10_1k_disjoint_failure_union_bound_injective
    {Ω : Type*} [Fintype Ω] {L n : ℕ} (P : FinProb Ω)
    (failed : Fin L → Ω → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hproduct : ∀ f : Fin n → Fin L, Function.Injective f →
      P.pr (fun ω => ∀ i, failed (f i) ω) ≤ p ^ n) :
    P.pr (fun ω => ∃ f : Fin n → Fin L,
      Function.Injective f ∧ ∀ i, failed (f i) ω) ≤
        (L : ℝ) ^ n * p ^ n := by
  classical
  let good (f : Fin n → Fin L) (ω : Ω) : Prop :=
    Function.Injective f ∧ ∀ i, failed (f i) ω
  let indicator (f : Fin n → Fin L) (ω : Ω) : ℝ :=
    @ite ℝ (good f ω) (Classical.propDecidable _) (P.w ω) 0
  let unionIndicator (ω : Ω) : ℝ :=
    @ite ℝ (∃ f : Fin n → Fin L, good f ω)
      (Classical.propDecidable _) (P.w ω) 0
  have hpoint (ω : Ω) :
      unionIndicator ω ≤ ∑ f : Fin n → Fin L, indicator f ω := by
    by_cases hex : ∃ f : Fin n → Fin L, good f ω
    · have hunion : unionIndicator ω = P.w ω := by simp [unionIndicator, hex]
      rw [hunion]
      obtain ⟨f, hf⟩ := hex
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun g : Fin n → Fin L => indicator g ω)
        (fun g hg => by
          by_cases h : good g ω
          · simpa [indicator, h] using P.nonneg ω
          · simp [indicator, h])
        (Finset.mem_univ f)
      simpa [indicator, good, hf] using hsingle
    · have hunion : unionIndicator ω = 0 := by simp [unionIndicator, hex]
      rw [hunion]
      apply Finset.sum_nonneg
      intro f hf
      by_cases h : good f ω
      · simpa [indicator, h] using P.nonneg ω
      · simp [indicator, h]
  have hprob (f : Fin n → Fin L) : P.pr (fun ω => good f ω) ≤ p ^ n := by
    by_cases hinj : Function.Injective f
    · exact le_trans
        (p10_1k_FinProb_pr_mono P _ _ (fun ω hω => hω.2))
        (hproduct f hinj)
    · have hzero : P.pr (fun ω => good f ω) = 0 := by
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro ω hω
        simp [good, hinj]
      rw [hzero]
      exact pow_nonneg hp n
  calc
    P.pr (fun ω => ∃ f : Fin n → Fin L, good f ω) =
        ∑ ω, unionIndicator ω := by
      simp only [FinProb.pr]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ∃ f : Fin n → Fin L, good f ω <;>
        simp [unionIndicator, h]
    _ ≤ ∑ ω, ∑ f : Fin n → Fin L, indicator f ω := by
      apply Finset.sum_le_sum
      intro ω hω
      exact hpoint ω
    _ = ∑ f : Fin n → Fin L, P.pr (fun ω => good f ω) := by
      simp only [FinProb.pr, indicator]
      change (∑ ω ∈ (Finset.univ : Finset Ω),
        ∑ f ∈ (Finset.univ : Finset (Fin n → Fin L)),
          @ite ℝ (good f ω) (Classical.propDecidable _) (P.w ω) 0) =
        ∑ f ∈ (Finset.univ : Finset (Fin n → Fin L)),
          ∑ ω ∈ (Finset.univ : Finset Ω),
            @ite ℝ (good f ω) (Classical.propDecidable _) (P.w ω) 0
      exact Finset.sum_comm
    _ ≤ ∑ f : Fin n → Fin L, p ^ n := by
      apply Finset.sum_le_sum
      intro f hf
      exact hprob f
    _ = (L : ℝ) ^ n * p ^ n := by simp [Fintype.card_fun]

private theorem p10_1k_pr_congr {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A B : Ω → Prop) (hAB : ∀ ω, A ω ↔ B ω) :
    P.pr A = P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω
  · have hB : B ω := (hAB ω).mp hA
    simp [hA, hB]
  · have hB : ¬ B ω := fun h => hA ((hAB ω).mpr h)
    simp [hA, hB]

private theorem p10_1k_pr_eq_expect_indicator {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = P.expect (fun ω =>
      @ite ℝ (A ω) (Classical.propDecidable _) 1 0) := by
  classical
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω <;> simp [hA]

private theorem p10_1k_pr_and_eq_expect_mul {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A B : Ω → Prop) :
    P.pr (fun ω => A ω ∧ B ω) =
      P.expect (fun ω =>
        (@ite ℝ (A ω) (Classical.propDecidable _) 1 0) *
          (@ite ℝ (B ω) (Classical.propDecidable _) 1 0)) := by
  classical
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB]

/-- A family of events on pairwise disjoint product-coordinate scopes is
independent under the product law. -/
private theorem p10_1k_pi_pr_pairwise_disjoint_scopes
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (n : ℕ) :
    ∀ (F : Fin n → (∀ i, Ω i) → Prop) (S : Fin n → Finset I),
      (∀ j ω ω', (∀ i ∈ S j, ω i = ω' i) → (F j ω ↔ F j ω')) →
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (FinProb.pi P).pr (fun ω => ∀ j, F j ω) =
        ∏ j : Fin n, (FinProb.pi P).pr (F j) := by
  classical
  induction n with
  | zero =>
      intro F S hdep hdisj
      simp [FinProb.pr, (FinProb.pi P).sum_eq_one]
  | succ n ih =>
      intro F S hdep hdisj
      let F0 : (∀ i, Ω i) → Prop := fun ω => F 0 ω
      let Frest : Fin n → (∀ i, Ω i) → Prop := fun j ω => F j.succ ω
      let Srest : Fin n → Finset I := fun j => S j.succ
      let U : Finset I := Finset.univ.biUnion Srest
      have hrestSubset (j : Fin n) : Srest j ⊆ U := by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩
      have hrestEvent (ω ω' : ∀ i, Ω i)
          (hω : ∀ x ∈ U, ω x = ω' x) :
          (∀ j, Frest j ω) ↔ ∀ j, Frest j ω' := by
        constructor <;> intro h j
        · exact (hdep j.succ ω ω'
            (fun x hx => hω x (hrestSubset j hx))).mp (h j)
        · exact (hdep j.succ ω' ω
            (fun x hx => (hω x (hrestSubset j hx)).symm)).mp (h j)
      have hdep0 : FinProb.DependsOn
          (fun ω => @ite ℝ (F0 ω) (Classical.propDecidable _) 1 0) (S 0) := by
        intro ω ω' hω
        simp [F0, hdep 0 ω ω' hω]
      have hdepRest : FinProb.DependsOn
          (fun ω => @ite ℝ (∀ j, Frest j ω)
            (Classical.propDecidable _) 1 0) U := by
        intro ω ω' hω
        simp [hrestEvent ω ω' hω]
      have hdisj0 : Disjoint (S 0) U := by
        apply Finset.disjoint_left.mpr
        intro x hx0 hxU
        obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hxU
        have hne : (0 : Fin (n + 1)) ≠ j.succ := by
          intro heq
          exact (Fin.succ_ne_zero j) heq.symm
        exact (Finset.disjoint_left.mp (hdisj 0 j.succ hne)) hx0 hxj
      let Pπ : FinProb (∀ i, Ω i) := FinProb.pi P
      let f : (∀ i, Ω i) → ℝ := fun ω =>
        @ite ℝ (F0 ω) (Classical.propDecidable _) 1 0
      let g : (∀ i, Ω i) → ℝ := fun ω =>
        @ite ℝ (∀ j, Frest j ω) (Classical.propDecidable _) 1 0
      have hfactor := FinProb.pi_expect_mul_of_disjoint P f g (S 0) U
        hdep0 hdepRest hdisj0
      have hpr0 : Pπ.pr F0 = Pπ.expect f := by
        simpa [Pπ, f] using p10_1k_pr_eq_expect_indicator Pπ F0
      have hprRest : Pπ.pr (fun ω => ∀ j, Frest j ω) = Pπ.expect g := by
        simpa [Pπ, g] using
          p10_1k_pr_eq_expect_indicator Pπ (fun ω => ∀ j, Frest j ω)
      have hprAnd : Pπ.pr
          (fun ω => F0 ω ∧ ∀ j, Frest j ω) = Pπ.expect (fun ω => f ω * g ω) := by
        simpa [Pπ, f, g] using
          p10_1k_pr_and_eq_expect_mul Pπ F0 (fun ω => ∀ j, Frest j ω)
      have hsplit (ω : ∀ i, Ω i) :
          (∀ j : Fin (n + 1), F j ω) ↔ F0 ω ∧ ∀ j : Fin n, Frest j ω := by
        constructor
        · intro h
          exact ⟨h 0, fun j => h j.succ⟩
        · rintro ⟨h0, hrest⟩ j
          exact Fin.cases h0 hrest j
      have hprSplit : Pπ.pr (fun ω => ∀ j : Fin (n + 1), F j ω) =
          Pπ.pr (fun ω => F0 ω ∧ ∀ j : Fin n, Frest j ω) :=
        p10_1k_pr_congr Pπ _ _ hsplit
      have hdisjRest : ∀ i j, i ≠ j → Disjoint (Srest i) (Srest j) := by
        intro i j hij
        exact hdisj i.succ j.succ (Fin.succ_inj.not.2 hij)
      have hind := ih Frest Srest
        (fun j ω ω' hω => hdep j.succ ω ω'
          hω) hdisjRest
      have hprodStep :
          (∏ j : Fin (n + 1), Pπ.pr (F j)) =
            Pπ.pr (F 0) * ∏ j : Fin n, Pπ.pr (F j.succ) := by
        rw [Fin.prod_univ_succ]
      calc
        Pπ.pr (fun ω => ∀ j : Fin (n + 1), F j ω) =
            Pπ.pr (fun ω => F0 ω ∧ ∀ j : Fin n, Frest j ω) := hprSplit
        _ = Pπ.pr F0 * Pπ.pr (fun ω => ∀ j : Fin n, Frest j ω) := by
          calc
            Pπ.pr (fun ω => F0 ω ∧ ∀ j, Frest j ω) =
                Pπ.expect (fun ω => f ω * g ω) := hprAnd
            _ = Pπ.expect f * Pπ.expect g := hfactor
            _ = Pπ.pr F0 * Pπ.pr (fun ω => ∀ j, Frest j ω) := by
              rw [← hpr0, ← hprRest]
        _ = Pπ.pr F0 * ∏ j : Fin n, Pπ.pr (F j.succ) := by
          rw [hind]
        _ = ∏ j : Fin (n + 1), Pπ.pr (F j) := hprodStep.symm

/-- The probability of an event invariant outside a finite coordinate scope
is its probability under the product marginal on that scope. -/
private theorem p10_1k_pi_pr_depends_on_scope
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (S : Finset I)
    (A : (∀ i, Ω i) → Prop) (ω₀ : ∀ i, Ω i)
    (hdepends : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (A ω ↔ A ω')) :
    (FinProb.pi P).pr A =
      (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).pr
        (fun a => A ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω).symm
          (a, fun i : {i // i ∉ S} => ω₀ i.1))) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω
  let indicator : (∀ i, Ω i) → ℝ := fun ω =>
    @ite ℝ (A ω) (Classical.propDecidable _) 1 0
  let restrictedEvent : (∀ i : {i // i ∈ S}, Ω i.1) → Prop := fun a =>
    A (e.symm (a, fun i : {i // i ∉ S} => ω₀ i.1))
  have hindicator : FinProb.DependsOn indicator S := by
    intro ω ω' hω
    have hprop : A ω = A ω' := propext (hdepends ω ω' hω)
    simp [indicator, hprop]
  have hpi := FinProb.pi_expect_depends P S indicator ω₀ hindicator
  calc
    (FinProb.pi P).pr A = (FinProb.pi P).expect indicator := by
      simpa [indicator] using p10_1k_pr_eq_expect_indicator (FinProb.pi P) A
    _ = (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).expect
          (fun a => indicator (e.symm (a, fun i : {i // i ∉ S} => ω₀ i.1))) := hpi
    _ = (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).expect
          (fun a => if restrictedEvent a then (1 : ℝ) else 0) := by
      apply congrArg
      funext a
      simp [indicator, restrictedEvent, e]
    _ = (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).pr restrictedEvent := by
      symm
      exact p10_1k_pr_eq_expect_indicator
        (FinProb.pi (fun i : {i // i ∈ S} => P i.1)) restrictedEvent

/-- Reindexing a finite product law by an equivalence is the image law of the
corresponding assignment reindexing. -/
private theorem p10_1k_map_pr {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (P : FinProb A) (f : A → B) (F : B → Prop) :
    (FinProb.map P f).pr F = P.pr (fun a => F (f a)) := by
  classical
  calc
    (FinProb.map P f).pr F =
        (FinProb.map P f).expect
          (fun b => @ite ℝ (F b) (Classical.propDecidable _) 1 0) :=
      p10_1k_pr_eq_expect_indicator _ F
    _ = P.expect (fun a => @ite ℝ (F (f a)) (Classical.propDecidable _) 1 0) :=
      FinProb.map_expect P f
        (fun b => @ite ℝ (F b) (Classical.propDecidable _) 1 0)
    _ = P.pr (fun a => F (f a)) := by
      symm
      exact p10_1k_pr_eq_expect_indicator P (fun a => F (f a))

private theorem p10_1kFinProb_ext {Ω : Type*} [Fintype Ω]
    (P Q : FinProb Ω) (hw : P.w = Q.w) : P = Q := by
  cases P with
  | mk wP nonnegP sumP =>
    cases Q with
    | mk wQ nonnegQ sumQ =>
      have hweights : wP = wQ := hw
      subst wQ
      have hnonneg : nonnegP = nonnegQ := Subsingleton.elim _ _
      have hsum : sumP = sumQ := Subsingleton.elim _ _
      cases hnonneg
      cases hsum
      rfl

private theorem p10_1k_pi_map_equiv
    {A B Ω : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype Ω] [DecidableEq Ω]
    (e : A ≃ B) (P : A → FinProb Ω) (W : B → Ω) :
    (FinProb.map (FinProb.pi P) (fun x b => x (e.symm b))).w W =
      (FinProb.pi (fun b => P (e.symm b))).w W := by
  classical
  let pre : A → Ω := fun a => W (e a)
  have hpre : (fun b => pre (e.symm b)) = W := by
    funext b
    simp [pre]
  have hunique (V : A → Ω) (hV : V ≠ pre) :
      (fun b => V (e.symm b)) ≠ W := by
    intro h
    apply hV
    funext a
    have hpoint := congrFun h (e a)
    simpa [pre] using hpoint
  unfold FinProb.map FinProb.pi
  change (∑ V : A → Ω,
      if (fun b : B => V (e.symm b)) = W then
        ∏ a : A, (P a).w (V a) else 0) =
    ∏ b : B, (P (e.symm b)).w (W b)
  rw [Finset.sum_eq_single pre]
  · simp only [hpre, if_pos]
    exact Fintype.prod_equiv e
      (fun a => (P a).w (W (e a)))
      (fun b => (P (e.symm b)).w (W b))
      (by intro a; simp)
  · intro V hVmem hV
    simp [hunique V hV]
  · simp

/-- A global tuple field restricted to an enumerated finite ID set has the
fixed-list product law used by the P10.1c test. -/
private theorem p10_1kIdTupleArrayLaw_finset_reindex
    {N k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (μ : I → Law N) (S : Finset I) (r : ℕ)
    (e : Fin r ≃ {id // id ∈ S})
    (F : (Fin r → Fin k → Fin N) → Prop) (defaultTuple : Fin k → Fin N) :
    (p10_1kIdTupleArrayLaw μ).pr
      (fun W => F (fun b => W (e b).1)) =
      (p10_1kTupleArrayLaw (fun b => μ (e b).1)).pr F := by
  classical
  let P : I → FinProb (Fin k → Fin N) :=
    fun id => p10_1kBlockTupleArrayLaw (μ id)
  let fullEvent : (I → Fin k → Fin N) → Prop :=
    fun W => F (fun b => W (e b).1)
  let ePi := Equiv.piEquivPiSubtypeProd (fun id : I => id ∈ S)
    (fun _ : I => Fin k → Fin N)
  let outside : ∀ id : {id // id ∉ S}, Fin k → Fin N := fun _ => defaultTuple
  let restrictedLaw : FinProb (∀ id : {id // id ∈ S}, Fin k → Fin N) :=
    FinProb.pi (fun id => P id.1)
  let localEvent : (∀ id : {id // id ∈ S}, Fin k → Fin N) → Prop :=
    fun W => F (fun b => W (e b))
  have hdepends : ∀ W W', (∀ id ∈ S, W id = W' id) →
      (fullEvent W ↔ fullEvent W') := by
    intro W W' hW
    have hlist : (fun b => W (e b).1) = (fun b => W' (e b).1) := by
      funext b
      exact hW (e b).1 (e b).2
    change F (fun b => W (e b).1) ↔ F (fun b => W' (e b).1)
    rw [hlist]
  have hscope := p10_1k_pi_pr_depends_on_scope P S fullEvent
    (fun _ => defaultTuple) hdepends
  have hsubevent (W : ∀ id : {id // id ∈ S}, Fin k → Fin N) :
      fullEvent (ePi.symm (W, outside)) = localEvent W := by
    have hlist :
        (fun b => ePi.symm (W, outside) (e b).1) = fun b => W (e b) := by
      funext b
      have hcoord : ePi.symm (W, outside) (e b).1 = W (e b) := by
        simp only [ePi, Equiv.piEquivPiSubtypeProd_symm_apply,
          dif_pos (e b).2]
      exact hcoord
    exact congrArg F hlist
  have hscope' :
      (p10_1kIdTupleArrayLaw μ).pr fullEvent = restrictedLaw.pr localEvent := by
    calc
      (p10_1kIdTupleArrayLaw μ).pr fullEvent = (FinProb.pi P).pr fullEvent := by
        rfl
      _ = restrictedLaw.pr (fun W => fullEvent (ePi.symm (W, outside))) := by
        simpa [P, restrictedLaw, fullEvent, ePi, outside] using hscope
      _ = restrictedLaw.pr localEvent := by
        apply p10_1k_pr_congr
        intro W
        exact Iff.of_eq (hsubevent W)
  let reindex : (∀ id : {id // id ∈ S}, Fin k → Fin N) →
      (Fin r → Fin k → Fin N) := fun W b => W (e b)
  let fixedListLaw : FinProb (Fin r → Fin k → Fin N) :=
    p10_1kTupleArrayLaw (k := k) (fun b => μ (e b).1)
  have hmap : FinProb.map restrictedLaw reindex = fixedListLaw := by
    apply p10_1kFinProb_ext
    funext W
    simpa [P, restrictedLaw, fixedListLaw, reindex,
      p10_1kTupleArrayLaw, p10_1kBlockTupleArrayLaw] using
      (p10_1k_pi_map_equiv e.symm (fun id => P id.1) W)
  calc
    (p10_1kIdTupleArrayLaw μ).pr fullEvent = restrictedLaw.pr localEvent := hscope'
    _ = (FinProb.map restrictedLaw reindex).pr F :=
      (p10_1k_map_pr restrictedLaw reindex F).symm
    _ = fixedListLaw.pr F := by rw [hmap]

/-- Changing arrays outside a finite ID scope does not change its
fixed-list failure event. -/
theorem p10_1k_fixedListFailure_depends_on_scope {N k q r : ℕ} {I : Type*}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N)
    (μ : Fin r → Law N) (a : ℝ) (S : Finset I)
    (e : Fin r ≃ {id // id ∈ S})
    (W W' : I → Fin k → Fin N)
    (hW : ∀ id ∈ S, W id = W' id) :
    fixedListFailure E G ρ D μ a (fun b i => W (e b).1 i) ↔
      fixedListFailure E G ρ D μ a (fun b i => W' (e b).1 i) := by
  have hlist : (fun b i => W (e b).1 i) = (fun b i => W' (e b).1 i) := by
    funext b
    funext i
    exact congrFun (hW (e b).1 (e b).2) i
  rw [hlist]

/-- A P10.1c failure-probability estimate on a fixed list transfers to the
global independent tuple field by restricting to the list's ID scope. -/
theorem p10_1kIdTupleArrayLaw_fixedListFailure_bound
    {N k q : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (μ : I → Law N) (S : Finset I) (r : ℕ)
    (e : Fin r ≃ {id // id ∈ S})
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (a ε : ℝ)
    (defaultTuple : Fin k → Fin N)
    (hfail : (p10_1kTupleArrayLaw (k := k)
      (fun b => μ (e b).1)).pr
      (fixedListFailure (k := k) (q := q) E G ρ D
        (fun b => μ (e b).1) a) ≤ ε) :
    (p10_1kIdTupleArrayLaw (k := k) μ).pr (fun W =>
      fixedListFailure (k := k) (q := q) E G ρ D
        (fun b => μ (e b).1) a
        (fun b i => W (e b).1 i)) ≤ ε := by
  rw [p10_1kIdTupleArrayLaw_finset_reindex (k := k) μ S r e
    (fixedListFailure (k := k) (q := q) E G ρ D
      (fun b => μ (e b).1) a) defaultTuple]
  exact hfail

/-- A slice is named by the exact word on the `m` special coordinates. -/
abbrev P10_1kSpecialSliceWord (m : ℕ) := Fin m → Bool

/-- A global prospective center ID consists of its special slice and the
residual location-level pair used by the height device. -/
abbrev P10_1kProspectiveId (n m : ℕ) (δ : ℝ) :=
  P10_1kSpecialSliceWord m × (p10_1kHeightParams n m δ).Loc

/-- Independent tuple arrays at every global prospective ID, with one
first-side law per special slice. -/
noncomputable def p10_1kGlobalTupleArrayLaw {N k : ℕ} (n m : ℕ) (δ : ℝ)
    (μ : P10_1kSpecialSliceWord m → Law N) :
    FinProb (P10_1kProspectiveId n m δ → Fin k → Fin N) :=
  p10_1kIdTupleArrayLaw (fun id => μ id.1)

/-- The global tuple-array sample has the product weight over slice-level IDs. -/
theorem p10_1kGlobalTupleArrayLaw_weight {N k : ℕ} (n m : ℕ) (δ : ℝ)
    (μ : P10_1kSpecialSliceWord m → Law N)
    (W : P10_1kProspectiveId n m δ → Fin k → Fin N) :
    (p10_1kGlobalTupleArrayLaw n m δ μ).w W =
      ∏ id : P10_1kProspectiveId n m δ,
        p10_1kBlockTupleArrayWeight (μ id.1) (W id) := by
  rfl

/-- List-failure events on pairwise disjoint prospective-ID scopes are
independent under the pre-generated tuple-array law. -/
theorem p10_1kIdTupleArrayLaw_disjoint_events {N k : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (μ : I → Law N)
    (n L : ℕ) (S : Fin L → Finset I)
    (F : Fin L → (I → Fin k → Fin N) → Prop)
    (hdepends : ∀ ℓ W W', (∀ id ∈ S ℓ, W id = W' id) →
      (F ℓ W ↔ F ℓ W'))
    (hdisjoint : ∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (S ℓ) (S ℓ'))
    (choose : Fin n → Fin L) (hinj : Function.Injective choose) :
    (p10_1kIdTupleArrayLaw μ).pr (fun W => ∀ i, F (choose i) W) =
      ∏ i : Fin n,
        (p10_1kIdTupleArrayLaw μ).pr (fun W => F (choose i) W) := by
  classical
  let P : I → FinProb (Fin k → Fin N) :=
    fun id => p10_1kBlockTupleArrayLaw (μ id)
  have hfactor := p10_1k_pi_pr_pairwise_disjoint_scopes P n
    (fun i W => F (choose i) W) (fun i => S (choose i))
    (fun i W W' hW => hdepends (choose i) W W' hW)
    (fun i j hij => hdisjoint (choose i) (choose j)
      (fun hEq => hij (hinj hEq)))
  simpa [p10_1kIdTupleArrayLaw, P] using hfactor

/-- If every candidate list fails with probability at most `ε`, the chance of
finding `n` pairwise disjoint failed lists is at most `L^n ε^n`. -/
theorem p10_1kIdTupleArrayLaw_disjoint_failure_union_bound
    {N k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (μ : I → Law N) (n L : ℕ) (S : Fin L → Finset I)
    (F : Fin L → (I → Fin k → Fin N) → Prop)
    (hdepends : ∀ ℓ W W', (∀ id ∈ S ℓ, W id = W' id) →
      (F ℓ W ↔ F ℓ W'))
    (hdisjoint : ∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (S ℓ) (S ℓ'))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hprob : ∀ ℓ,
      (p10_1kIdTupleArrayLaw μ).pr (F ℓ) ≤ ε) :
    (p10_1kIdTupleArrayLaw μ).pr (fun W => ∃ choose : Fin n → Fin L,
      Function.Injective choose ∧ ∀ i, F (choose i) W) ≤
        (L : ℝ) ^ n * ε ^ n := by
  have hproduct : ∀ choose : Fin n → Fin L, Function.Injective choose →
      (p10_1kIdTupleArrayLaw μ).pr
        (fun W => ∀ i, F (choose i) W) ≤ ε ^ n := by
    intro choose hinj
    rw [p10_1kIdTupleArrayLaw_disjoint_events μ n L S F
      hdepends hdisjoint choose hinj]
    have hnonneg (i : Fin n) :
        0 ≤ (p10_1kIdTupleArrayLaw μ).pr (F (choose i)) := by
      unfold FinProb.pr
      apply Finset.sum_nonneg
      intro W hW
      split_ifs
      · exact (p10_1kIdTupleArrayLaw μ).nonneg W
      · exact le_rfl
    calc
      (∏ i : Fin n, (p10_1kIdTupleArrayLaw μ).pr (F (choose i))) ≤
          ∏ i : Fin n, ε := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact hnonneg i
        · intro i hi
          exact hprob (choose i)
      _ = ε ^ n := by simp
  exact p10_1k_disjoint_failure_union_bound_injective
    (p10_1kIdTupleArrayLaw μ) F ε hε hproduct

/-- Independent prospective-center positions over all special slices. -/
noncomputable def p10_1kGlobalPositionLaw (n m : ℕ) (δ : ℝ) :
    FinProb (P10_1kProspectiveId n m δ → Bool) := by
  let p := p10_1kHeightParams n m δ
  exact FinProb.pi (fun _ => FinProb.bernoulli (p.lam / (p.V : ℝ)))

/-- Independent activations over all global prospective IDs. -/
noncomputable def p10_1kGlobalActivationLaw (n m : ℕ) (δ : ℝ) :
    FinProb (P10_1kProspectiveId n m δ → Bool) := by
  let p := p10_1kHeightParams n m δ
  exact FinProb.pi (fun _ => FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam))

/-- Independent uniform tie permutations at each global site-level. -/
noncomputable def p10_1kGlobalTieLaw (n m : ℕ) (δ : ℝ) :
    FinProb (P10_1kProspectiveId n m δ →
      (p10_1kHeightParams n m δ).TiePerm) := by
  let p := p10_1kHeightParams n m δ
  exact FinProb.pi (fun _ => FinProb.uniformAll ⟨1⟩)

/-- A positive tuple-array atom has positive first-side mass at every entry. -/
theorem p10_1k_tupleArrayWeight_entries_pos {N r k : ℕ}
    (μ : Fin r → Law N) (W : Fin r → Fin k → Fin N)
    (hW : 0 < tupleArrayWeight μ W) :
    ∀ b i, 0 < (μ b).w (W b i) := by
  classical
  have houter : ∀ b, (∏ i : Fin k, (μ b).w (W b i)) ≠ 0 := by
    have hne : (∏ b : Fin r, ∏ i : Fin k, (μ b).w (W b i)) ≠ 0 :=
      ne_of_gt hW
    intro b
    exact (Finset.prod_ne_zero_iff.mp hne) b (Finset.mem_univ _)
  intro b i
  have hinner : (μ b).w (W b i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp (houter b)) i (Finset.mem_univ _)
  exact lt_of_le_of_ne ((μ b).nonneg (W b i)) (Ne.symm hinner)

/-- The tuple-array law and its weight have the same positive support. -/
theorem p10_1k_tupleArrayLaw_entries_pos {N r k : ℕ}
    (μ : Fin r → Law N) (W : Fin r → Fin k → Fin N)
    (hW : 0 < (p10_1kTupleArrayLaw μ).w W) :
    ∀ b i, 0 < (μ b).w (W b i) :=
  p10_1k_tupleArrayWeight_entries_pos μ W (by simpa [p10_1kTupleArrayLaw_weight] using hW)

/-- The Section 10 special-coordinate, tuple-list, and height-count scales. -/
noncomputable def p10_1kSpecialCount (n : ℕ) (δ : ℝ) : ℕ := ⌊(n : ℝ) ^ (200 * δ)⌋₊
noncomputable def p10_1kTupleListLength (n : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) ^ (300 * δ)⌉₊
noncomputable def p10_1kHeightCount (n : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) ^ (141 * δ)⌉₊

/-- A fixed-list test uses at most the special-coordinate and height-count
number of blocks. -/
noncomputable def p10_1kFixedListBlockCount (n : ℕ) (δ : ℝ) : ℕ :=
  p10_1kSpecialCount n δ + p10_1kHeightCount n δ

/-- Cast bounds for the rounded fixed-list parameters. -/
theorem p10_1kFixedListScale_rounding_bounds (n : ℕ) (δ : ℝ)
    (hn : 2 ≤ n) (hδ : 0 < δ) :
    (p10_1kSpecialCount n δ : ℝ) ≤ (n : ℝ) ^ (200 * δ) ∧
      (p10_1kTupleListLength n δ : ℝ) ≤ 2 * (n : ℝ) ^ (300 * δ) ∧
      (p10_1kFixedListBlockCount n δ : ℝ) ≤ 3 * (n : ℝ) ^ (200 * δ) := by
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have h200 : (n : ℝ) ^ (141 * δ) ≤ (n : ℝ) ^ (200 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hnreal (by nlinarith)
  have hm : (p10_1kSpecialCount n δ : ℝ) ≤ (n : ℝ) ^ (200 * δ) := by
    dsimp [p10_1kSpecialCount]
    exact Nat.floor_le (by positivity)
  have hkNat : p10_1kTupleListLength n δ ≤
      ⌊(n : ℝ) ^ (300 * δ)⌋₊ + 1 := by
    exact Nat.ceil_le_floor_add_one _
  have hkCast : (p10_1kTupleListLength n δ : ℝ) ≤
      (n : ℝ) ^ (300 * δ) + 1 := by
    calc
      (p10_1kTupleListLength n δ : ℝ) ≤
          (⌊(n : ℝ) ^ (300 * δ)⌋₊ : ℝ) + 1 := by exact_mod_cast hkNat
      _ ≤ (n : ℝ) ^ (300 * δ) + 1 := by
        have hfloor := Nat.floor_le (by positivity : 0 ≤ (n : ℝ) ^ (300 * δ))
        linarith
  have hk : (p10_1kTupleListLength n δ : ℝ) ≤
      2 * (n : ℝ) ^ (300 * δ) := by
    have hpow : 1 ≤ (n : ℝ) ^ (300 * δ) := by
      calc
        1 = (n : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
        _ ≤ (n : ℝ) ^ (300 * δ) :=
          Real.rpow_le_rpow_of_exponent_le hnreal (by positivity)
    nlinarith [hkCast, hpow]
  have hTNat : p10_1kHeightCount n δ ≤
      ⌊(n : ℝ) ^ (141 * δ)⌋₊ + 1 := by
    exact Nat.ceil_le_floor_add_one _
  have hTCast : (p10_1kHeightCount n δ : ℝ) ≤
      (n : ℝ) ^ (141 * δ) + 1 := by
    calc
      (p10_1kHeightCount n δ : ℝ) ≤
          (⌊(n : ℝ) ^ (141 * δ)⌋₊ : ℝ) + 1 := by exact_mod_cast hTNat
      _ ≤ (n : ℝ) ^ (141 * δ) + 1 := by
        have hfloor := Nat.floor_le (by positivity : 0 ≤ (n : ℝ) ^ (141 * δ))
        linarith
  have hblocks : (p10_1kFixedListBlockCount n δ : ℝ) ≤
      3 * (n : ℝ) ^ (200 * δ) := by
    dsimp [p10_1kFixedListBlockCount]
    rw [Nat.cast_add]
    have hr : 1 ≤ (n : ℝ) ^ (141 * δ) := by
      calc
        1 = (n : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
        _ ≤ (n : ℝ) ^ (141 * δ) :=
          Real.rpow_le_rpow_of_exponent_le hnreal (by positivity)
    nlinarith [hm, hTCast, h200, hr]
  exact ⟨hm, hk, hblocks⟩

/-- Total error budget for the absolute-mass and deletion-ratio gates in the
retained squared-tilt cluster draw. -/
noncomputable def p10_1kRetainedTiltBudget (n : ℕ) (δ : ℝ) : ℝ :=
  Real.exp (-((p10_1kTupleListLength n δ : ℝ) *
      (p10_1kFixedListBlockCount n δ : ℝ))) +
    (p10_1kFixedListBlockCount n δ : ℝ) *
      (Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (-δ) *
        (p10_1kTupleListLength n δ : ℝ))) +
       Real.exp (-((2 / 5 : ℝ) *
        (p10_1kTupleListLength n δ : ℝ))))

/-- A simpler eventual majorant for the retained-tilt budget. -/
noncomputable def p10_1kRetainedTiltBudgetMajorant (n : ℕ) (δ : ℝ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (500 * δ)) +
    3 * (n : ℝ) ^ (200 * δ) *
      Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) +
    3 * (n : ℝ) ^ (200 * δ) *
      Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ)))

/-- The rounded fixed-list parameters make the retained-tilt error budget less
than one half for all sufficiently large dimensions. -/
theorem p10_1k_fixedList_retainedTilt_budget_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, p10_1kRetainedTiltBudget n δ ≤ 1 / 2 := by
  have hn2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  have hpow200 := p10_1k_eventually_power_gap
    (a := 0) (b := 200 * δ) (c := 2) (by positivity) (by norm_num)
  have hA : Tendsto
      (fun n : ℕ => Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (500 * δ)))
      atTop (nhds 0) := by
    simpa using
      (p10_1k_power_exp_neg_tendsto
        (a := 500 * δ) (b := 0) (c := (1 / 2 : ℝ))
        (by positivity) (by positivity) (by norm_num))
  have hOwn : Tendsto
      (fun n : ℕ => 3 * (n : ℝ) ^ (200 * δ) *
        Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))))
      atTop (nhds 0) := by
    have h := p10_1k_power_exp_neg_tendsto
      (a := 299 * δ) (b := 200 * δ) (c := (6 / 25 : ℝ))
      (by positivity) (by nlinarith) (by norm_num)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h.const_mul (3 : ℝ)
  have hExternal : Tendsto
      (fun n : ℕ => 3 * (n : ℝ) ^ (200 * δ) *
        Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ))))
      atTop (nhds 0) := by
    have h := p10_1k_power_exp_neg_tendsto
      (a := 300 * δ) (b := 200 * δ) (c := (2 / 5 : ℝ))
      (by positivity) (by nlinarith) (by norm_num)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h.const_mul (3 : ℝ)
  have hMajorant : Tendsto (p10_1kRetainedTiltBudgetMajorant · δ)
      atTop (nhds 0) := by
    simpa [p10_1kRetainedTiltBudgetMajorant, add_assoc] using
      (hA.add hOwn).add hExternal
  have hsmall : ∀ᶠ n : ℕ in atTop,
      p10_1kRetainedTiltBudgetMajorant n δ < 1 / 2 :=
    hMajorant.eventually (Iio_mem_nhds (by norm_num))
  have hdom : ∀ᶠ n : ℕ in atTop,
      p10_1kRetainedTiltBudget n δ ≤ p10_1kRetainedTiltBudgetMajorant n δ := by
    filter_upwards [hn2, hpow200] with n hn hpow
    let x : ℝ := (n : ℝ)
    let m : ℕ := p10_1kSpecialCount n δ
    let k : ℕ := p10_1kTupleListLength n δ
    let r : ℕ := p10_1kFixedListBlockCount n δ
    have hxpos : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < n)
    have hxone : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ n)
    have hlarge : 2 < x ^ (200 * δ) := by
      have hpow' : 2 * x ^ (0 : ℝ) < x ^ (200 * δ) := by simpa [x] using hpow
      simpa using hpow'
    have hfloor : x ^ (200 * δ) < (m : ℝ) + 1 := by
      dsimp [x, m, p10_1kSpecialCount]
      exact Nat.lt_floor_add_one _
    have hmLower : x ^ (200 * δ) / 2 ≤ (m : ℝ) := by
      calc
        x ^ (200 * δ) / 2 ≤ x ^ (200 * δ) - 1 := by
          have hX : 2 ≤ x ^ (200 * δ) := hlarge.le
          have hhalf : 1 ≤ x ^ (200 * δ) / 2 := by
            rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
            calc
              (1 : ℝ) * 2 = 2 := by norm_num
              _ ≤ x ^ (200 * δ) := hX
          calc
            x ^ (200 * δ) / 2 ≤ x ^ (200 * δ) / 2 +
                (x ^ (200 * δ) / 2 - 1) :=
              le_add_of_nonneg_right (sub_nonneg.mpr hhalf)
            _ = x ^ (200 * δ) - 1 := by ring
        _ ≤ (m : ℝ) := by linarith [hfloor]
    have hTnonneg : 0 ≤ (p10_1kHeightCount n δ : ℝ) := Nat.cast_nonneg _
    have hrLower : x ^ (200 * δ) / 2 ≤ (r : ℝ) := by
      dsimp [r, p10_1kFixedListBlockCount]
      rw [Nat.cast_add]
      exact le_trans hmLower (by nlinarith [hTnonneg])
    have hkLower : x ^ (300 * δ) ≤ (k : ℝ) := by
      dsimp [x, k, p10_1kTupleListLength]
      exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ (300 * δ)))
    have hround := p10_1kFixedListScale_rounding_bounds n δ hn hδ
    have hrUpper : (r : ℝ) ≤ 3 * x ^ (200 * δ) := by
      simpa [r, x] using hround.2.2
    have hpow500 : x ^ (300 * δ) * x ^ (200 * δ) = x ^ (500 * δ) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    have hkrLower : (1 / 2 : ℝ) * x ^ (500 * δ) ≤
        (k : ℝ) * (r : ℝ) := by
      calc
        (1 / 2 : ℝ) * x ^ (500 * δ) =
            x ^ (300 * δ) * (x ^ (200 * δ) / 2) := by
          rw [← hpow500]
          ring
        _ ≤ (k : ℝ) * (r : ℝ) :=
          mul_le_mul hkLower hrLower (by positivity) (by positivity)
    have hpow299 : x ^ (-δ) * x ^ (300 * δ) = x ^ (299 * δ) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    have hgainK : x ^ (299 * δ) ≤ x ^ (-δ) * (k : ℝ) := by
      calc
        x ^ (299 * δ) = x ^ (-δ) * x ^ (300 * δ) := hpow299.symm
        _ ≤ x ^ (-δ) * (k : ℝ) :=
          mul_le_mul_of_nonneg_left hkLower (Real.rpow_nonneg hxpos.le _)
    have hAbsExp : Real.exp (-((k : ℝ) * (r : ℝ))) ≤
        Real.exp (-(1 / 2 : ℝ) * x ^ (500 * δ)) :=
      Real.exp_le_exp.mpr (by nlinarith [hkrLower])
    have hOwnExp :
        Real.exp (-((6 / 25 : ℝ) * x ^ (-δ) * (k : ℝ))) ≤
          Real.exp (-((6 / 25 : ℝ) * x ^ (299 * δ))) :=
      Real.exp_le_exp.mpr (by nlinarith [hgainK])
    have hExtExp : Real.exp (-((2 / 5 : ℝ) * (k : ℝ))) ≤
        Real.exp (-((2 / 5 : ℝ) * x ^ (300 * δ))) :=
      Real.exp_le_exp.mpr (by nlinarith [hkLower])
    unfold p10_1kRetainedTiltBudget p10_1kRetainedTiltBudgetMajorant
    calc
      Real.exp (-((k : ℝ) * (r : ℝ))) + (r : ℝ) *
          (Real.exp (-((6 / 25 : ℝ) * x ^ (-δ) * (k : ℝ))) +
            Real.exp (-((2 / 5 : ℝ) * (k : ℝ)))) =
          Real.exp (-((k : ℝ) * (r : ℝ))) +
            (r : ℝ) * Real.exp (-((6 / 25 : ℝ) * x ^ (-δ) * (k : ℝ))) +
            (r : ℝ) * Real.exp (-((2 / 5 : ℝ) * (k : ℝ))) := by ring
      _ ≤ Real.exp (-(1 / 2 : ℝ) * x ^ (500 * δ)) +
          3 * x ^ (200 * δ) * Real.exp (-((6 / 25 : ℝ) * x ^ (299 * δ))) +
          3 * x ^ (200 * δ) * Real.exp (-((2 / 5 : ℝ) * x ^ (300 * δ))) := by
        gcongr
  filter_upwards [hdom, hsmall] with n hdom hsmall
  exact le_trans hdom hsmall.le

/-- The rounded tuple-list length and block count are positive, eventually. -/
theorem p10_1k_fixedList_counts_positive_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 0 < p10_1kFixedListBlockCount n δ ∧
        0 < p10_1kTupleListLength n δ := by
  have hM := p10_1k_eventually_power_gap
    (by positivity : (0 : ℝ) < 200 * δ) (by norm_num : (0 : ℝ) < 1)
  have hK := p10_1k_eventually_power_gap
    (by positivity : (0 : ℝ) < 300 * δ) (by norm_num : (0 : ℝ) < 1)
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hM, hK, hnlarge] with n hM hK hn
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hmreal : (1 : ℝ) ≤ (n : ℝ) ^ (200 * δ) := by
    simpa [Real.rpow_zero] using hM.le
  have hmNat : 1 ≤ p10_1kSpecialCount n δ := by
    dsimp [p10_1kSpecialCount]
    exact Nat.le_floor (by simpa using hmreal)
  have hkreal : (1 : ℝ) ≤ (n : ℝ) ^ (300 * δ) := by
    simpa [Real.rpow_zero] using hK.le
  have hkcast : (1 : ℝ) ≤ (p10_1kTupleListLength n δ : ℝ) := by
    calc
      1 ≤ (n : ℝ) ^ (300 * δ) := hkreal
      _ ≤ (p10_1kTupleListLength n δ : ℝ) := by
        dsimp [p10_1kTupleListLength]
        exact Nat.le_ceil _
  have hkNat : 1 ≤ p10_1kTupleListLength n δ := by exact_mod_cast hkcast
  refine ⟨hn, ?_⟩
  constructor
  · dsimp [p10_1kFixedListBlockCount]
    omega
  · omega

/-- The rounded block and list lengths leave enough exponential hit-set mass
to contain at least `n` labels, eventually. -/
theorem p10_1k_fixedList_hit_support_scale_eventually (ζ δ : ℝ)
    (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min 1 ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ≤ Real.exp ((n : ℝ) ^ ζ -
        (p10_1kTupleListLength n δ : ℝ) *
          (p10_1kFixedListBlockCount n δ : ℝ)) := by
  have hminζ : min (min 1 ζ) 1 ≤ ζ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hδζ : δ < ζ / 2000 := by
    exact lt_of_lt_of_le hδsmall
      (div_le_div_of_nonneg_right hminζ (by norm_num))
  have h500ζ : 500 * δ < ζ := by nlinarith [hδζ]
  have hδζ' : δ < ζ := by nlinarith [hδζ, hζ]
  have hgap12 := p10_1k_eventually_power_gap h500ζ (by norm_num : (0 : ℝ) < 12)
  have hgap2div := p10_1k_eventually_power_gap hδζ'
    (div_pos (by norm_num : (0 : ℝ) < 2) hδ)
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hgap12, hgap2div, hnlarge] with n hgap12 hgap2div hn
  let x : ℝ := (n : ℝ)
  have hnreal : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show (1 : ℕ) ≤ n by omega)
  have hnpos : 0 < x := lt_of_lt_of_le (by norm_num) hnreal
  have hround := p10_1kFixedListScale_rounding_bounds n δ hn hδ
  have hk : (p10_1kTupleListLength n δ : ℝ) ≤ 2 * x ^ (300 * δ) := by
    simpa [x] using hround.2.1
  have hr : (p10_1kFixedListBlockCount n δ : ℝ) ≤ 3 * x ^ (200 * δ) := by
    simpa [x] using hround.2.2
  have hpow : x ^ (300 * δ) * x ^ (200 * δ) = x ^ (500 * δ) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hkr : (p10_1kTupleListLength n δ : ℝ) *
      (p10_1kFixedListBlockCount n δ : ℝ) ≤ 6 * x ^ (500 * δ) := by
    have hmul := mul_le_mul hk hr (by positivity) (by positivity)
    calc
      (p10_1kTupleListLength n δ : ℝ) *
          (p10_1kFixedListBlockCount n δ : ℝ) ≤
        (2 * x ^ (300 * δ)) * (3 * x ^ (200 * δ)) := hmul
      _ = 6 * (x ^ (300 * δ) * x ^ (200 * δ)) := by ring
      _ = 6 * x ^ (500 * δ) := by rw [hpow]
  have hlogN : Real.log x ≤ x ^ δ / δ := by
    simpa [x] using Real.log_natCast_le_rpow_div n hδ
  have hLogTwice : 2 * Real.log x < x ^ ζ := by
    calc
      2 * Real.log x ≤ 2 * (x ^ δ / δ) :=
        mul_le_mul_of_nonneg_left hlogN (by norm_num)
      _ = (2 / δ) * x ^ δ := by ring
      _ < x ^ ζ := by simpa [x] using hgap2div
  have hKRTwice : 2 * ((p10_1kTupleListLength n δ : ℝ) *
      (p10_1kFixedListBlockCount n δ : ℝ)) < x ^ ζ := by
    calc
      2 * ((p10_1kTupleListLength n δ : ℝ) *
          (p10_1kFixedListBlockCount n δ : ℝ)) ≤ 12 * x ^ (500 * δ) := by
        nlinarith [hkr]
      _ < x ^ ζ := hgap12
  have hsum : Real.log x +
      (p10_1kTupleListLength n δ : ℝ) *
        (p10_1kFixedListBlockCount n δ : ℝ) < x ^ ζ := by
    nlinarith [hLogTwice, hKRTwice]
  have hexp : x ≤ Real.exp (x ^ ζ -
      (p10_1kTupleListLength n δ : ℝ) *
        (p10_1kFixedListBlockCount n δ : ℝ)) := by
    apply (Real.log_le_iff_le_exp hnpos).mp
    linarith [hsum]
  simpa [x] using hexp

/-- The first six quantitative hypotheses of the fixed-list test hold for the
rounded Section 10 choices, eventually. -/
theorem p10_1k_fixedList_basic_premises_eventually (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      let r := p10_1kFixedListBlockCount n δ
      let k := p10_1kTupleListLength n δ
      let ε := (n : ℝ) ^ (-η₀)
      let a := (n : ℝ) ^ (-δ)
      let w := (n : ℝ) ^ η₀
      let wμ := (n : ℝ) ^ δ
      let wν := (n : ℝ) ^ δ
      0 ≤ ε ∧ 100 * ε ≤ a ∧ a ≤ 1 / 10 ∧
        wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤ w ∧
        Real.log ((r : ℝ) + 1) ≤ a ^ 2 * (k : ℝ) / 100 := by
  have hηδ : δ < η₀ / 2000 := by
    have hmin : min (min η₀ ζ) 1 ≤ η₀ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    exact lt_of_lt_of_le hδsmall
      (div_le_div_of_nonneg_right hmin (by norm_num))
  have hδη : δ < η₀ := by nlinarith [hηδ]
  have h500η : 500 * δ < η₀ := by nlinarith [hηδ]
  have h200298 : 200 * δ < 298 * δ := by nlinarith [hδ]
  have hgap100 := p10_1k_eventually_power_gap hδη (by norm_num : (0 : ℝ) < 100)
  have hgap10 := p10_1k_eventually_power_gap
    (by nlinarith [hδ] : (0 : ℝ) < δ) (by norm_num : (0 : ℝ) < 10)
  have hgap16 := p10_1k_eventually_power_gap h500η (by norm_num : (0 : ℝ) < 16)
  have hgap300 := p10_1k_eventually_power_gap h200298 (by norm_num : (0 : ℝ) < 300)
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hgap100, hgap10, hgap16, hgap300, hnlarge]
    with n hgap100 hgap10 hgap16 hgap300 hn
  let x : ℝ := (n : ℝ)
  let r := p10_1kFixedListBlockCount n δ
  let k := p10_1kTupleListLength n δ
  let ε : ℝ := x ^ (-η₀)
  let a : ℝ := x ^ (-δ)
  let w : ℝ := x ^ η₀
  let wμ : ℝ := x ^ δ
  let wν : ℝ := x ^ δ
  have hnreal : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show (1 : ℕ) ≤ n by omega)
  have hnpos : 0 < x := lt_of_lt_of_le (by norm_num) hnreal
  have hδpow : 1 ≤ x ^ δ := by
    calc
      1 = x ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ x ^ δ := Real.rpow_le_rpow_of_exponent_le hnreal (by positivity)
  have hpow141200 : x ^ (141 * δ) ≤ x ^ (200 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hnreal (by nlinarith [hδ])
  have hpowδ500 : x ^ δ ≤ x ^ (500 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hnreal (by nlinarith [hδ])
  have hround := p10_1kFixedListScale_rounding_bounds n δ hn hδ
  have hr : (r : ℝ) ≤ 3 * x ^ (200 * δ) := by
    simpa [r, x] using hround.2.2
  have hk : (k : ℝ) ≤ 2 * x ^ (300 * δ) := by
    simpa [k, x] using hround.2.1
  have hkLower : x ^ (300 * δ) ≤ (k : ℝ) := by
    dsimp [k, p10_1kTupleListLength, x]
    exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ (300 * δ)))
  have hRplus : (r : ℝ) + 1 ≤ 4 * x ^ (200 * δ) := by
    have hr' := hr
    have hpow : 1 ≤ x ^ (200 * δ) := by
      calc
        1 = x ^ (0 : ℝ) := by rw [Real.rpow_zero]
        _ ≤ x ^ (200 * δ) :=
          Real.rpow_le_rpow_of_exponent_le hnreal (by positivity)
    nlinarith [hr', hpow]
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    nlinarith
  have hkr : 2 * (k : ℝ) * (r : ℝ) ≤ 12 * x ^ (500 * δ) := by
    have hmul : (k : ℝ) * (r : ℝ) ≤
        (2 * x ^ (300 * δ)) * (3 * x ^ (200 * δ)) :=
      mul_le_mul hk hr (by positivity) (by positivity)
    have hmul2 : 2 * ((k : ℝ) * (r : ℝ)) ≤
        2 * ((2 * x ^ (300 * δ)) * (3 * x ^ (200 * δ))) :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    have hpow : x ^ (300 * δ) * x ^ (200 * δ) = x ^ (500 * δ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    calc
      2 * (k : ℝ) * (r : ℝ) = 2 * ((k : ℝ) * (r : ℝ)) := by ring
      _ ≤ 2 * ((2 * x ^ (300 * δ)) * (3 * x ^ (200 * δ))) := hmul2
      _ = 12 * x ^ (500 * δ) := by
        calc
          2 * ((2 * x ^ (300 * δ)) * (3 * x ^ (200 * δ))) =
              12 * (x ^ (300 * δ) * x ^ (200 * δ)) := by ring
          _ = 12 * x ^ (500 * δ) := by rw [hpow]
  have hwidth : wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤ w := by
    have hpowBound : x ^ δ + Real.log 4 ≤ 4 * x ^ (500 * δ) := by
      calc
        x ^ δ + Real.log 4 ≤ x ^ δ + 3 := by gcongr
        _ ≤ x ^ δ + 3 * x ^ δ := by
          have h3 : (3 : ℝ) ≤ 3 * x ^ δ := by
            simpa using mul_le_mul_of_nonneg_left hδpow (by norm_num : (0 : ℝ) ≤ 3)
          exact add_le_add le_rfl h3
        _ = 4 * x ^ δ := by ring
        _ ≤ 4 * x ^ (500 * δ) := by gcongr
    have hleft : x ^ δ + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤
        16 * x ^ (500 * δ) := by
      calc
        x ^ δ + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤
            4 * x ^ (500 * δ) + 2 * (k : ℝ) * (r : ℝ) :=
          by gcongr
        _ ≤ 4 * x ^ (500 * δ) + 12 * x ^ (500 * δ) :=
          by gcongr
        _ = 16 * x ^ (500 * δ) := by ring
    dsimp [w, wν, x]
    exact le_of_lt (lt_of_le_of_lt hleft (by simpa [x] using hgap16))
  have hεa : 100 * ε ≤ a := by
    dsimp [ε, a]
    rw [Real.rpow_neg hnpos.le, Real.rpow_neg hnpos.le]
    have hmul : 100 * x ^ δ ≤ x ^ η₀ := (hgap100).le
    have hdiv : 100 / x ^ η₀ ≤ 1 / x ^ δ :=
      (div_le_div_iff₀ (Real.rpow_pos_of_pos hnpos _)
        (Real.rpow_pos_of_pos hnpos _)).2 (by simpa using hmul)
    simpa [div_eq_mul_inv] using hdiv
  have ha : a ≤ 1 / 10 := by
    dsimp [a]
    rw [Real.rpow_neg hnpos.le]
    have hten : 10 ≤ x ^ δ := by simpa [Real.rpow_zero] using hgap10.le
    simpa [one_div] using
      (inv_le_inv₀ (Real.rpow_pos_of_pos hnpos _) (by norm_num)).2 hten
  have hlogR : Real.log ((r : ℝ) + 1) ≤ (r : ℝ) := by
    have hpos : 0 < (r : ℝ) + 1 := by positivity
    calc
      Real.log ((r : ℝ) + 1) ≤ ((r : ℝ) + 1) - 1 := Real.log_le_sub_one_of_pos hpos
      _ = (r : ℝ) := by ring
  have hlogCap : 3 * x ^ (200 * δ) ≤ x ^ (298 * δ) / 100 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2
    nlinarith [hgap300]
  have ha2 : a ^ 2 = x ^ (-2 * δ) := by
    dsimp [a]
    rw [pow_two, ← Real.rpow_add hnpos]
    congr 1
    ring
  have hpow298 : x ^ (-2 * δ) * x ^ (300 * δ) = x ^ (298 * δ) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have ha2k : x ^ (298 * δ) ≤ a ^ 2 * (k : ℝ) := by
    rw [ha2]
    calc
      x ^ (298 * δ) = x ^ (-2 * δ) * x ^ (300 * δ) := hpow298.symm
      _ ≤ x ^ (-2 * δ) * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hkLower (Real.rpow_nonneg hnpos.le _)
  have hlog : Real.log ((r : ℝ) + 1) ≤ a ^ 2 * (k : ℝ) / 100 := by
    calc
      Real.log ((r : ℝ) + 1) ≤ (r : ℝ) := hlogR
      _ ≤ 3 * x ^ (200 * δ) := hr
      _ ≤ x ^ (298 * δ) / 100 := hlogCap
      _ ≤ a ^ 2 * (k : ℝ) / 100 :=
        div_le_div_of_nonneg_right ha2k (by norm_num)
  exact ⟨by positivity, hεa, ha, hwidth, hlog⟩

/-- The exceptional-set estimate required by P10.1c also holds for the rounded
Section 10 block and list counts, eventually. -/
theorem p10_1k_fixedList_exceptional_premise_eventually (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      let r := p10_1kFixedListBlockCount n δ
      let k := p10_1kTupleListLength n δ
      let a := (n : ℝ) ^ (-δ)
      let w := (n : ℝ) ^ η₀
      let wμ := (n : ℝ) ^ δ
      ( (r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp (wμ - w) ≤
        Real.exp (-(a ^ 2 * (k : ℝ)) / 50) := by
  have hηδ : δ < η₀ / 2000 := by
    have hmin : min (min η₀ ζ) 1 ≤ η₀ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    exact lt_of_lt_of_le hδsmall
      (div_le_div_of_nonneg_right hmin (by norm_num))
  have hδη : δ < η₀ := by nlinarith [hηδ]
  have h298η : 298 * δ < η₀ := by nlinarith [hηδ]
  have hgap2000 := p10_1k_eventually_power_gap hδη (by norm_num : (0 : ℝ) < 2000)
  have hgap298 := p10_1k_eventually_power_gap h298η (by norm_num : (0 : ℝ) < 1)
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hgap2000, hgap298, hnlarge]
    with n hgap2000 hgap298 hn
  let x : ℝ := (n : ℝ)
  let r := p10_1kFixedListBlockCount n δ
  let k := p10_1kTupleListLength n δ
  let a : ℝ := x ^ (-δ)
  let w : ℝ := x ^ η₀
  let wμ : ℝ := x ^ δ
  have hnreal : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show (1 : ℕ) ≤ n by omega)
  have hnpos : 0 < x := lt_of_lt_of_le (by norm_num) hnreal
  have hround := p10_1kFixedListScale_rounding_bounds n δ hn hδ
  have hr : (r : ℝ) ≤ 3 * x ^ (200 * δ) := by
    simpa [r, x] using hround.2.2
  have hk : (k : ℝ) ≤ 2 * x ^ (300 * δ) := by
    simpa [k, x] using hround.2.1
  have hRplus : (r : ℝ) + 1 ≤ 4 * x ^ (200 * δ) := by
    have hpow : 1 ≤ x ^ (200 * δ) := by
      calc
        1 = x ^ (0 : ℝ) := by rw [Real.rpow_zero]
        _ ≤ x ^ (200 * δ) :=
          Real.rpow_le_rpow_of_exponent_le hnreal (by positivity)
    nlinarith [hr, hpow]
  have hpow500 : x ^ (200 * δ) * x ^ (500 * δ) = x ^ (700 * δ) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hkr : (k : ℝ) * (r : ℝ) ≤ 6 * x ^ (500 * δ) := by
    have hmul : (k : ℝ) * (r : ℝ) ≤
        (2 * x ^ (300 * δ)) * (3 * x ^ (200 * δ)) :=
      mul_le_mul hk hr (by positivity) (by positivity)
    have hpow : x ^ (300 * δ) * x ^ (200 * δ) = x ^ (500 * δ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    calc
      (k : ℝ) * (r : ℝ) ≤
          (2 * x ^ (300 * δ)) * (3 * x ^ (200 * δ)) := hmul
      _ = 6 * (x ^ (300 * δ) * x ^ (200 * δ)) := by ring
      _ = 6 * x ^ (500 * δ) := by rw [hpow]
  have hpoly : ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) ≤
      24 * x ^ (700 * δ) := by
    calc
      ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) =
          ((r : ℝ) + 1) * ((k : ℝ) * (r : ℝ)) := by ring
      _ ≤ (4 * x ^ (200 * δ)) * (6 * x ^ (500 * δ)) :=
        mul_le_mul hRplus hkr (by positivity) (by positivity)
      _ = 24 * (x ^ (200 * δ) * x ^ (500 * δ)) := by ring
      _ = 24 * x ^ (700 * δ) := by rw [hpow500]
  have ha2 : a ^ 2 = x ^ (-2 * δ) := by
    dsimp [a]
    rw [pow_two, ← Real.rpow_add hnpos]
    congr 1
    ring
  have hpow298 : x ^ (-2 * δ) * x ^ (300 * δ) = x ^ (298 * δ) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have ha2k : a ^ 2 * (k : ℝ) ≤ 2 * x ^ (298 * δ) := by
    rw [ha2]
    calc
      x ^ (-2 * δ) * (k : ℝ) ≤ x ^ (-2 * δ) * (2 * x ^ (300 * δ)) :=
        mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hnpos.le _)
      _ = 2 * x ^ (298 * δ) := by
        calc
          x ^ (-2 * δ) * (2 * x ^ (300 * δ)) =
              2 * (x ^ (-2 * δ) * x ^ (300 * δ)) := by ring
          _ = 2 * x ^ (298 * δ) := by rw [hpow298]
  have hlogNat : Real.log x ≤ x ^ δ / δ := by
    simpa [x] using Real.log_natCast_le_rpow_div n hδ
  have hlog700 : 700 * δ * Real.log x ≤ 700 * x ^ δ := by
    calc
      700 * δ * Real.log x ≤ 700 * δ * (x ^ δ / δ) :=
        mul_le_mul_of_nonneg_left hlogNat (by positivity)
      _ = 700 * x ^ δ := by field_simp [ne_of_gt hδ]
  have hlog24 : Real.log 24 ≤ 23 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 24)
    nlinarith
  have hδpow : 1 ≤ x ^ δ := by
    calc
      1 = x ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ x ^ δ := Real.rpow_le_rpow_of_exponent_le hnreal (by positivity)
  have hsmallδ : 724 * x ^ δ < x ^ η₀ / 2 := by
    nlinarith [hgap2000]
  have hsmall298 : x ^ (298 * δ) / 25 < x ^ η₀ / 2 := by
    nlinarith [hgap298]
  have hlogProduct :
      Real.log (24 * x ^ (700 * δ) * Real.exp (x ^ δ - x ^ η₀)) =
        Real.log 24 + 700 * δ * Real.log x + x ^ δ - x ^ η₀ := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by norm_num) (by positivity)]
    rw [Real.log_rpow hnpos, Real.log_exp]
    ring
  have hlogBound : Real.log (24 * x ^ (700 * δ) * Real.exp (x ^ δ - x ^ η₀)) ≤
      -x ^ (298 * δ) / 25 := by
    rw [hlogProduct]
    have hlog23 : Real.log 24 ≤ 23 * x ^ δ := by
      calc
        Real.log 24 ≤ 23 := hlog24
        _ ≤ 23 * x ^ δ := by
          simpa using mul_le_mul_of_nonneg_left hδpow (by norm_num : (0 : ℝ) ≤ 23)
    nlinarith [hlog23, hlog700, hsmallδ, hsmall298]
  have hexpBound : 24 * x ^ (700 * δ) * Real.exp (x ^ δ - x ^ η₀) ≤
      Real.exp (-x ^ (298 * δ) / 25) :=
    (Real.log_le_iff_le_exp (by positivity)).mp hlogBound
  change ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp (wμ - w) ≤
    Real.exp (-(a ^ 2 * (k : ℝ)) / 50)
  calc
    ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp (wμ - w) ≤
        24 * x ^ (700 * δ) * Real.exp (x ^ δ - x ^ η₀) := by
      dsimp [wμ, w]
      exact mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
    _ ≤ Real.exp (-x ^ (298 * δ) / 25) := hexpBound
    _ ≤ Real.exp (-(a ^ 2 * (k : ℝ)) / 50) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ha2k]

/-- The failure weight in P10.1c is the probability under the independent
tuple-array law. -/
theorem p10_1k_fixedListFailureWeight_eq_pr {N r k q : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N) (a : ℝ) :
    fixedListFailureWeight (N := N) (r := r) (k := k) (q := q) E G ρ D μ a =
      (p10_1kTupleArrayLaw (k := k) μ).pr
        (fixedListFailure (k := k) (q := q) E G ρ D μ a) := by
  classical
  unfold fixedListFailureWeight FinProb.pr
  simp_rw [p10_1kTupleArrayLaw_weight]

/-- Apply the repaired fixed-list test directly to the independent tuple-array
law used by the Section 10 experiment. -/
theorem p10_1k_fixedList_failure_probability_bound {N r k q : ℕ}
    (hfixed : P10_1cFixedListTest)
    (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (ν : Law N)
    (μ : Fin r → Law N) (w ε a wμ wν : ℝ)
    (hblocks : ∀ b, (μ b).SupportedIn X ∧ (μ b).WidthLE wμ)
    (hν : ν.WidthLE wν)
    (hD : ∀ j, (D j).SupportedIn Y)
    (haggregate : ∀ y, (∑ j, ρ.w j * (D j).w y) ≤ 4 * ν.w y)
    (hdisc : DiscOne E X Y w w ε)
    (hε : 0 ≤ ε) (hεa : 100 * ε ≤ a) (ha : a ≤ 1 / 10)
    (hwidth : wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤ w)
    (hlog : Real.log ((r : ℝ) + 1) ≤ a ^ 2 * (k : ℝ) / 100)
    (herror : ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp (wμ - w) ≤
      Real.exp (-(a ^ 2 * (k : ℝ)) / 50)) :
    ∃ c₅ : ℝ, 0 < c₅ ∧
      (p10_1kTupleArrayLaw (k := k) μ).pr
        (fixedListFailure E G ρ D μ a) ≤ Real.exp (-c₅ * a ^ 2 * (k : ℝ)) := by
  rcases hfixed with ⟨c₅, hc₅, htest⟩
  refine ⟨c₅, hc₅, ?_⟩
  rw [← p10_1k_fixedListFailureWeight_eq_pr E G ρ D μ a]
  exact htest N r k q E X Y G ρ D ν μ w ε a wμ wν
    hblocks hν hD haggregate hdisc hε hεa ha hwidth hlog herror

/-- Apply P10.1c to the tuple arrays on one finite scope of global
prospective IDs. -/
theorem p10_1kIdTupleArrayLaw_fixedListFailure_test_bound
    {N k q : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (hfixed : P10_1cFixedListTest)
    (μ : I → Law N) (S : Finset I) (r : ℕ)
    (e : Fin r ≃ {id // id ∈ S})
    (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (ν : Law N)
    (w ε a wμ wν : ℝ)
    (hblocks : ∀ b, (μ (e b).1).SupportedIn X ∧
      (μ (e b).1).WidthLE wμ)
    (hν : ν.WidthLE wν) (hD : ∀ j, (D j).SupportedIn Y)
    (haggregate : ∀ y, (∑ j, ρ.w j * (D j).w y) ≤ 4 * ν.w y)
    (hdisc : DiscOne E X Y w w ε)
    (hε : 0 ≤ ε) (hεa : 100 * ε ≤ a) (ha : a ≤ 1 / 10)
    (hwidth : wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤ w)
    (hlog : Real.log ((r : ℝ) + 1) ≤ a ^ 2 * (k : ℝ) / 100)
    (herror : ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp (wμ - w) ≤
      Real.exp (-(a ^ 2 * (k : ℝ)) / 50))
    (defaultTuple : Fin k → Fin N) :
    ∃ c₅ : ℝ, 0 < c₅ ∧
      (p10_1kIdTupleArrayLaw (k := k) μ).pr (fun W =>
        fixedListFailure (k := k) (q := q) E G ρ D
          (fun b => μ (e b).1) a (fun b i => W (e b).1 i)) ≤
        Real.exp (-c₅ * a ^ 2 * (k : ℝ)) := by
  let μblocks : Fin r → Law N := fun b => μ (e b).1
  obtain ⟨c₅, hc₅, hfail⟩ := p10_1k_fixedList_failure_probability_bound
    hfixed E X Y G ρ D ν μblocks w ε a wμ wν hblocks hν hD haggregate
      hdisc hε hεa ha hwidth hlog herror
  refine ⟨c₅, hc₅, ?_⟩
  exact p10_1kIdTupleArrayLaw_fixedListFailure_bound μ S r e E G ρ D a
    (Real.exp (-c₅ * a ^ 2 * (k : ℝ))) defaultTuple (by simpa [μblocks] using hfail)

/-- A selected PCluster patch supplies the laws, widths, supports, and
aggregate estimate needed for the fixed-list test with repeated first-side
samples from its first law. -/
theorem p10_1k_clusterData_fixedList_probability_bound {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ} {A B : Finset (Fin N)}
    (hfixed : P10_1cFixedListTest)
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (X Y : Finset (Fin N)) (hAX : A ⊆ X) (hBY : B ⊆ Y)
    (η₀ ε a : ℝ) (r k : ℕ)
    (hdisc : DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ε)
    (hε : 0 ≤ ε) (hεa : 100 * ε ≤ a) (ha : a ≤ 1 / 10)
    (hwidth : (n : ℝ) ^ δ + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤
      (n : ℝ) ^ η₀)
    (hlog : Real.log ((r : ℝ) + 1) ≤ a ^ 2 * (k : ℝ) / 100)
    (herror : ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) *
      Real.exp ((n : ℝ) ^ δ - (n : ℝ) ^ η₀) ≤
        Real.exp (-(a ^ 2 * (k : ℝ)) / 50)) :
    ∃ c₅ : ℝ, 0 < c₅ ∧
      (p10_1kTupleArrayLaw (k := k) (fun _ : Fin r => data.μ)).pr
        (fixedListFailure E G (p10_1kClusterPrior data) data.D
          (fun _ : Fin r => data.μ) a) ≤ Real.exp (-c₅ * a ^ 2 * (k : ℝ)) := by
  let μblocks : Fin r → Law N := fun _ => data.μ
  let ν : Law N := p10_1kClusterAggregate data
  have hblocks : ∀ b, (μblocks b).SupportedIn X ∧
      (μblocks b).WidthLE ((n : ℝ) ^ δ) := by
    intro b
    constructor
    · intro x hxX
      exact data.μ_supported x (by
        intro hxA
        exact hxX (hAX hxA))
    · exact data.μ_width
  have hν : ν.WidthLE ((n : ℝ) ^ δ) := by
    intro y
    simpa [ν, p10_1kClusterAggregate, p10_1kClusterPrior, Law.mix] using
      data.aggregate_width y
  have hD : ∀ j, (data.D j).SupportedIn Y := by
    intro j y hy
    exact data.D_supported j y (by
      intro hyB
      exact hy (hBY hyB))
  have haggregate : ∀ y, (∑ j, data.lam j * (data.D j).w y) ≤ 4 * ν.w y := by
    intro y
    have heq : (∑ j, data.lam j * (data.D j).w y) = ν.w y := by
      simp [ν, p10_1kClusterAggregate, p10_1kClusterPrior, Law.mix]
    rw [heq]
    nlinarith [ν.nonneg y]
  exact p10_1k_fixedList_failure_probability_bound hfixed E X Y G
    (p10_1kClusterPrior data) data.D ν μblocks
    ((n : ℝ) ^ η₀) ε a ((n : ℝ) ^ δ) ((n : ℝ) ^ δ)
    hblocks hν hD haggregate hdisc hε hεa ha hwidth hlog herror

/-- The repaired fixed-list test applies eventually to every available cluster
patch and every pair of supporting side sets satisfying the one-shot
discrepancy hypothesis. -/
theorem p10_1k_clusterData_fixedList_probability_eventually
    (hfixed : P10_1cFixedListTest) (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
        (X Y A B : Finset (Fin N))
        (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B),
        A ⊆ X → B ⊆ Y →
        DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
        ∃ c₅ : ℝ, 0 < c₅ ∧
          (p10_1kTupleArrayLaw
            (k := p10_1kTupleListLength n δ)
            (fun _ : Fin (p10_1kFixedListBlockCount n δ) => data.μ)).pr
            (fixedListFailure (k := p10_1kTupleListLength n δ)
              (q := data.K) E G (p10_1kClusterPrior data) data.D
              (fun _ : Fin (p10_1kFixedListBlockCount n δ) => data.μ)
              ((n : ℝ) ^ (-δ))) ≤
            Real.exp (-c₅ * ((n : ℝ) ^ (-δ)) ^ 2 *
              (p10_1kTupleListLength n δ : ℝ)) := by
  have hbasic := p10_1k_fixedList_basic_premises_eventually
    η₀ ζ δ hη₀ hζ hδ hδsmall
  have hexception := p10_1k_fixedList_exceptional_premise_eventually
    η₀ ζ δ hη₀ hζ hδ hδsmall
  filter_upwards [hbasic, hexception] with n hbasic hexception
  let r := p10_1kFixedListBlockCount n δ
  let k := p10_1kTupleListLength n δ
  let ε : ℝ := (n : ℝ) ^ (-η₀)
  let a : ℝ := (n : ℝ) ^ (-δ)
  let w : ℝ := (n : ℝ) ^ η₀
  let wμ : ℝ := (n : ℝ) ^ δ
  let wν : ℝ := (n : ℝ) ^ δ
  rcases hbasic with ⟨hε, hεa, ha, hwidth, hlog⟩
  have herror : (↑r + 1) * (↑k) * (↑r) * Real.exp (wμ - w) ≤
      Real.exp (-(a ^ 2 * ↑k) / 50) := by
    simpa [r, k, wμ, w, a, p10_1kFixedListBlockCount,
      p10_1kFixedListBlockCount, p10_1kTupleListLength] using hexception
  intro N E G X Y A B data hAX hBY hdisc
  simpa [r, k, ε, a, p10_1kFixedListBlockCount, p10_1kTupleListLength] using
    p10_1k_clusterData_fixedList_probability_bound hfixed data X Y hAX hBY
      η₀ ε a r k hdisc hε hεa ha hwidth hlog herror

/-- Every finite probability law has at least one positive-weight atom. -/
theorem p10_1k_FinProb_exists_pos {Ω : Type*} [Fintype Ω] (P : FinProb Ω) :
    ∃ ω, 0 < P.w ω := by
  by_contra h
  push_neg at h
  have hzero (ω : Ω) : P.w ω = 0 :=
    le_antisymm (h ω) (P.nonneg ω)
  have hsum := P.sum_eq_one
  simp [hzero] at hsum

/-- The probabilities of an event and its complement sum to one. -/
theorem p10_1k_FinProb_pr_not {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) : P.pr A + P.pr (fun ω => ¬ A ω) = 1 := by
  classical
  letI : DecidablePred A := fun ω => Classical.propDecidable (A ω)
  letI : DecidablePred (fun ω => ¬ A ω) :=
    fun ω => Classical.propDecidable (¬ A ω)
  unfold FinProb.pr
  calc
    (Finset.univ.sum fun ω : Ω => if A ω then P.w ω else 0) +
        (Finset.univ.sum fun ω : Ω => if ¬ A ω then P.w ω else 0) =
      Finset.univ.sum (fun ω : Ω =>
        (if A ω then P.w ω else 0) + (if ¬ A ω then P.w ω else 0)) := by
      rw [Finset.sum_add_distrib]
    _ = Finset.univ.sum (fun ω : Ω => P.w ω) := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : A ω <;> simp [h]
    _ = 1 := P.sum_eq_one

/-- Positive event probability supplies a positive-weight atom in that event. -/
theorem p10_1k_FinProb_exists_pos_of_pr_pos {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (hA : 0 < P.pr A) :
    ∃ ω, A ω ∧ 0 < P.w ω := by
  classical
  by_contra h
  push_neg at h
  have hprzero : P.pr A = 0 := by
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ω hω
    by_cases hAω : A ω
    · have hzero : P.w ω = 0 := le_antisymm (h ω hAω) (P.nonneg ω)
      simp [hAω, hzero]
    · simp [hAω]
  exact (ne_of_gt hA) hprzero

/-- A fixed-list failure bound below one yields a successful tuple array with
positive product weight. -/
theorem p10_1k_fixedList_successful_tuple_exists {N r k q : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N) (a ε : ℝ)
    (hfail : (p10_1kTupleArrayLaw (k := k) μ).pr
      (fixedListFailure (k := k) (q := q) E G ρ D μ a) ≤ ε) (hε : ε < 1) :
    ∃ W, ¬ fixedListFailure (k := k) (q := q) E G ρ D μ a W ∧
      0 < tupleArrayWeight μ W := by
  let P := p10_1kTupleArrayLaw (k := k) μ
  have hsuccess : 0 < P.pr
      (fun W => ¬ fixedListFailure (k := k) (q := q) E G ρ D μ a W) := by
    have hsum := p10_1k_FinProb_pr_not P
      (fixedListFailure (k := k) (q := q) E G ρ D μ a)
    dsimp [P] at hsum hfail
    linarith
  obtain ⟨W, hgood, hweight⟩ := p10_1k_FinProb_exists_pos_of_pr_pos P
    (fun W => ¬ fixedListFailure (k := k) (q := q) E G ρ D μ a W) hsuccess
  exact ⟨W, hgood, by
    simpa [P, p10_1kTupleArrayLaw_weight] using hweight⟩

/-- A successful fixed-list outcome supplies the absolute squared-mass bound
and the own/external deletion-ratio thresholds used by the cluster tilt. -/
theorem p10_1k_successfulFixedList_test_bounds {N r k q : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N)
    (gain : ℝ) (W : Fin r → Fin k → Fin N)
    (hgood : ¬ fixedListFailure (k := k) (q := q) E G ρ D μ gain W) :
    Real.exp (-2 * (k : ℝ) * (r : ℝ)) ≤
        squaredClusterMass ρ D (fixedListHitSet E G W) ∧
      (∀ b, FixedListOwnBlock E G ρ D (μ b) gain →
        Real.exp ((-Real.log 4 + (2 / 5 : ℝ) * gain) * (k : ℝ)) ≤
          squaredClusterMass ρ D (fixedListHitSet E G W) /
            squaredClusterMass ρ D
              (fixedListHitSetWithout E G W b)) ∧
      (∀ b, ¬ FixedListOwnBlock E G ρ D (μ b) gain →
        Real.exp (-2 * (k : ℝ)) ≤
          squaredClusterMass ρ D (fixedListHitSet E G W) /
            squaredClusterMass ρ D
              (fixedListHitSetWithout E G W b)) := by
  classical
  have habs : ¬ squaredClusterMass ρ D (fixedListHitSet E G W) <
      Real.exp (-2 * (k : ℝ) * (r : ℝ)) := by
    intro hlt
    apply hgood
    unfold fixedListFailure
    exact Or.inl hlt
  constructor
  · exact le_of_not_gt habs
  · constructor
    · intro b hown
      have hratio : ¬
          squaredClusterMass ρ D (fixedListHitSet E G W) /
            squaredClusterMass ρ D (fixedListHitSetWithout E G W b) <
              Real.exp ((-Real.log 4 + (2 / 5 : ℝ) * gain) * (k : ℝ)) := by
        intro hlt
        apply hgood
        unfold fixedListFailure
        exact Or.inr (Or.inl ⟨b, hown, hlt⟩)
      exact le_of_not_gt hratio
    · intro b hnotOwn
      have hratio : ¬
          squaredClusterMass ρ D (fixedListHitSet E G W) /
            squaredClusterMass ρ D (fixedListHitSetWithout E G W b) <
              Real.exp (-2 * (k : ℝ)) := by
        intro hlt
        apply hgood
        unfold fixedListFailure
        exact Or.inr (Or.inr ⟨b, hnotOwn, hlt⟩)
      exact le_of_not_gt hratio

/-- The full fixed-list hit set is contained in the set omitting any one
block's hit requirement. -/
theorem p10_1k_fixedListHitSet_subsetWithout {N r k : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (W : Fin r → Fin k → Fin N) (deleted : Fin r) :
    fixedListHitSet E G W ⊆ fixedListHitSetWithout E G W deleted := by
  classical
  intro y hy
  have hy' : ∀ b : Fin r, ∀ i : Fin k, Hits E G (W b i) y := by
    simpa [fixedListHitSet] using hy
  simp only [fixedListHitSetWithout, Finset.mem_filter, Finset.mem_univ,
    true_and]
  intro b hb i
  exact hy' b i

/-- Squared cluster mass is monotone under inclusion of its hit sets. -/
theorem p10_1k_squaredClusterMass_mono {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N)
    (F F' : Finset (Fin N)) (hFF' : F ⊆ F') :
    squaredClusterMass ρ D F ≤ squaredClusterMass ρ D F' := by
  classical
  unfold squaredClusterMass
  apply Finset.sum_le_sum
  intro j hj
  have hFnonneg : 0 ≤ lawMassOn (D j) F := by
    unfold lawMassOn
    apply Finset.sum_nonneg
    intro y hy
    exact (D j).nonneg y
  have hF'nonneg : 0 ≤ lawMassOn (D j) F' := by
    unfold lawMassOn
    apply Finset.sum_nonneg
    intro y hy
    exact (D j).nonneg y
  have hmassle : lawMassOn (D j) F ≤ lawMassOn (D j) F' := by
    unfold lawMassOn
    apply Finset.sum_le_sum_of_subset_of_nonneg hFF'
    intro y hy hnot
    exact (D j).nonneg y
  have hsq : (lawMassOn (D j) F) ^ 2 ≤ (lawMassOn (D j) F') ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hmassle)
      (add_nonneg hF'nonneg hFnonneg)
    nlinarith
  exact mul_le_mul_of_nonneg_left hsq (ρ.nonneg j)

/-- A successful fixed list retains at least half the squared-tilt cluster
prior after the absolute mass and all own/external deletion-ratio gates. -/
theorem p10_1k_successfulFixedList_retainedTilt_half_mass {N r k q : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N)
    (gain : ℝ) (W : Fin r → Fin k → Fin N)
    (hgood : ¬ fixedListFailure (k := k) (q := q) E G ρ D μ gain W)
    (hbudget :
      Real.exp (-((k : ℝ) * (r : ℝ))) + (r : ℝ) *
        (Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) +
          Real.exp (-((2 / 5 : ℝ) * (k : ℝ)))) ≤ 1 / 2) :
    ∃ hA : 0 < squaredClusterMass ρ D (fixedListHitSet E G W),
      (1 / 2 : ℝ) ≤ FinProb.pr
        (p10_1kSquaredTiltPrior ρ D (fixedListHitSet E G W) hA)
        (fun j => j ∈ p10_1kTiltGoodClusterSet
          (fun j => lawMassOn (D j) (fixedListHitSet E G W) <
            Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ))))
          (fun b j =>
            (FixedListOwnBlock E G ρ D (μ b) gain ∧
              lawMassOn (D j) (fixedListHitSet E G W) /
                lawMassOn (D j) (fixedListHitSetWithout E G W b) <
                  Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ))) ∨
            (¬ FixedListOwnBlock E G ρ D (μ b) gain ∧
              lawMassOn (D j) (fixedListHitSet E G W) /
                lawMassOn (D j) (fixedListHitSetWithout E G W b) <
                  Real.exp (-(6 / 5 : ℝ) * (k : ℝ))))) := by
  classical
  let F := fixedListHitSet E G W
  have htests := p10_1k_successfulFixedList_test_bounds E G ρ D μ gain W hgood
  have hA : 0 < squaredClusterMass ρ D F :=
    lt_of_lt_of_le (Real.exp_pos _) (by simpa [F] using htests.1)
  let P := p10_1kSquaredTiltPrior ρ D F hA
  let massBad : Fin q → Prop := fun j =>
    lawMassOn (D j) F < Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ)))
  let ratioBad : Fin r → Fin q → Prop := fun b j =>
    (FixedListOwnBlock E G ρ D (μ b) gain ∧
      lawMassOn (D j) F /
        lawMassOn (D j) (fixedListHitSetWithout E G W b) <
          Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ))) ∨
    (¬ FixedListOwnBlock E G ρ D (μ b) gain ∧
      lawMassOn (D j) F /
        lawMassOn (D j) (fixedListHitSetWithout E G W b) <
          Real.exp (-(6 / 5 : ℝ) * (k : ℝ)))
  have hmassTail : P.pr massBad ≤ Real.exp (-((k : ℝ) * (r : ℝ))) := by
    simpa [P, massBad, F] using
      p10_1kSquaredTiltPrior_absoluteMass_tail ρ D F hA k r
        (by simpa [F] using htests.1)
  have hratioTail : ∀ b, P.pr (ratioBad b) ≤
      Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) +
        Real.exp (-((2 / 5 : ℝ) * (k : ℝ))) := by
    intro b
    by_cases hown : FixedListOwnBlock E G ρ D (μ b) gain
    · have hratio :
          Real.exp ((-Real.log 4 + (2 / 5 : ℝ) * gain) * (k : ℝ)) ≤
            squaredClusterMass ρ D F /
              squaredClusterMass ρ D (fixedListHitSetWithout E G W b) := by
        simpa [F] using htests.2.1 b hown
      have hAminus : 0 < squaredClusterMass ρ D
          (fixedListHitSetWithout E G W b) := by
        apply lt_of_lt_of_le (Real.exp_pos _)
        exact le_trans (by simpa [F] using htests.1)
          (p10_1k_squaredClusterMass_mono ρ D F
            (fixedListHitSetWithout E G W b)
            (p10_1k_fixedListHitSet_subsetWithout E G W b))
      have htail := p10_1kSquaredTiltPrior_ownDeletion_tail ρ D F
        (fixedListHitSetWithout E G W b)
        (p10_1k_fixedListHitSet_subsetWithout E G W b) hA hAminus gain k hratio
      have hcase : P.pr (fun j =>
          lawMassOn (D j) F / lawMassOn (D j)
            (fixedListHitSetWithout E G W b) <
            Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ))) ≤
          Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) := by
        simpa [P, F] using htail
      have hsum : Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) ≤
          Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) +
            Real.exp (-((2 / 5 : ℝ) * (k : ℝ))) :=
        le_add_of_nonneg_right (Real.exp_nonneg _)
      simpa [ratioBad, hown] using le_trans hcase hsum
    · have hratio : Real.exp (-2 * (k : ℝ)) ≤
          squaredClusterMass ρ D F /
            squaredClusterMass ρ D (fixedListHitSetWithout E G W b) := by
        simpa [F] using htests.2.2 b hown
      have hAminus : 0 < squaredClusterMass ρ D
          (fixedListHitSetWithout E G W b) := by
        apply lt_of_lt_of_le (Real.exp_pos _)
        exact le_trans (by simpa [F] using htests.1)
          (p10_1k_squaredClusterMass_mono ρ D F
            (fixedListHitSetWithout E G W b)
            (p10_1k_fixedListHitSet_subsetWithout E G W b))
      have htail := p10_1kSquaredTiltPrior_externalDeletion_tail ρ D F
        (fixedListHitSetWithout E G W b)
        (p10_1k_fixedListHitSet_subsetWithout E G W b) hA hAminus k hratio
      have hcase : P.pr (fun j =>
          lawMassOn (D j) F / lawMassOn (D j)
            (fixedListHitSetWithout E G W b) <
            Real.exp (-(6 / 5 : ℝ) * (k : ℝ))) ≤
          Real.exp (-((2 / 5 : ℝ) * (k : ℝ))) := by
        simpa [P, F] using htail
      have hsum : Real.exp (-((2 / 5 : ℝ) * (k : ℝ))) ≤
          Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) +
            Real.exp (-((2 / 5 : ℝ) * (k : ℝ))) :=
        le_add_of_nonneg_left (Real.exp_nonneg _)
      simpa [ratioBad, hown] using le_trans hcase hsum
  have hretained := p10_1kTiltGoodClusterSet_mass_ge_half P massBad
    ratioBad (Real.exp (-((k : ℝ) * (r : ℝ))))
    (Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) +
      Real.exp (-((2 / 5 : ℝ) * (k : ℝ))))
    hmassTail hratioTail hbudget
  refine ⟨hA, ?_⟩
  simpa [P, massBad, ratioBad, F, p10_1kTiltGoodClusterSet] using hretained

/-- For the rounded Section 10 block and tuple counts, every successful fixed
list has a retained squared-tilt cluster set of mass at least one half once
the dimension is large enough. -/
theorem p10_1k_successfulFixedList_retainedTilt_half_mass_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (N q : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
        (ρ : FinProb (Fin q)) (D : Fin q → Law N)
        (μ : Fin (p10_1kFixedListBlockCount n δ) → Law N)
        (W : Fin (p10_1kFixedListBlockCount n δ) →
          Fin (p10_1kTupleListLength n δ) → Fin N),
        ¬ fixedListFailure (k := p10_1kTupleListLength n δ) (q := q)
          E G ρ D μ ((n : ℝ) ^ (-δ)) W →
        ∃ hA : 0 < squaredClusterMass ρ D (fixedListHitSet E G W),
          (1 / 2 : ℝ) ≤ FinProb.pr
            (p10_1kSquaredTiltPrior ρ D (fixedListHitSet E G W) hA)
            (fun j => j ∈ p10_1kTiltGoodClusterSet
              (fun j => lawMassOn (D j) (fixedListHitSet E G W) <
                Real.exp (-(3 / 2 : ℝ) *
                  (p10_1kTupleListLength n δ : ℝ) *
                  (p10_1kFixedListBlockCount n δ : ℝ)))
              (fun b j =>
                (FixedListOwnBlock E G ρ D (μ b) ((n : ℝ) ^ (-δ)) ∧
                  lawMassOn (D j) (fixedListHitSet E G W) /
                    lawMassOn (D j) (fixedListHitSetWithout E G W b) <
                      Real.exp ((-Real.log 2 + (2 / 25 : ℝ) *
                        ((n : ℝ) ^ (-δ))) *
                        (p10_1kTupleListLength n δ : ℝ))) ∨
                (¬ FixedListOwnBlock E G ρ D (μ b) ((n : ℝ) ^ (-δ)) ∧
                  lawMassOn (D j) (fixedListHitSet E G W) /
                  lawMassOn (D j) (fixedListHitSetWithout E G W b) <
                      Real.exp (-(6 / 5 : ℝ) *
                        (p10_1kTupleListLength n δ : ℝ))))) := by
  have hbudgetEvent := p10_1k_fixedList_retainedTilt_budget_eventually δ hδ
  filter_upwards [hbudgetEvent] with n hbudget
  intro N q E G ρ D μ W hgood
  have hbudget' :
      Real.exp (-((p10_1kTupleListLength n δ : ℝ) *
        (p10_1kFixedListBlockCount n δ : ℝ))) +
        (p10_1kFixedListBlockCount n δ : ℝ) *
          (Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (-δ) *
            (p10_1kTupleListLength n δ : ℝ))) +
           Real.exp (-((2 / 5 : ℝ) *
            (p10_1kTupleListLength n δ : ℝ)))) ≤ 1 / 2 := by
    simpa [p10_1kRetainedTiltBudget] using hbudget
  simpa [mul_assoc] using
    (p10_1k_successfulFixedList_retainedTilt_half_mass E G ρ D μ
      ((n : ℝ) ^ (-δ)) W hgood hbudget')

/-- A successful fixed-list outcome yields a retained squared-tilt label
marginal with the expected component atom cap. -/
theorem p10_1k_successfulFixedList_retainedLabelAtomCap {N q r k : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N)
    (gain : ℝ) (W : Fin r → Fin k → Fin N)
    (hgood : ¬ fixedListFailure (k := k) (q := q) E G ρ D μ gain W)
    (hbudget :
      Real.exp (-((k : ℝ) * (r : ℝ))) + (r : ℝ) *
        (Real.exp (-((6 / 25 : ℝ) * gain * (k : ℝ))) +
          Real.exp (-((2 / 5 : ℝ) * (k : ℝ)))) ≤ 1 / 2)
    (hN : 0 < N) (cap : ℝ) (hcap : 0 ≤ cap)
    (hAtom : ∀ j y, (D j).w y ≤ cap) :
    ∃ hA : 0 < squaredClusterMass ρ D (fixedListHitSet E G W),
      ∃ hR : (1 / 2 : ℝ) ≤ FinProb.pr
        (p10_1kSquaredTiltPrior ρ D (fixedListHitSet E G W) hA)
        (fun j => j ∈ p10_1kTiltGoodClusterSet
          (fun j => lawMassOn (D j) (fixedListHitSet E G W) <
            Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ))))
          (fun b j =>
            (FixedListOwnBlock E G ρ D (μ b) gain ∧
              lawMassOn (D j) (fixedListHitSet E G W) /
                lawMassOn (D j) (fixedListHitSetWithout E G W b) <
                  Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ))) ∨
            (¬ FixedListOwnBlock E G ρ D (μ b) gain ∧
              lawMassOn (D j) (fixedListHitSet E G W) /
                lawMassOn (D j) (fixedListHitSetWithout E G W b) <
                  Real.exp (-(6 / 5 : ℝ) * (k : ℝ))))) ,
      ∀ y, (p10_1kRetainedSquaredTiltLabelMarginal ρ D
        (fixedListHitSet E G W) hA hN
        (p10_1kTiltGoodClusterSet
          (fun j => lawMassOn (D j) (fixedListHitSet E G W) <
            Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ))))
          (fun b j =>
            (FixedListOwnBlock E G ρ D (μ b) gain ∧
              lawMassOn (D j) (fixedListHitSet E G W) /
                lawMassOn (D j) (fixedListHitSetWithout E G W b) <
                  Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ))) ∨
            (¬ FixedListOwnBlock E G ρ D (μ b) gain ∧
              lawMassOn (D j) (fixedListHitSet E G W) /
                lawMassOn (D j) (fixedListHitSetWithout E G W b) <
                  Real.exp (-(6 / 5 : ℝ) * (k : ℝ))))) hR).w y ≤
        2 * cap / squaredClusterMass ρ D (fixedListHitSet E G W) := by
  obtain ⟨hA, hR⟩ := p10_1k_successfulFixedList_retainedTilt_half_mass
    E G ρ D μ gain W hgood hbudget
  refine ⟨hA, hR, ?_⟩
  intro y
  exact p10_1kRetainedSquaredTiltLabelMarginal_atom_le
    ρ D (fixedListHitSet E G W) hA hN
    (p10_1kTiltGoodClusterSet
      (fun j => lawMassOn (D j) (fixedListHitSet E G W) <
        Real.exp (-(3 / 2 : ℝ) * ((k : ℝ) * (r : ℝ))))
      (fun b j =>
        (FixedListOwnBlock E G ρ D (μ b) gain ∧
          lawMassOn (D j) (fixedListHitSet E G W) /
            lawMassOn (D j) (fixedListHitSetWithout E G W b) <
              Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * (k : ℝ))) ∨
        (¬ FixedListOwnBlock E G ρ D (μ b) gain ∧
          lawMassOn (D j) (fixedListHitSet E G W) /
            lawMassOn (D j) (fixedListHitSetWithout E G W b) <
              Real.exp (-(6 / 5 : ℝ) * (k : ℝ)))))
    hR cap hcap hAtom y

/-- A lower bound on squared cluster mass forces one positive-prior cluster to
have at least the corresponding square-root mass. -/
theorem p10_1k_squaredMass_largeCluster {q N : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (t : ℝ) (ht : 0 < t)
    (hmass : t ^ 2 ≤ squaredClusterMass ρ D F) :
    ∃ j, 0 < ρ.w j ∧ t ≤ lawMassOn (D j) F := by
  classical
  let mass : Fin q → ℝ := fun j => lawMassOn (D j) F
  have hmassNonneg (j : Fin q) : 0 ≤ mass j := by
    dsimp [mass, lawMassOn]
    apply Finset.sum_nonneg
    intro y hy
    exact (D j).nonneg y
  by_contra h
  have hnot (j : Fin q) (hρ : 0 < ρ.w j) : mass j < t := by
    by_contra hge
    exact h ⟨j, hρ, le_of_not_gt hge⟩
  rcases p10_1k_FinProb_exists_pos ρ with ⟨j₀, hρ₀⟩
  have hterm_le (j : Fin q) : ρ.w j * mass j ^ 2 ≤ ρ.w j * t ^ 2 := by
    by_cases hρ : 0 < ρ.w j
    · have hmLt : mass j < t := hnot j hρ
      have hprod := mul_nonneg (sub_nonneg.mpr hmLt.le)
        (add_nonneg ht.le (hmassNonneg j))
      have hsquare : mass j ^ 2 ≤ t ^ 2 := by nlinarith [hprod]
      exact mul_le_mul_of_nonneg_left hsquare (ρ.nonneg j)
    · have hρzero : ρ.w j = 0 := le_antisymm (le_of_not_gt hρ) (ρ.nonneg j)
      simp [hρzero]
  have hterm_lt : ρ.w j₀ * mass j₀ ^ 2 < ρ.w j₀ * t ^ 2 := by
    have hmLt := hnot j₀ hρ₀
    have hprod := mul_pos (sub_pos.mpr hmLt)
      (add_pos_of_pos_of_nonneg ht (hmassNonneg j₀))
    have hsquare : mass j₀ ^ 2 < t ^ 2 := by
      nlinarith [hprod]
    exact mul_lt_mul_of_pos_left hsquare hρ₀
  have hsumlt :
      (∑ j : Fin q, ρ.w j * mass j ^ 2) <
        ∑ j : Fin q, ρ.w j * t ^ 2 := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact hterm_le j
    · exact ⟨j₀, Finset.mem_univ _, hterm_lt⟩
  have hsum_eq : (∑ j : Fin q, ρ.w j * t ^ 2) = t ^ 2 := by
    rw [← Finset.sum_mul, ρ.sum_eq_one]
    ring
  have hcontra : squaredClusterMass ρ D F < t ^ 2 := by
    calc
      squaredClusterMass ρ D F = ∑ j : Fin q, ρ.w j * mass j ^ 2 := by
        simp [squaredClusterMass, mass]
      _ < ∑ j : Fin q, ρ.w j * t ^ 2 := hsumlt
      _ = t ^ 2 := hsum_eq
  exact (not_lt_of_ge hmass) hcontra

/-- Positive-weight support of a law inside a finite set. -/
noncomputable def p10_1kPositiveLawSupport {N : ℕ} (μ : Law N)
    (F : Finset (Fin N)) : Finset (Fin N) := by
  classical
  exact F.filter fun y => 0 < μ.w y

/-- A uniform atom cap bounds the mass of a set by its positive support size
times that cap. -/
theorem p10_1k_lawMassOn_le_positiveSupportCard_mul_atom {N : ℕ}
    (μ : Law N) (F : Finset (Fin N)) (cap : ℝ)
    (hAtom : ∀ y, μ.w y ≤ cap) :
    lawMassOn μ F ≤ (p10_1kPositiveLawSupport μ F).card * cap := by
  classical
  have heq : lawMassOn μ F =
      ∑ y ∈ p10_1kPositiveLawSupport μ F, μ.w y := by
    unfold lawMassOn p10_1kPositiveLawSupport
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hpos : 0 < μ.w y
    · simp [hpos]
    · have hzero : μ.w y = 0 := le_antisymm (le_of_not_gt hpos) (μ.nonneg y)
      simp [hpos, hzero]
  have hsum :
      (∑ y ∈ p10_1kPositiveLawSupport μ F, μ.w y) ≤
        ∑ y ∈ p10_1kPositiveLawSupport μ F, cap := by
    apply Finset.sum_le_sum
    intro y hy
    exact hAtom y
  calc
    lawMassOn μ F = ∑ y ∈ p10_1kPositiveLawSupport μ F, μ.w y := heq
    _ ≤ ∑ y ∈ p10_1kPositiveLawSupport μ F, cap := hsum
    _ = (p10_1kPositiveLawSupport μ F).card * cap := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- A positive mass lower bound and an atom cap force a lower bound on the
number of supported labels. -/
theorem p10_1k_positiveSupport_card_ge {N : ℕ} (μ : Law N)
    (F : Finset (Fin N)) (t cap : ℝ) (hcap : 0 < cap)
    (hmass : t ≤ lawMassOn μ F) (hAtom : ∀ y, μ.w y ≤ cap) :
    t / cap ≤ (p10_1kPositiveLawSupport μ F).card := by
  have hmassCap := p10_1k_lawMassOn_le_positiveSupportCard_mul_atom μ F cap hAtom
  calc
    t / cap ≤ lawMassOn μ F / cap := div_le_div_of_nonneg_right hmass (le_of_lt hcap)
    _ ≤ (p10_1kPositiveLawSupport μ F).card := (div_le_iff₀ hcap).2 hmassCap

/-- Inject a finite coordinate set into a host-side subset with enough labels. -/
theorem p10_1k_injective_labels_of_card {N n : ℕ} (F : Finset (Fin N))
    (hcard : n ≤ F.card) :
    ∃ lab : Fin n → Fin N, Function.Injective lab ∧ ∀ i, lab i ∈ F := by
  classical
  let V := {y : Fin N // y ∈ F}
  have hcardV : n ≤ Fintype.card V := by
    simpa [V, Fintype.card_coe] using hcard
  let e : Fin n ↪ V :=
    (Fin.castLEEmb hcardV).trans (Fintype.equivFin V).symm.toEmbedding
  refine ⟨fun i => (e i).1, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    exact Subtype.ext hij
  · intro i
    exact (e i).2

/-- A successful fixed list has a positive-prior cluster whose hit-set mass is
at least `exp(-k*r)`. -/
theorem p10_1k_successfulFixedList_large_cluster_mass {N r k q : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N) (a : ℝ)
    (W : Fin r → Fin k → Fin N) (hgood : ¬ fixedListFailure E G ρ D μ a W) :
    ∃ j, 0 < ρ.w j ∧
      Real.exp (-((k : ℝ) * (r : ℝ))) ≤
        lawMassOn (D j) (fixedListHitSet E G W) := by
  have hnotMass : ¬ squaredClusterMass ρ D (fixedListHitSet E G W) <
      Real.exp (-2 * (k : ℝ) * (r : ℝ)) := by
    intro hmass
    apply hgood
    dsimp [fixedListFailure]
    exact Or.inl hmass
  have hmass : Real.exp (-2 * (k : ℝ) * (r : ℝ)) ≤
      squaredClusterMass ρ D (fixedListHitSet E G W) := le_of_not_gt hnotMass
  have htsq : (Real.exp (-((k : ℝ) * (r : ℝ)))) ^ 2 =
      Real.exp (-2 * (k : ℝ) * (r : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [← htsq] at hmass
  exact p10_1k_squaredMass_largeCluster ρ D (fixedListHitSet E G W)
    (Real.exp (-((k : ℝ) * (r : ℝ)))) (Real.exp_pos _) hmass

/-- Under the cluster atom bound, a successful fixed list provides at least `n`
distinct positive-mass labels in one cluster, provided its exponential mass
scale dominates `n`. -/
theorem p10_1k_successfulFixedList_large_hit_support {n N r k q : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (ζ : ℝ)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N) (a : ℝ)
    (W : Fin r → Fin k → Fin N) (hgood : ¬ fixedListFailure E G ρ D μ a W)
    (hAtom : ∀ j y, (D j).w y ≤ Real.exp (-((n : ℝ) ^ ζ)))
    (hExp : (n : ℝ) ≤ Real.exp ((n : ℝ) ^ ζ - (k : ℝ) * (r : ℝ))) :
    ∃ j, 0 < ρ.w j ∧
      n ≤ (p10_1kPositiveLawSupport (D j) (fixedListHitSet E G W)).card := by
  obtain ⟨j, hρj, hmass⟩ :=
    p10_1k_successfulFixedList_large_cluster_mass E G ρ D μ a W hgood
  have hcard := p10_1k_positiveSupport_card_ge (D j)
    (fixedListHitSet E G W) (Real.exp (-((k : ℝ) * (r : ℝ))))
    (Real.exp (-((n : ℝ) ^ ζ))) (Real.exp_pos _)
    hmass (hAtom j)
  have hratio :
      Real.exp (-((k : ℝ) * (r : ℝ))) / Real.exp (-((n : ℝ) ^ ζ)) =
        Real.exp ((n : ℝ) ^ ζ - (k : ℝ) * (r : ℝ)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hcardReal : (n : ℝ) ≤
      (p10_1kPositiveLawSupport (D j) (fixedListHitSet E G W)).card := by
    calc
      (n : ℝ) ≤ Real.exp ((n : ℝ) ^ ζ - (k : ℝ) * (r : ℝ)) := hExp
      _ = Real.exp (-((k : ℝ) * (r : ℝ))) /
            Real.exp (-((n : ℝ) ^ ζ)) := hratio.symm
      _ ≤ (p10_1kPositiveLawSupport (D j) (fixedListHitSet E G W)).card := hcard
  exact ⟨j, hρj, by exact_mod_cast hcardReal⟩

/-- A successful fixed list and the cluster atom bound give an injective list
of `n` second-side labels, each hitting all of the tuple entries. -/
theorem p10_1k_successfulFixedList_injective_labels {n N r k q : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (ζ : ℝ)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N) (a : ℝ)
    (W : Fin r → Fin k → Fin N) (hgood : ¬ fixedListFailure E G ρ D μ a W)
    (hAtom : ∀ j y, (D j).w y ≤ Real.exp (-((n : ℝ) ^ ζ)))
    (hExp : (n : ℝ) ≤ Real.exp ((n : ℝ) ^ ζ - (k : ℝ) * (r : ℝ))) :
    ∃ j, 0 < ρ.w j ∧
      ∃ lab : Fin n → Fin N,
        Function.Injective lab ∧
          (∀ i, 0 < (D j).w (lab i)) ∧
          (∀ i b t, Hits E G (W b t) (lab i)) := by
  classical
  obtain ⟨j, hρj, hcard⟩ :=
    p10_1k_successfulFixedList_large_hit_support E G ζ ρ D μ a W hgood hAtom hExp
  let F := fixedListHitSet E G W
  obtain ⟨lab, hinj, hlab⟩ :=
    p10_1k_injective_labels_of_card
      (p10_1kPositiveLawSupport (D j) F) hcard
  refine ⟨j, hρj, lab, hinj, ?_, ?_⟩
  · intro i
    have hmem : lab i ∈ F ∧ 0 < (D j).w (lab i) := by
      simpa [p10_1kPositiveLawSupport] using hlab i
    exact hmem.2
  · intro i b t
    have hmem : lab i ∈ F := Finset.filter_subset _ _ (hlab i)
    have hhit := (Finset.mem_filter.mp hmem).2
    simpa [F, fixedListHitSet] using hhit b t

/-- On a successful fixed list, the squared cluster mass of its hit set is
positive, and the squared-tilt law has a positive atom whose label hits every
entry of every block. -/
theorem p10_1k_successfulFixedList_has_tilted_hit {N r k q : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N) (a : ℝ)
    (W : Fin r → Fin k → Fin N) (hgood : ¬ fixedListFailure E G ρ D μ a W)
    (hN : 0 < N) :
    ∃ hA : 0 < squaredClusterMass ρ D (fixedListHitSet E G W),
      ∃ j y, (p10_1kSquaredTiltLabelLaw ρ D
        (fixedListHitSet E G W) hA hN).w (j, y) > 0 ∧
        ∀ b i, Hits E G (W b i) y := by
  have hnotMass : ¬ squaredClusterMass ρ D (fixedListHitSet E G W) <
      Real.exp (-2 * (k : ℝ) * (r : ℝ)) := by
    intro hmass
    apply hgood
    dsimp [fixedListFailure]
    exact Or.inl hmass
  have hmass : Real.exp (-2 * (k : ℝ) * (r : ℝ)) ≤
      squaredClusterMass ρ D (fixedListHitSet E G W) := le_of_not_gt hnotMass
  have hA : 0 < squaredClusterMass ρ D (fixedListHitSet E G W) :=
    lt_of_lt_of_le (Real.exp_pos _) hmass
  obtain ⟨z, hz⟩ := p10_1k_FinProb_exists_pos
    (p10_1kSquaredTiltLabelLaw ρ D (fixedListHitSet E G W) hA hN)
  rcases z with ⟨j, y⟩
  have hy := p10_1kSquaredTiltLabelLaw_support ρ D
    (fixedListHitSet E G W) hA hN j y (ne_of_gt hz)
  refine ⟨hA, j, y, hz, ?_⟩
  simpa [fixedListHitSet] using hy

/-- Unpack the chosen patch's cluster mixture and all its pointwise estimates. -/
theorem p10_1k_patchWitness_clusterData {n N : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (X Y RX RY : Finset (Fin N))
    (ζ δ : ℝ)
    (w : P10_1kPatchWitness (n := n) (N := N) E G X Y ζ δ RX RY) :
    Nonempty (P10_1kClusterData (n := n) (N := N) E G ζ δ w.A w.B) := by
  classical
  have hpatch := w.patch
  change ∃ (μ : Law N) (K : ℕ) (lam : Fin K → ℝ) (D : Fin K → Law N),
    μ.SupportedIn w.A ∧ (∀ j, (D j).SupportedIn w.B) ∧
    (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧
    μ.WidthLE ((n : ℝ) ^ δ) ∧
    (∀ y, ∑ j, lam j * (D j).w y ≤ Real.exp ((n : ℝ) ^ δ) / N) ∧
    (∀ j y, (D j).w y ≤ Real.exp (-((n : ℝ) ^ ζ))) ∧
    (∀ j, 0 < lam j → ∀ y y', 0 < (D j).w y → 0 < (D j).w y' →
      1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ y y') at hpatch
  rcases hpatch with
    ⟨μ, K, lam, D, hμ, hD, hlam, hlamsum, hμw, hagg, hatom, hcodeg⟩
  exact ⟨⟨μ, K, lam, D, hμ, hD, hlam, hlamsum, hμw, hagg, hatom, hcodeg⟩⟩

/-- Extract one available cluster patch outside prescribed bounded discards. -/
theorem p10_1k_patch_witness_of_available {n N : ℕ}
    (κ ζ δ : ℝ) (E : Fin N → Fin N → Prop) (G : Colour)
    (X Y RX RY : Finset (Fin N))
    (havail : AvailableAt κ (PCluster G ζ δ) n N E X Y)
    (hRX : (RX.card : ℝ) ≤ κ * (N : ℝ))
    (hRY : (RY.card : ℝ) ≤ κ * (N : ℝ)) :
    Nonempty (P10_1kPatchWitness (n := n) (N := N) E G X Y ζ δ RX RY) := by
  obtain ⟨A, B, hpatch, hA, hB⟩ := havail RX RY hRX hRY
  exact ⟨⟨A, B, hpatch, hA, hB⟩⟩

/-- Every bounded discard pair has a patch witness, so the available witnesses
form a nonempty finite tag menu. -/
theorem p10_1k_finite_patch_menu {n N : ℕ} (κ ζ δ : ℝ)
    (hκ : 0 < κ) (E : Fin N → Fin N → Prop) (G : Colour)
    (X Y : Finset (Fin N))
    (havail : AvailableAt κ (PCluster G ζ δ) n N E X Y) :
    Nonempty (P10_1kTagIndex N κ) ∧
      ∀ t : P10_1kTagIndex N κ,
        Nonempty (P10_1kPatchWitness (n := n) (N := N) E G X Y ζ δ
          t.1.1 t.1.2) := by
  classical
  constructor
  · refine ⟨⟨(∅, ∅), ?_⟩⟩
    simp [mul_nonneg hκ.le (Nat.cast_nonneg N)]
  · intro t
    exact p10_1k_patch_witness_of_available κ ζ δ E G X Y t.1.1 t.1.2 havail
      t.2.1 t.2.2

/-- A fixed witness choice for every tag in the finite available-patch menu. -/
noncomputable def p10_1kChoosePatchMenu {n N : ℕ}
    (κ ζ δ : ℝ) (E : Fin N → Fin N → Prop) (G : Colour)
    (X Y : Finset (Fin N))
    (havail : AvailableAt κ (PCluster G ζ δ) n N E X Y) :
    (t : P10_1kTagIndex N κ) →
      P10_1kPatchWitness (n := n) (N := N) E G X Y ζ δ t.1.1 t.1.2 := by
  classical
  intro t
  exact Classical.choice (p10_1k_patch_witness_of_available κ ζ δ E G X Y
    t.1.1 t.1.2 havail t.2.1 t.2.2)

/-- Choose all cluster data in the finite patch menu once and for all. -/
noncomputable def p10_1kChooseClusterMenu {n N : ℕ}
    (κ ζ δ : ℝ) (E : Fin N → Fin N → Prop) (G : Colour)
    (X Y : Finset (Fin N))
    (havail : AvailableAt κ (PCluster G ζ δ) n N E X Y) :
    (t : P10_1kTagIndex N κ) →
      P10_1kClusterData (n := n) (N := N) E G ζ δ
        (p10_1kChoosePatchMenu κ ζ δ E G X Y havail t).A
        (p10_1kChoosePatchMenu κ ζ δ E G X Y havail t).B := by
  classical
  intro t
  exact Classical.choice (p10_1k_patchWitness_clusterData E G X Y
    t.1.1 t.1.2 ζ δ (p10_1kChoosePatchMenu κ ζ δ E G X Y havail t))

/-- The residual coordinates, split into chunks whose sizes are the powers of two
in the binary expansion of `d`. -/
abbrev P10_1kChunkGroup (d : ℕ) (i : Fin d.bitIndices.length) :=
  Fin (d.bitIndices.get i) → ZMod 2

abbrev P10_1kChunkCoordinate (d : ℕ) :=
  Σ i : Fin d.bitIndices.length, P10_1kChunkGroup d i

abbrev P10_1kChunkWord (d : ℕ) :=
  ∀ i : Fin d.bitIndices.length, P10_1kChunkGroup d i → Bool

/-- Each chunk index group is an elementary abelian 2-group. -/
theorem p10_1k_chunkGroup_two_add (d : ℕ) (i : Fin d.bitIndices.length)
    (g : P10_1kChunkGroup d i) : g + g = 0 := by
  funext j
  have hchar (x : ZMod 2) : x + x = 0 := by
    fin_cases x <;> decide
  exact hchar (g j)

/-- The binary chunk coordinate type has exactly `d` positions. -/
theorem p10_1k_chunkCoordinate_card (d : ℕ) :
    Fintype.card (P10_1kChunkCoordinate d) = d := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ i : Fin d.bitIndices.length, Fintype.card (P10_1kChunkGroup d i)) =
        ∑ i : Fin d.bitIndices.length, 2 ^ d.bitIndices.get i := by simp
    _ = (d.bitIndices.map (fun i => 2 ^ i)).sum := by
      simp
    _ = d := Nat.sum_map_two_pow_bitIndices d

/-- The coordinate equivalence induced by the binary chunk decomposition. -/
noncomputable def p10_1k_chunkCoordinateEquiv (d : ℕ) :
    Fin d ≃ P10_1kChunkCoordinate d := by
  let h := p10_1k_chunkCoordinate_card d
  exact (finCongr h.symm).trans
    (Fintype.equivFin (P10_1kChunkCoordinate d)).symm

/-- Reindex a cube word by the binary chunks of its coordinate dimension. -/
noncomputable def p10_1k_chunkWordEquiv (d : ℕ) :
    (Fin d → Bool) ≃ (P10_1kChunkCoordinate d → Bool) :=
  Equiv.arrowCongr (p10_1k_chunkCoordinateEquiv d) (Equiv.refl Bool)

/-- Convert a function on chunk coordinates into a dependent family of chunk words. -/
noncomputable def p10_1kChunkCoordinateToFamilyEquiv (d : ℕ) :
    (P10_1kChunkCoordinate d → Bool) ≃ P10_1kChunkWord d where
  toFun f i g := f ⟨i, g⟩
  invFun W p := W p.1 p.2
  left_inv f := by funext p; cases p; rfl
  right_inv W := by funext i g; rfl

/-- Reindex a residual cube word as a dependent family of binary chunk words. -/
noncomputable def p10_1kChunkFamilyEquiv (d : ℕ) :
    (Fin d → Bool) ≃ P10_1kChunkWord d :=
  (p10_1k_chunkWordEquiv d).trans (p10_1kChunkCoordinateToFamilyEquiv d)

/-- A residual word viewed as a dependent family of chunk words. -/
noncomputable def p10_1k_chunkedWord (d : ℕ) (s : Fin d → Bool) :
    ∀ i : Fin d.bitIndices.length, P10_1kChunkGroup d i → Bool :=
  fun i g => p10_1k_chunkWordEquiv d s ⟨i, g⟩

/-- The explicit chunked word is the family-equivalence image of the residual word. -/
theorem p10_1k_chunkedWord_eq_familyEquiv (d : ℕ) (s : Fin d → Bool) :
    p10_1k_chunkedWord d s = p10_1kChunkFamilyEquiv d s := by
  funext i g
  rfl

/-- Flip one residual coordinate. -/
def p10_1kFlipCoordinate {d : ℕ} (s : Fin d → Bool) (j : Fin d) : Fin d → Bool :=
  fun k => if k = j then !s k else s k

/-- Flipping a single Boolean coordinate has Hamming distance one. -/
theorem p10_1kFlipCoordinate_hammingDist (d : ℕ) (s : Fin d → Bool) (j : Fin d) :
    hammingDist s (p10_1kFlipCoordinate s j) = 1 := by
  have hset : Finset.univ.filter (fun k : Fin d =>
      s k ≠ p10_1kFlipCoordinate s j k) = {j} := by
    ext k
    simp [p10_1kFlipCoordinate]
  simp [hammingDist, hset]

/-- A residual coordinate flip changes exactly its corresponding chunk bit. -/
theorem p10_1k_chunkedWord_flipCoordinate (d : ℕ) (s : Fin d → Bool)
    (j : Fin d) (i : Fin d.bitIndices.length) (g : P10_1kChunkGroup d i) :
    p10_1k_chunkedWord d (p10_1kFlipCoordinate s j) i g =
      if (p10_1k_chunkCoordinateEquiv d).symm ⟨i, g⟩ = j then
        !p10_1k_chunkedWord d s i g else p10_1k_chunkedWord d s i g := by
  simp [p10_1k_chunkedWord, p10_1k_chunkWordEquiv,
    p10_1kFlipCoordinate]

/-- A residual coordinate flip toggles one bit in its containing chunk. -/
theorem p10_1k_chunkedWord_flip_changed (d : ℕ) (s : Fin d → Bool) (j : Fin d) :
    p10_1k_chunkedWord d (p10_1kFlipCoordinate s j)
        (p10_1k_chunkCoordinateEquiv d j).1 =
      flipChunkBit (p10_1k_chunkedWord d s
        (p10_1k_chunkCoordinateEquiv d j).1)
        (p10_1k_chunkCoordinateEquiv d j).2 := by
  let e := p10_1k_chunkCoordinateEquiv d
  have hcoord (g : P10_1kChunkGroup d (e j).1) :
      e.symm ⟨(e j).1, g⟩ = j ↔ g = (e j).2 := by
    rw [Equiv.symm_apply_eq]
    change (Sigma.mk (e j).1 g = e j) ↔ g = (e j).2
    rw [Sigma.mk.inj_iff]
    simp
  funext g
  simp [p10_1k_chunkedWord_flipCoordinate, hcoord, e, flipChunkBit]

/-- Every other chunk is unchanged by a residual coordinate flip. -/
theorem p10_1k_chunkedWord_flip_unchanged (d : ℕ) (s : Fin d → Bool) (j : Fin d)
    (i : Fin d.bitIndices.length) (hi : i ≠ (p10_1k_chunkCoordinateEquiv d j).1) :
    p10_1k_chunkedWord d (p10_1kFlipCoordinate s j) i =
      p10_1k_chunkedWord d s i := by
  let p := p10_1k_chunkCoordinateEquiv d j
  funext g
  have hcoord : (p10_1k_chunkCoordinateEquiv d).symm ⟨i, g⟩ ≠ j := by
    intro h
    have hp : (⟨i, g⟩ : P10_1kChunkCoordinate d) = p10_1k_chunkCoordinateEquiv d j :=
      (Equiv.symm_apply_eq _).mp h
    exact hi (congrArg Sigma.fst hp)
  simp [p10_1k_chunkedWord_flipCoordinate, hcoord]

/-- Two different one-bit flips of a word differ in exactly two coordinates. -/
theorem p10_1k_chunkHammingDist_two_flips {G : Type} [Fintype G] [DecidableEq G]
    (s : G → Bool) (a b : G) :
    chunkHammingDistance (flipChunkBit s a) (flipChunkBit s b) = 0 ∨
      chunkHammingDistance (flipChunkBit s a) (flipChunkBit s b) = 2 := by
  by_cases hab : a = b
  · subst b
    left
    simp [chunkHammingDistance]
  · right
    have hba : b ≠ a := fun h => hab h.symm
    have hset :
        (Finset.univ.filter fun x : G =>
          flipChunkBit s a x ≠ flipChunkBit s b x) = {a, b} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hne
        by_contra hnot
        have hxa : x ≠ a := fun hxa => hnot (Or.inl hxa)
        have hxb : x ≠ b := fun hxb => hnot (Or.inr hxb)
        simp [flipChunkBit, hxa, hxb] at hne
      · intro hx
        rcases hx with hx | hx
        · subst x
          simp [flipChunkBit, hab]
        · subst x
          simp [flipChunkBit, hba]
    simp [chunkHammingDistance, hset, hab]

/-- A projected neighbor never equals the projection of its center: it is a
one-bit neighbor of a different one-bit neighbor. -/
theorem p10_1k_projectedNeighbor_ne_projectedCenter
    {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (h₂ : ∀ g : G, g + g = 0) (s : G → Bool) (g : G) :
    projectedNeighbor s g ≠ chunkProject s := by
  intro heq
  have hproj := (p10_1a_hamming_projection (G := G) h₂).1 (flipChunkBit s g)
  have hone : chunkHammingDistance (flipChunkBit s g)
      (chunkProject (flipChunkBit s g)) = 1 := hproj.2
  have heq' : chunkProject (flipChunkBit s g) = chunkProject s := by
    simpa [projectedNeighbor] using heq
  rw [heq'] at hone
  have hpair := p10_1k_chunkHammingDist_two_flips s g (chunkSyndrome s)
  have hpair' : chunkHammingDistance (flipChunkBit s g) (chunkProject s) = 0 ∨
      chunkHammingDistance (flipChunkBit s g) (chunkProject s) = 2 := by
    simpa [chunkProject] using hpair
  omega

/-- In one chunk, every nonempty projected-neighbor fiber has size the whole
chunk when the syndrome is zero, and size two otherwise. -/
theorem p10_1k_local_projectedNeighbor_fiber_card
    {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (h₂ : ∀ g : G, g + g = 0) (s t : G → Bool)
    (hne : ∃ g, projectedNeighbor s g = t) :
    Fintype.card {g : G // projectedNeighbor s g = t} =
      if chunkSyndrome s = 0 then Fintype.card G else 2 := by
  classical
  have hmult := p10_1a_neighbour_multiplicities h₂ s t
  have hcard : Fintype.card {g : G // projectedNeighbor s g = t} =
      projectedNeighborMultiplicity s t := by
    let F := projectedNeighborFiber s t
    let e : {g : G // projectedNeighbor s g = t} ≃ {g : G // g ∈ F} := {
      toFun := fun g => ⟨g.1, by
        change g.1 ∈ Finset.univ.filter (fun l => projectedNeighbor s l = t)
        simp [g.2]⟩
      invFun := fun g => ⟨g.1, by
        have hg : g.1 ∈ Finset.univ.filter
            (fun l => projectedNeighbor s l = t) := by
          simpa [F, projectedNeighborFiber] using g.2
        exact (Finset.mem_filter.mp hg).2⟩
      left_inv := by intro g; apply Subtype.ext; rfl
      right_inv := by intro g; apply Subtype.ext; rfl }
    calc
      Fintype.card {g : G // projectedNeighbor s g = t} =
          Fintype.card {g : G // g ∈ F} :=
        Fintype.card_congr e
      _ = F.card := Fintype.card_coe F
      _ = projectedNeighborMultiplicity s t := by rfl
  have hnon : projectedNeighborMultiplicity s t ≠ 0 := by
    intro hzero
    obtain ⟨g, hg⟩ := hne
    have hmem : g ∈ Finset.univ.filter (fun l => projectedNeighbor s l = t) := by
      simp [hg]
    have hpos : 0 < (Finset.univ.filter
        (fun l => projectedNeighbor s l = t)).card :=
      Finset.card_pos.mpr ⟨g, hmem⟩
    unfold projectedNeighborMultiplicity projectedNeighborFiber at hzero
    rw [hzero] at hpos
    omega
  rcases hmult with hzero | hrest
  · exact (hnon hzero).elim
  · rcases hrest with hcenter | hnoncenter
    · rw [hcard, if_pos hcenter.1]
      exact hcenter.2
    · rw [hcard, if_neg hnoncenter.1]
      exact hnoncenter.2

/-- First-side labels that hit an entire finite list of second-side labels. -/
noncomputable def p10_1kCommonNeighborSet {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (y : ι → Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun x => ∀ i, Hits E G x (y i)

/-- A positive-mass atom that hits every label gives positive mass to the
star's full common-neighbor set. -/
theorem p10_1kCommonNeighborSet_mass_pos_of_atom {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (μ : Law N) (y : ι → Fin N)
    (x : Fin N) (hx : 0 < μ.w x) (hhit : ∀ i, Hits E G x (y i)) :
    0 < lawMassOn μ (p10_1kCommonNeighborSet E G y) := by
  classical
  have hmem : x ∈ p10_1kCommonNeighborSet E G y := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hhit⟩
  have hle : μ.w x ≤ lawMassOn μ (p10_1kCommonNeighborSet E G y) := by
    unfold lawMassOn
    exact Finset.single_le_sum (fun z hz => μ.nonneg z) hmem
  exact lt_of_lt_of_le hx hle

/-- If one tuple sample has positive mass and hits every label in a star, then
the common-neighbor set of that star has positive mass. -/
theorem p10_1kCommonNeighborSet_mass_pos_of_tuple {N r k : ℕ}
    {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (μ : Fin r → Law N)
    (W : Fin r → Fin k → Fin N) (b : Fin r) (i : Fin k)
    (y : ι → Fin N) (hweight : 0 < (μ b).w (W b i))
    (hhit : ∀ j, Hits E G (W b i) (y j)) :
    0 < lawMassOn (μ b) (p10_1kCommonNeighborSet E G y) := by
  classical
  have hmem : W b i ∈ p10_1kCommonNeighborSet E G y := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact hhit
  have hle : (μ b).w (W b i) ≤
      lawMassOn (μ b) (p10_1kCommonNeighborSet E G y) := by
    unfold lawMassOn
    exact Finset.single_le_sum (fun x hx => (μ b).nonneg x) hmem
  exact lt_of_lt_of_le hweight hle

/-- Conditioning a first-side law on a positive-mass common-neighbor set gives
a probability row supported on every required edge. -/
theorem p10_1k_restrict_commonNeighborLaw {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (y : ι → Fin N) (μ : Law N)
    (hpos : 0 < lawMassOn μ (p10_1kCommonNeighborSet E G y)) :
    ∀ x, (Law.restrict μ (p10_1kCommonNeighborSet E G y) hpos).w x ≠ 0 →
      ∀ i, Hits E G x (y i) := by
  classical
  intro x hx i
  have hxmem : x ∈ p10_1kCommonNeighborSet E G y := by
    by_contra hnot
    simp [Law.restrict, hnot] at hx
  exact (Finset.mem_filter.mp hxmem).2 i

/-- A subprobability row obtained by conditioning a first-side law on all
labels in a finite star; when the common-neighbor mass is zero, use the zero
row. -/
noncomputable def p10_1kCommonNeighborSubrow {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (y : ι → Fin N) (μ : Law N) :
    Fin N → ℝ := by
  classical
  exact if h : 0 < lawMassOn μ (p10_1kCommonNeighborSet E G y) then
    (Law.restrict μ (p10_1kCommonNeighborSet E G y) h).w else fun _ => 0

/-- The common-neighbor subrow is nonnegative and supported on every required
edge. -/
theorem p10_1kCommonNeighborSubrow_support {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (y : ι → Fin N) (μ : Law N) :
    (∀ x, 0 ≤ p10_1kCommonNeighborSubrow E G y μ x) ∧
    (∀ x, p10_1kCommonNeighborSubrow E G y μ x ≠ 0 → ∀ i, Hits E G x (y i)) := by
  classical
  constructor
  · intro x
    by_cases h : 0 < lawMassOn μ (p10_1kCommonNeighborSet E G y)
    · simp [p10_1kCommonNeighborSubrow, h, (Law.restrict μ _ h).nonneg x]
    · simp [p10_1kCommonNeighborSubrow, h]
  · intro x hx i
    by_cases h : 0 < lawMassOn μ (p10_1kCommonNeighborSet E G y)
    · have hx' : (Law.restrict μ (p10_1kCommonNeighborSet E G y) h).w x ≠ 0 := by
        simpa [p10_1kCommonNeighborSubrow, h] using hx
      exact p10_1k_restrict_commonNeighborLaw E G y μ h x hx' i
    · simp [p10_1kCommonNeighborSubrow, h] at hx

/-- The common-neighbor subrow has mass one exactly when the common-neighbor
set has positive mass, and zero otherwise. -/
theorem p10_1kCommonNeighborSubrow_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (y : ι → Fin N) (μ : Law N) :
    ∑ x, p10_1kCommonNeighborSubrow E G y μ x =
      if 0 < lawMassOn μ (p10_1kCommonNeighborSet E G y) then 1 else 0 := by
  classical
  by_cases h : 0 < lawMassOn μ (p10_1kCommonNeighborSet E G y)
  · simp [p10_1kCommonNeighborSubrow, h, (Law.restrict μ _ h).sum_eq_one]
  · simp [p10_1kCommonNeighborSubrow, h]

/-- A positive-mass tuple sample that hits every assigned label yields a
normalized even-row subrow supported on every star edge. -/
theorem p10_1k_tupleSample_subrow {N r k : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (μ : Fin r → Law N)
    (W : Fin r → Fin k → Fin N) (b : Fin r) (i : Fin k)
    (y : ι → Fin N) (hweight : 0 < (μ b).w (W b i))
    (hhit : ∀ j, Hits E G (W b i) (y j)) :
    (∀ x, 0 ≤ p10_1kCommonNeighborSubrow E G y (μ b) x) ∧
      (∑ x, p10_1kCommonNeighborSubrow E G y (μ b) x = 1) ∧
      (∀ x, p10_1kCommonNeighborSubrow E G y (μ b) x ≠ 0 →
        ∀ j, Hits E G x (y j)) := by
  have hmass := p10_1kCommonNeighborSet_mass_pos_of_tuple
    E G μ W b i y hweight hhit
  have hsupport := p10_1kCommonNeighborSubrow_support E G y (μ b)
  have hsum := p10_1kCommonNeighborSubrow_sum E G y (μ b)
  refine ⟨hsupport.1, ?_, hsupport.2⟩
  simpa [hmass] using hsum

/-- Conditioning a law on a set of mass at least one half costs at most a
factor two in every atom. -/
theorem p10_1k_restrict_atom_le_two {N : ℕ} (μ : Law N) (F : Finset (Fin N))
    (hMass : (1 / 2 : ℝ) ≤ lawMassOn μ F) (y : Fin N) :
    (Law.restrict μ F (lt_of_lt_of_le (by norm_num) hMass)).w y ≤ 2 * μ.w y := by
  classical
  by_cases hy : y ∈ F
  · simp only [Law.restrict, hy]
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hMass)).2
    nlinarith [μ.nonneg y]
  · simp [Law.restrict, hy, μ.nonneg y]

/-- Conditioning on a set of mass at least `exp (-L)` increases each atom by
at most `exp L`. -/
theorem p10_1k_restrict_atom_le_of_mass_lower {N : ℕ}
    (μ : Law N) (F : Finset (Fin N)) (L : ℝ)
    (hMass : Real.exp (-L) ≤ lawMassOn μ F) (y : Fin N) :
    (Law.restrict μ F
      (lt_of_lt_of_le (Real.exp_pos _) hMass)).w y ≤ Real.exp L * μ.w y := by
  classical
  have hmassPos : 0 < lawMassOn μ F :=
    lt_of_lt_of_le (Real.exp_pos _) hMass
  by_cases hy : y ∈ F
  · simp only [Law.restrict, hy]
    have hrecip : 1 / lawMassOn μ F ≤ Real.exp L := by
      apply (div_le_iff₀ hmassPos).2
      calc
        1 = Real.exp (-L) * Real.exp L := by
          rw [← Real.exp_add]
          simp
        _ ≤ lawMassOn μ F * Real.exp L :=
          mul_le_mul_of_nonneg_right hMass (Real.exp_nonneg _)
        _ = Real.exp L * lawMassOn μ F := by ring
    calc
      (μ.w y) / lawMassOn μ F = μ.w y * (1 / lawMassOn μ F) := by ring
      _ ≤ μ.w y * Real.exp L :=
        mul_le_mul_of_nonneg_left hrecip (μ.nonneg y)
      _ = Real.exp L * μ.w y := by ring
  · simp only [Law.restrict, hy]
    exact mul_nonneg (Real.exp_nonneg _) (μ.nonneg y)

/-- A cluster conditioned on a finite mask; zero-mass masks use a default law. -/
noncomputable def p10_1kMaskClusterLaw {N q : ℕ} (D : Fin q → Law N)
    (F : Finset (Fin N)) (y₀ : Fin N) (j : Fin q) : Law N :=
  if hmass : 0 < lawMassOn (D j) F then
    Law.restrict (D j) F hmass
  else Law.dirac y₀

/-- A masked cluster stays on the original second-side support when the
fallback label is chosen from that support. -/
theorem p10_1kMaskClusterLaw_supportedIn {N q : ℕ}
    (D : Fin q → Law N) (F B : Finset (Fin N)) (y₀ : Fin N)
    (hD : ∀ j, (D j).SupportedIn B) (hy₀ : y₀ ∈ B) (j : Fin q) :
    (p10_1kMaskClusterLaw D F y₀ j).SupportedIn B := by
  classical
  intro y hy
  by_cases hmass : 0 < lawMassOn (D j) F
  · simp [p10_1kMaskClusterLaw, hmass, Law.restrict, hD j y hy]
  · have hne : y ≠ y₀ := by
      intro heq
      subst y
      exact hy hy₀
    simp [p10_1kMaskClusterLaw, hmass, Law.dirac, hne]

/-- After masking a PCluster component and imposing a successful-list mass
lower bound, each restricted label atom is exponentially small. -/
theorem p10_1k_maskedCluster_restrict_atom_le {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ}
    {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (Fmask Fhit : Finset (Fin N)) (y₀ : Fin N) (j : Fin data.K)
    (L : ℝ)
    (hmask : (1 / 2 : ℝ) ≤ lawMassOn (data.D j) Fmask)
    (hhit : Real.exp (-L) ≤ lawMassOn
      (p10_1kMaskClusterLaw data.D Fmask y₀ j) Fhit) :
    ∀ y, (Law.restrict (p10_1kMaskClusterLaw data.D Fmask y₀ j) Fhit
      (lt_of_lt_of_le (Real.exp_pos _) hhit)).w y ≤
        2 * Real.exp (L - (n : ℝ) ^ ζ) := by
  classical
  have hmaskPos : 0 < lawMassOn (data.D j) Fmask :=
    lt_of_lt_of_le (by norm_num) hmask
  have hmaskAtom : ∀ y,
      (p10_1kMaskClusterLaw data.D Fmask y₀ j).w y ≤ 2 * (data.D j).w y := by
    intro y
    rw [p10_1kMaskClusterLaw, dif_pos hmaskPos]
    exact p10_1k_restrict_atom_le_two (data.D j) Fmask hmask y
  have hhitPos : 0 < lawMassOn
      (p10_1kMaskClusterLaw data.D Fmask y₀ j) Fhit :=
    lt_of_lt_of_le (Real.exp_pos _) hhit
  intro y
  calc
    (Law.restrict (p10_1kMaskClusterLaw data.D Fmask y₀ j) Fhit hhitPos).w y ≤
        Real.exp L * (p10_1kMaskClusterLaw data.D Fmask y₀ j).w y :=
      p10_1k_restrict_atom_le_of_mass_lower
        (p10_1kMaskClusterLaw data.D Fmask y₀ j) Fhit L hhit y
    _ ≤ Real.exp L * (2 * (data.D j).w y) :=
      mul_le_mul_of_nonneg_left (hmaskAtom y) (Real.exp_nonneg _)
    _ ≤ Real.exp L * (2 * Real.exp (-((n : ℝ) ^ ζ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (data.D_atom j y) (by norm_num))
        (Real.exp_nonneg _)
    _ = 2 * Real.exp (L - (n : ℝ) ^ ζ) := by
      calc
        Real.exp L * (2 * Real.exp (-((n : ℝ) ^ ζ))) =
            2 * (Real.exp L * Real.exp (-((n : ℝ) ^ ζ))) := by ring
        _ = 2 * Real.exp (L - (n : ℝ) ^ ζ) := by
          rw [← Real.exp_add]
          congr 1

/-- Codegree guarantees on retained clusters survive conditioning them to a
mask, whenever the prior and masked laws assign positive mass. -/
theorem p10_1kMaskClusterLaw_codegree {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ}
    {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (F : Finset (Fin N)) (y₀ : Fin N) (j : Fin data.K) (y y' : Fin N)
    (hmask : (1 / 2 : ℝ) ≤ lawMassOn (data.D j) F)
    (hprior : 0 < data.lam j) (hy : 0 < (p10_1kMaskClusterLaw data.D F y₀ j).w y)
    (hy' : 0 < (p10_1kMaskClusterLaw data.D F y₀ j).w y') :
    1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G data.μ y y' := by
  have hmass : 0 < lawMassOn (data.D j) F :=
    lt_of_lt_of_le (by norm_num) hmask
  have hDpos (z : Fin N) (hz : 0 < (p10_1kMaskClusterLaw data.D F y₀ j).w z) :
      0 < (data.D j).w z := by
    by_contra hnot
    have hDzero : (data.D j).w z = 0 := le_antisymm
      (le_of_not_gt hnot) ((data.D j).nonneg z)
    have hzero : (p10_1kMaskClusterLaw data.D F y₀ j).w z = 0 := by
      simp [p10_1kMaskClusterLaw, hmass, Law.restrict, hDzero]
    exact (ne_of_gt hz) hzero
  exact data.codegree j hprior y y' (hDpos y hy) (hDpos y' hy')

/-- Positive weight after conditioning the cluster prior implies positive
original cluster weight. -/
theorem p10_1k_maskedPrior_pos_implies_original {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ}
    {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (R : Finset (Fin data.K)) (hR : 0 < FinProb.pr (p10_1kClusterPrior data)
      (fun j => j ∈ R)) (j : Fin data.K)
    (h : 0 < (FinProb.cond (p10_1kClusterPrior data) (fun j => j ∈ R) hR).w j) :
    0 < data.lam j := by
  classical
  let ρ := p10_1kClusterPrior data
  have hρ : 0 < ρ.w j := by
    by_contra hnot
    have hzero : ρ.w j = 0 := le_antisymm (le_of_not_gt hnot) (ρ.nonneg j)
    have hcondzero : (FinProb.cond ρ (fun j => j ∈ R) hR).w j = 0 := by
      by_cases hj : j ∈ R
      · simp [FinProb.cond, hj, hzero]
      · simp [FinProb.cond, hj]
    exact (ne_of_gt h) (by simpa [ρ] using hcondzero)
  simpa [ρ, p10_1kClusterPrior] using hρ

/-- Restricting each retained cluster to a half-mass mask and conditioning the
prior on a retained half preserves its aggregate law up to factor four. -/
theorem p10_1k_maskedClusterAggregate_le {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (ν : Law N)
    (F : Finset (Fin N)) (R : Finset (Fin q)) (y₀ : Fin N) (C : ℝ)
    (hR : (1 / 2 : ℝ) ≤ FinProb.pr ρ (fun j => j ∈ R))
    (hmask : ∀ j ∈ R, (1 / 2 : ℝ) ≤ lawMassOn (D j) F)
    (hagg : ∀ y, ∑ j, ρ.w j * (D j).w y ≤ C * ν.w y) :
    ∀ y, ∑ j,
      (FinProb.cond ρ (fun j => j ∈ R)
        (lt_of_lt_of_le (by norm_num) hR)).w j *
          (p10_1kMaskClusterLaw D F y₀ j).w y ≤ 4 * C * ν.w y := by
  classical
  intro y
  let ρ' := FinProb.cond ρ (fun j => j ∈ R)
    (lt_of_lt_of_le (by norm_num) hR)
  have hterm (j : Fin q) :
      ρ'.w j * (p10_1kMaskClusterLaw D F y₀ j).w y ≤
        4 * (ρ.w j * (D j).w y) := by
    by_cases hj : j ∈ R
    · have hmassHalf := hmask j hj
      have hmassPos : 0 < lawMassOn (D j) F :=
        lt_of_lt_of_le (by norm_num) hmassHalf
      have hprior : ρ'.w j = ρ.w j / FinProb.pr ρ (fun j => j ∈ R) := by
        simp [ρ', FinProb.cond, hj]
      have hpriorBound : ρ'.w j ≤ 2 * ρ.w j := by
        rw [hprior]
        apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hR)).2
        have hp : (1 : ℝ) ≤ 2 * FinProb.pr ρ (fun j => j ∈ R) := by
          linarith
        calc
          ρ.w j = 1 * ρ.w j := by ring
          _ ≤ (2 * FinProb.pr ρ (fun j => j ∈ R)) * ρ.w j :=
            mul_le_mul_of_nonneg_right hp (ρ.nonneg j)
          _ = 2 * ρ.w j * FinProb.pr ρ (fun j => j ∈ R) := by ring
      have hmaskAtom : (p10_1kMaskClusterLaw D F y₀ j).w y ≤ 2 * (D j).w y := by
        rw [p10_1kMaskClusterLaw, dif_pos hmassPos]
        exact p10_1k_restrict_atom_le_two (D j) F hmassHalf y
      calc
        ρ'.w j * (p10_1kMaskClusterLaw D F y₀ j).w y ≤
            (2 * ρ.w j) * (p10_1kMaskClusterLaw D F y₀ j).w y :=
          mul_le_mul_of_nonneg_right hpriorBound
            ((p10_1kMaskClusterLaw D F y₀ j).nonneg y)
        _ ≤ (2 * ρ.w j) * (2 * (D j).w y) :=
          mul_le_mul_of_nonneg_left hmaskAtom
            (mul_nonneg (by norm_num) (ρ.nonneg j))
        _ = 4 * (ρ.w j * (D j).w y) := by ring
    · have hprior : ρ'.w j = 0 := by simp [ρ', FinProb.cond, hj]
      simp only [hprior, zero_mul]
      exact mul_nonneg (by norm_num) (mul_nonneg (ρ.nonneg j) ((D j).nonneg y))
  calc
    (∑ j, ρ'.w j * (p10_1kMaskClusterLaw D F y₀ j).w y) ≤
        ∑ j, 4 * (ρ.w j * (D j).w y) :=
      Finset.sum_le_sum fun j hj => hterm j
    _ = 4 * ∑ j, ρ.w j * (D j).w y := by rw [Finset.mul_sum]
    _ ≤ 4 * (C * ν.w y) :=
      mul_le_mul_of_nonneg_left (hagg y) (by norm_num)
    _ = 4 * C * ν.w y := by ring

/-- A law assigns mass at most one to any finite set. -/
theorem p10_1k_lawMassOn_le_one {N : ℕ} (μ : Law N) (F : Finset (Fin N)) :
    lawMassOn μ F ≤ 1 := by
  classical
  calc
    lawMassOn μ F = ∑ y ∈ F, μ.w y := rfl
    _ ≤ ∑ y, μ.w y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      intro y hy hnot
      exact μ.nonneg y
    _ = 1 := μ.sum_eq_one

/-- The mass of a set under a mixture is the mixture of its component masses. -/
theorem p10_1k_lawMassOn_mix {N q : ℕ} (ρ : FinProb (Fin q))
    (D : Fin q → Law N) (F : Finset (Fin N)) :
    lawMassOn (Law.mix ρ D) F =
      ∑ j, ρ.w j * lawMassOn (D j) F := by
  classical
  unfold lawMassOn
  change (∑ y ∈ F, ∑ j, ρ.w j * (D j).w y) =
    ∑ j, ρ.w j * ∑ y ∈ F, (D j).w y
  calc
    (∑ y ∈ F, ∑ j, ρ.w j * (D j).w y) =
        ∑ j, ∑ y ∈ F, ρ.w j * (D j).w y := by rw [Finset.sum_comm]
    _ = ∑ j, ρ.w j * ∑ y ∈ F, (D j).w y := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]

/-- Retain those clusters assigning at least half their mass to the mask. -/
noncomputable def p10_1kRetainedClusterSet {N q : ℕ}
    (D : Fin q → Law N) (F : Finset (Fin N)) : Finset (Fin q) := by
  classical
  exact Finset.univ.filter fun j => (1 / 2 : ℝ) ≤ lawMassOn (D j) F

/-- A mask carrying at least nine tenths of the aggregate mass retains at least
half of the cluster prior after discarding clusters with mask mass below one
half. -/
theorem p10_1k_retainedClusterSet_mass {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (F : Finset (Fin N))
    (hF : 9 / 10 ≤ lawMassOn (Law.mix ρ D) F) :
    (1 / 2 : ℝ) ≤ FinProb.pr ρ (fun j => j ∈ p10_1kRetainedClusterSet D F) := by
  classical
  let R := p10_1kRetainedClusterSet D F
  let p : ℝ := FinProb.pr ρ (fun j => j ∈ R)
  have hpoint (j : Fin q) :
      ρ.w j * lawMassOn (D j) F ≤
        (1 / 2 : ℝ) * ρ.w j + (1 / 2 : ℝ) *
          (if j ∈ R then ρ.w j else 0) := by
    by_cases hj : j ∈ R
    · have hmass : (1 / 2 : ℝ) ≤ lawMassOn (D j) F := by
        simpa [R, p10_1kRetainedClusterSet] using
          (Finset.mem_filter.mp hj).2
      have hmassOne := p10_1k_lawMassOn_le_one (D j) F
      simp only [if_pos hj]
      calc
        ρ.w j * lawMassOn (D j) F ≤ ρ.w j * 1 :=
          mul_le_mul_of_nonneg_left hmassOne (ρ.nonneg j)
        _ = (1 / 2 : ℝ) * ρ.w j + (1 / 2 : ℝ) * ρ.w j := by ring
    · have hmass : lawMassOn (D j) F ≤ (1 / 2 : ℝ) := by
        have hnot : ¬ (1 / 2 : ℝ) ≤ lawMassOn (D j) F := by
          simpa [R, p10_1kRetainedClusterSet] using hj
        exact (lt_of_not_ge hnot).le
      simp only [if_neg hj]
      calc
        ρ.w j * lawMassOn (D j) F ≤ ρ.w j * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hmass (ρ.nonneg j)
        _ = (1 / 2 : ℝ) * ρ.w j := by ring
        _ = (1 / 2 : ℝ) * ρ.w j + (1 / 2 : ℝ) * 0 := by ring
  have hupper : lawMassOn (Law.mix ρ D) F ≤ 1 / 2 + (1 / 2 : ℝ) * p := by
    rw [p10_1k_lawMassOn_mix]
    calc
      (∑ j, ρ.w j * lawMassOn (D j) F) ≤
          ∑ j, ((1 / 2 : ℝ) * ρ.w j + (1 / 2 : ℝ) *
            (if j ∈ R then ρ.w j else 0)) :=
        Finset.sum_le_sum fun j hj => hpoint j
      _ = (1 / 2 : ℝ) * ∑ j, ρ.w j +
          (1 / 2 : ℝ) * ∑ j, (if j ∈ R then ρ.w j else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 1 / 2 + (1 / 2 : ℝ) * p := by
        rw [ρ.sum_eq_one]
        have hp : p = ∑ j, (if j ∈ R then ρ.w j else 0) := by
          dsimp [p, FinProb.pr]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hjR : j ∈ R <;> simp [hjR]
        rw [← hp]
        ring
  have hp : (1 / 2 : ℝ) ≤ p := by
    have hcomp : (9 / 10 : ℝ) ≤ 1 / 2 + (1 / 2 : ℝ) * p := le_trans hF hupper
    linarith
  exact hp

/-- A nonnegative price system yields a cheap-label mask and a retained
cluster mixture with a controlled aggregate. -/
theorem p10_1k_mask_price_response {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ}
    {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    {T : ℕ} (price : Fin (T + 1) → Fin N → ℝ)
    (hprice : ∀ t y, 0 ≤ price t y) (y₀ : Fin N) (hy₀ : y₀ ∈ B) :
    ∃ F : Finset (Fin N), ∃ R : Finset (Fin data.K),
      ∃ hret : 0 < FinProb.pr (p10_1kClusterPrior data) (fun j => j ∈ R),
      9 / 10 ≤ lawMassOn (p10_1kClusterAggregate data) F ∧
      (1 / 2 : ℝ) ≤ FinProb.pr (p10_1kClusterPrior data) (fun j => j ∈ R) ∧
      (∀ j ∈ R, (1 / 2 : ℝ) ≤ lawMassOn (data.D j) F) ∧
      (∀ t, (∑ y ∈ F, (p10_1kClusterAggregate data).w y * price t y) ≤
        10 * totalMaskPrice (p10_1kClusterAggregate data) price) ∧
      (∀ y, ∑ j,
        (FinProb.cond (p10_1kClusterPrior data) (fun j => j ∈ R)
          hret).w j *
            (p10_1kMaskClusterLaw data.D F y₀ j).w y ≤
          4 * (p10_1kClusterAggregate data).w y) := by
  classical
  let ρ := p10_1kClusterPrior data
  let ν := p10_1kClusterAggregate data
  let F := cheapMaskLabels ν price
  let R := p10_1kRetainedClusterSet data.D F
  have hmask := p10_1f_mask_price_separation ν price hprice
  have hmass : 9 / 10 ≤ lawMassOn (Law.mix ρ data.D) F := by
    simpa [F, ν, ρ, p10_1kClusterAggregate, p10_1kClusterPrior, Law.mix] using hmask.1
  have hR : (1 / 2 : ℝ) ≤ FinProb.pr ρ (fun j => j ∈ R) := by
    exact p10_1k_retainedClusterSet_mass ρ data.D F hmass
  have hcomponent : ∀ j ∈ R, (1 / 2 : ℝ) ≤ lawMassOn (data.D j) F := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hagg : ∀ y, ∑ j, ρ.w j * (data.D j).w y ≤ 1 * ν.w y := by
    intro y
    simp [ν, ρ, p10_1kClusterAggregate, p10_1kClusterPrior, Law.mix]
  have hcond : 0 < FinProb.pr ρ (fun j => j ∈ R) :=
    lt_of_lt_of_le (by norm_num) hR
  refine ⟨F, R, hcond, ?_, hR, hcomponent, hmask.2, ?_⟩
  · simpa [F, ν] using hmask.1
  · intro y
    have hbound := p10_1k_maskedClusterAggregate_le ρ data.D ν F R
      y₀ 1 hR hcomponent hagg y
    simpa [ρ, ν] using hbound

/-- Positive codegree guarantees a positive-mass common neighbor for a pair. -/
theorem p10_1k_pair_common_neighbor_exists {N : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (μ : Law N) (y y' : Fin N)
    (hcodeg : 0 < codeg E G μ y y') :
    ∃ x, 0 < μ.w x ∧ Hits E G x y ∧ Hits E G x y' := by
  classical
  by_contra h
  have hterm (x : Fin N) :
      μ.w x * (if Hits E G x y ∧ Hits E G x y' then 1 else 0) = 0 := by
    by_cases hhit : Hits E G x y ∧ Hits E G x y'
    · have hnotpos : ¬ 0 < μ.w x := by
        intro hxpos
        exact h ⟨x, hxpos, hhit.1, hhit.2⟩
      have hxzero : μ.w x = 0 :=
        le_antisymm (le_of_not_gt hnotpos) (μ.nonneg x)
      simp [hhit, hxzero]
    · simp [hhit]
  have hzero : codeg E G μ y y' = 0 := by
    unfold codeg
    exact Finset.sum_eq_zero fun x hx => hterm x
  rw [hzero] at hcodeg
  norm_num at hcodeg

/-- A single chunk projection sends a one-bit neighbor to distance at most three. -/
private theorem p10_1k_chunkProjection_flip_dist_le_three
    {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (h₂ : ∀ g : G, g + g = 0) (s : G → Bool) (g : G) :
    hammingDist (chunkProject s) (chunkProject (flipChunkBit s g)) ≤ 3 := by
  have hprojS := (p10_1a_hamming_projection (G := G) h₂).1 s
  have hprojT := (p10_1a_hamming_projection (G := G) h₂).1 (flipChunkBit s g)
  have hs : hammingDist s (chunkProject s) = 1 := by
    simpa [hammingDist, chunkHammingDistance] using hprojS.2
  have ht : hammingDist (flipChunkBit s g) (chunkProject (flipChunkBit s g)) = 1 := by
    simpa [hammingDist, chunkHammingDistance] using hprojT.2
  have hedge : hammingDist s (flipChunkBit s g) = 1 := by
    have hset : Finset.univ.filter (fun i : G => s i ≠ flipChunkBit s g i) = {g} := by
      ext i
      simp [flipChunkBit]
    calc
      hammingDist s (flipChunkBit s g) =
          chunkHammingDistance s (flipChunkBit s g) := by
        simp [hammingDist, chunkHammingDistance]
      _ = 1 := by simp [chunkHammingDistance, hset]
  have h₁ := hammingDist_triangle (chunkProject s) s (chunkProject (flipChunkBit s g))
  have h₂' := hammingDist_triangle s (flipChunkBit s g) (chunkProject (flipChunkBit s g))
  have hsymm : hammingDist (chunkProject s) s = 1 := by
    simpa [hammingDist_comm] using hs
  calc
    hammingDist (chunkProject s) (chunkProject (flipChunkBit s g)) ≤
        hammingDist (chunkProject s) s + hammingDist s (chunkProject (flipChunkBit s g)) := h₁
    _ ≤ 1 + (hammingDist s (flipChunkBit s g) +
        hammingDist (flipChunkBit s g) (chunkProject (flipChunkBit s g))) :=
      add_le_add (le_of_eq hsymm) h₂'
    _ = 3 := by rw [hedge, ht]

/-- Apply the syndrome projection independently in every binary chunk. -/
noncomputable def p10_1k_projectedWord (d : ℕ) (s : Fin d → Bool) : Fin d → Bool :=
  (p10_1kChunkFamilyEquiv d).symm
    (productProject (p10_1kChunkFamilyEquiv d s))

/-- Each chunk of the projected word has zero syndrome. -/
theorem p10_1k_projectedChunk_syndrome_zero (d : ℕ) (s : Fin d → Bool)
    (i : Fin d.bitIndices.length) :
    chunkSyndrome (productProject (p10_1k_chunkedWord d s) i) = 0 := by
  have hproject := p10_1a_hamming_projection
    (G := P10_1kChunkGroup d i) (p10_1k_chunkGroup_two_add d i)
  exact (hproject.1 (p10_1k_chunkedWord d s i)).1

/-- The projected word, reindexed by its chunks, is the product of the chunk
projections. -/
theorem p10_1k_chunkedWord_projected (d : ℕ) (s : Fin d → Bool) :
    p10_1k_chunkedWord d (p10_1k_projectedWord d s) =
      productProject (p10_1k_chunkedWord d s) := by
  calc
    p10_1k_chunkedWord d (p10_1k_projectedWord d s) =
        p10_1kChunkFamilyEquiv d (p10_1k_projectedWord d s) :=
      p10_1k_chunkedWord_eq_familyEquiv d _
    _ = productProject (p10_1kChunkFamilyEquiv d s) :=
      Equiv.apply_symm_apply (p10_1kChunkFamilyEquiv d) _
    _ = productProject (p10_1k_chunkedWord d s) := by
      rw [p10_1k_chunkedWord_eq_familyEquiv]

/-- A product projection fiber is the product of its chunk projection fibers. -/
private noncomputable def p10_1k_productProjectionFiberEquiv (d : ℕ)
    (t : P10_1kChunkWord d) :
    {W : P10_1kChunkWord d // productProject W = t} ≃
      ∀ i : Fin d.bitIndices.length,
        {u : P10_1kChunkGroup d i → Bool // chunkProject u = t i} where
  toFun W i := ⟨W.1 i, congrFun W.2 i⟩
  invFun W := ⟨fun i => (W i).1, by
    funext i
    exact (W i).2⟩
  left_inv W := by
    apply Subtype.ext
    funext i g
    rfl
  right_inv W := by
    funext i
    apply Subtype.ext
    rfl

/-- Reindex a residual projection fiber as a product-projection fiber. -/
private noncomputable def p10_1k_residualProjectionFiberEquiv (d : ℕ)
    (s₀ : Fin d → Bool) :
    {s : Fin d → Bool // p10_1k_projectedWord d s = p10_1k_projectedWord d s₀} ≃
      {W : P10_1kChunkWord d //
        productProject W = productProject (p10_1k_chunkedWord d s₀)} where
  toFun x := ⟨p10_1kChunkFamilyEquiv d x.1, by
    have hx := congrArg (p10_1kChunkFamilyEquiv d) x.2
    have hx' : productProject (p10_1kChunkFamilyEquiv d x.1) =
        productProject (p10_1kChunkFamilyEquiv d s₀) := by
      simpa [p10_1k_projectedWord] using hx
    simpa [← p10_1k_chunkedWord_eq_familyEquiv d s₀] using hx'⟩
  invFun x := ⟨(p10_1kChunkFamilyEquiv d).symm x.1, by
    have hx : productProject x.1 = productProject (p10_1kChunkFamilyEquiv d s₀) := by
      simpa [p10_1k_chunkedWord_eq_familyEquiv] using x.2
    apply (p10_1kChunkFamilyEquiv d).injective
    simpa [p10_1k_projectedWord] using hx⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- The residual projection fiber has the product of the chunk group orders. -/
theorem p10_1k_projectedFiber_card (d : ℕ) (s₀ : Fin d → Bool) :
    Fintype.card {s : Fin d → Bool //
      p10_1k_projectedWord d s = p10_1k_projectedWord d s₀} =
      ∏ i : Fin d.bitIndices.length, Fintype.card (P10_1kChunkGroup d i) := by
  classical
  let t := productProject (p10_1k_chunkedWord d s₀)
  calc
    Fintype.card {s : Fin d → Bool //
        p10_1k_projectedWord d s = p10_1k_projectedWord d s₀} =
        Fintype.card {W : P10_1kChunkWord d // productProject W = t} :=
      Fintype.card_congr (p10_1k_residualProjectionFiberEquiv d s₀)
    _ = Fintype.card (∀ i : Fin d.bitIndices.length,
        {u : P10_1kChunkGroup d i → Bool // chunkProject u = t i}) :=
      Fintype.card_congr (p10_1k_productProjectionFiberEquiv d t)
    _ = ∏ i : Fin d.bitIndices.length,
        Fintype.card {u : P10_1kChunkGroup d i → Bool // chunkProject u = t i} := by
      simp
    _ = ∏ i : Fin d.bitIndices.length, Fintype.card (P10_1kChunkGroup d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hzero : chunkSyndrome (t i) = 0 := by
        dsimp [t, productProject]
        exact p10_1k_projectedChunk_syndrome_zero d s₀ i
      have hpreimage :=
        (p10_1a_hamming_projection (G := P10_1kChunkGroup d i)
          (p10_1k_chunkGroup_two_add d i)).2 (t i) hzero
      simpa [Fintype.card_subtype] using hpreimage

/-- The projected fiber size is a single power of two with exponent the sum of
the binary chunk indices. -/
theorem p10_1k_projectedFiber_card_eq_pow (d : ℕ) (s₀ : Fin d → Bool) :
    Fintype.card {s : Fin d → Bool //
      p10_1k_projectedWord d s = p10_1k_projectedWord d s₀} =
      2 ^ (∑ i : Fin d.bitIndices.length, d.bitIndices.get i) := by
  rw [p10_1k_projectedFiber_card]
  simp [P10_1kChunkGroup, Finset.prod_pow_eq_pow_sum]

/-- True coordinates of a chunked word are the disjoint union of the true
coordinates in its chunks. -/
private noncomputable def p10_1k_chunkSigmaTrueEquiv (d : ℕ) (s : Fin d → Bool) :
    {p : P10_1kChunkCoordinate d // p10_1k_chunkWordEquiv d s p = true} ≃
      Σ i : Fin d.bitIndices.length,
        {g : P10_1kChunkGroup d i // p10_1k_chunkedWord d s i g = true} where
  toFun x := ⟨x.1.1, ⟨x.1.2, by
    simpa [p10_1k_chunkWordEquiv, p10_1k_chunkedWord] using x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, by
    simpa [p10_1k_chunkWordEquiv, p10_1k_chunkedWord] using x.2.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

/-- The total number of true bits in a chunked word is its product count. -/
theorem p10_1k_productTrueCount_eq_card (d : ℕ) (s : Fin d → Bool) :
    productTrueCount (p10_1k_chunkedWord d s) =
      Fintype.card {p : P10_1kChunkCoordinate d //
        p10_1k_chunkWordEquiv d s p = true} := by
  classical
  calc
    productTrueCount (p10_1k_chunkedWord d s) =
        ∑ i : Fin d.bitIndices.length,
          Fintype.card {g : P10_1kChunkGroup d i //
            p10_1k_chunkedWord d s i g = true} := by
      simp [productTrueCount, Fintype.card_subtype]
    _ = Fintype.card (Σ i : Fin d.bitIndices.length,
          {g : P10_1kChunkGroup d i // p10_1k_chunkedWord d s i g = true}) := by
      rw [Fintype.card_sigma]
    _ = Fintype.card {p : P10_1kChunkCoordinate d //
          p10_1k_chunkWordEquiv d s p = true} :=
      (Fintype.card_congr (p10_1k_chunkSigmaTrueEquiv d s)).symm

/-- Reindexing preserves the parity of a cube word. -/
private noncomputable def p10_1k_trueCoordinateEquiv (d : ℕ) (s : Fin d → Bool) :
    {i : Fin d // s i = true} ≃
      {p : P10_1kChunkCoordinate d // p10_1k_chunkWordEquiv d s p = true} where
  toFun x := ⟨p10_1k_chunkCoordinateEquiv d x.1, by
    simpa [p10_1k_chunkWordEquiv] using x.2⟩
  invFun x := ⟨(p10_1k_chunkCoordinateEquiv d).symm x.1, by
    simpa [p10_1k_chunkWordEquiv] using x.2⟩
  left_inv := by intro x; cases x; simp
  right_inv := by intro x; cases x; simp

/-- True-coordinate count is unchanged by the binary chunk reindexing. -/
theorem p10_1k_trueCount_eq_productTrueCount (d : ℕ) (s : Fin d → Bool) :
    Fintype.card {i : Fin d // s i = true} =
      productTrueCount (p10_1k_chunkedWord d s) := by
  calc
    Fintype.card {i : Fin d // s i = true} =
        Fintype.card {p : P10_1kChunkCoordinate d //
          p10_1k_chunkWordEquiv d s p = true} :=
      Fintype.card_congr (p10_1k_trueCoordinateEquiv d s)
    _ = productTrueCount (p10_1k_chunkedWord d s) :=
      (p10_1k_productTrueCount_eq_card d s).symm

/-- The binary chunk projection changes the role parity according to the number
of binary chunks. -/
theorem p10_1k_projectedWord_parity (d : ℕ) (s : Fin d → Bool) :
    (Even (Fintype.card (Fin d.bitIndices.length)) →
      (Even (Fintype.card {i : Fin d // s i = true}) ↔
        Even (Fintype.card {i : Fin d // p10_1k_projectedWord d s i = true}))) ∧
    (Odd (Fintype.card (Fin d.bitIndices.length)) →
      (Even (Fintype.card {i : Fin d // s i = true}) ↔
        ¬ Even (Fintype.card {i : Fin d // p10_1k_projectedWord d s i = true}))) := by
  have h₂ : ∀ i : Fin d.bitIndices.length, ∀ g : P10_1kChunkGroup d i, g + g = 0 :=
    fun i g => p10_1k_chunkGroup_two_add d i g
  have hp := p10_1a_product_parity h₂ (p10_1k_chunkedWord d s)
  refine ⟨?_, ?_⟩
  · intro hEven
    have h := hp.1 hEven
    rw [p10_1k_trueCount_eq_productTrueCount d s,
      p10_1k_trueCount_eq_productTrueCount d (p10_1k_projectedWord d s),
      p10_1k_chunkedWord_projected]
    exact h
  · intro hOdd
    have h := hp.2 hOdd
    rw [p10_1k_trueCount_eq_productTrueCount d s,
      p10_1k_trueCount_eq_productTrueCount d (p10_1k_projectedWord d s),
      p10_1k_chunkedWord_projected]
    exact h

/-- Reindexing preserves Hamming distance as well as parity. -/
private noncomputable def p10_1k_diffCoordinateEquiv (d : ℕ)
    (s t : Fin d → Bool) :
    {i : Fin d // s i ≠ t i} ≃
      {p : P10_1kChunkCoordinate d //
        p10_1k_chunkWordEquiv d s p ≠ p10_1k_chunkWordEquiv d t p} where
  toFun x := ⟨p10_1k_chunkCoordinateEquiv d x.1, by
    simpa [p10_1k_chunkWordEquiv] using x.2⟩
  invFun x := ⟨(p10_1k_chunkCoordinateEquiv d).symm x.1, by
    simpa [p10_1k_chunkWordEquiv] using x.2⟩
  left_inv := by intro x; cases x; simp
  right_inv := by intro x; cases x; simp

private noncomputable def p10_1k_chunkSigmaDiffEquiv (d : ℕ)
    (s t : Fin d → Bool) :
    {p : P10_1kChunkCoordinate d //
      p10_1k_chunkWordEquiv d s p ≠ p10_1k_chunkWordEquiv d t p} ≃
      Σ i : Fin d.bitIndices.length,
        {g : P10_1kChunkGroup d i //
          p10_1k_chunkedWord d s i g ≠ p10_1k_chunkedWord d t i g} where
  toFun x := ⟨x.1.1, ⟨x.1.2, by
    simpa [p10_1k_chunkWordEquiv, p10_1k_chunkedWord] using x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, by
    simpa [p10_1k_chunkWordEquiv, p10_1k_chunkedWord] using x.2.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

/-- The residual Hamming metric equals the sum of its chunk metrics. -/
theorem p10_1k_hammingDist_eq_productHammingDistance (d : ℕ)
    (s t : Fin d → Bool) :
    hammingDist s t =
      productHammingDistance (p10_1k_chunkedWord d s) (p10_1k_chunkedWord d t) := by
  classical
  calc
    hammingDist s t = Fintype.card {i : Fin d // s i ≠ t i} := by
      simp [hammingDist, Fintype.card_subtype]
    _ = Fintype.card {p : P10_1kChunkCoordinate d //
          p10_1k_chunkWordEquiv d s p ≠ p10_1k_chunkWordEquiv d t p} :=
      Fintype.card_congr (p10_1k_diffCoordinateEquiv d s t)
    _ = Fintype.card (Σ i : Fin d.bitIndices.length,
          {g : P10_1kChunkGroup d i //
            p10_1k_chunkedWord d s i g ≠ p10_1k_chunkedWord d t i g}) :=
      Fintype.card_congr (p10_1k_chunkSigmaDiffEquiv d s t)
    _ = ∑ i : Fin d.bitIndices.length,
          Fintype.card {g : P10_1kChunkGroup d i //
            p10_1k_chunkedWord d s i g ≠ p10_1k_chunkedWord d t i g} := by
      rw [Fintype.card_sigma]
    _ = productHammingDistance (p10_1k_chunkedWord d s) (p10_1k_chunkedWord d t) := by
      simp [productHammingDistance, chunkHammingDistance, Fintype.card_subtype]

/-- Projection moves a residual word by one bit in every binary chunk. -/
theorem p10_1k_projectedWord_hammingDist (d : ℕ) (s : Fin d → Bool) :
    hammingDist s (p10_1k_projectedWord d s) =
      Fintype.card (Fin d.bitIndices.length) := by
  have h₂ : ∀ i : Fin d.bitIndices.length, ∀ g : P10_1kChunkGroup d i, g + g = 0 :=
    fun i g => p10_1k_chunkGroup_two_add d i g
  rw [p10_1k_hammingDist_eq_productHammingDistance,
    p10_1k_chunkedWord_projected]
  exact p10_1a_product_distance h₂ (p10_1k_chunkedWord d s)

/-- Two residual words with the same projected word are within two coordinates
per binary chunk. -/
theorem p10_1k_projectedWord_fiber_diameter (d : ℕ) (s t : Fin d → Bool)
    (hproj : p10_1k_projectedWord d s = p10_1k_projectedWord d t) :
    hammingDist s t ≤ 2 * Fintype.card (Fin d.bitIndices.length) := by
  have h₂ : ∀ i : Fin d.bitIndices.length, ∀ g : P10_1kChunkGroup d i, g + g = 0 :=
    fun i g => p10_1k_chunkGroup_two_add d i g
  have hchunk := congrArg (p10_1k_chunkedWord d) hproj
  have hs := p10_1k_chunkedWord_projected d s
  have ht := p10_1k_chunkedWord_projected d t
  have hproduct : productProject (p10_1k_chunkedWord d s) =
      productProject (p10_1k_chunkedWord d t) := by
    rw [← hs, ← ht]
    exact hchunk
  rw [p10_1k_hammingDist_eq_productHammingDistance]
  exact p10_1a_product_fiber_diameter h₂
    (p10_1k_chunkedWord d s) (p10_1k_chunkedWord d t) hproduct

/-- A residual cube edge moves at most three coordinates after projection. -/
theorem p10_1k_projectedWord_flip_hammingDist_le_three (d : ℕ)
    (s : Fin d → Bool) (j : Fin d) :
    hammingDist (p10_1k_projectedWord d s)
        (p10_1k_projectedWord d (p10_1kFlipCoordinate s j)) ≤ 3 := by
  let p := p10_1k_chunkCoordinateEquiv d j
  let W := p10_1k_chunkedWord d s
  let W' := p10_1k_chunkedWord d (p10_1kFlipCoordinate s j)
  have hchanged := p10_1k_chunkedWord_flip_changed d s j
  have hchanged' : W' p.1 = flipChunkBit (W p.1) p.2 := by
    simpa [W, W', p] using hchanged
  have hunchanged (i : Fin d.bitIndices.length) (hi : i ≠ p.1) : W' i = W i := by
    exact p10_1k_chunkedWord_flip_unchanged d s j i hi
  have h₂ : ∀ g : P10_1kChunkGroup d p.1, g + g = 0 :=
    p10_1k_chunkGroup_two_add d p.1
  have hlocal := p10_1k_chunkProjection_flip_dist_le_three h₂ (W p.1) p.2
  let term : Fin d.bitIndices.length → ℕ := fun i =>
    chunkHammingDistance (productProject W i) (productProject W' i)
  have hsum : (∑ i, term i) = term p.1 :=
    Fintype.sum_eq_single p.1 (fun i hi => by
      simp [term, productProject, hunchanged i hi, chunkHammingDistance])
  have hproduct : productHammingDistance (productProject W) (productProject W') =
      chunkHammingDistance (chunkProject (W p.1))
        (chunkProject (flipChunkBit (W p.1) p.2)) := by
    calc
      productHammingDistance (productProject W) (productProject W') = ∑ i, term i := rfl
      _ = term p.1 := hsum
      _ = chunkHammingDistance (chunkProject (W p.1))
          (chunkProject (flipChunkBit (W p.1) p.2)) := by
        simp [term, productProject, hchanged']
  rw [p10_1k_hammingDist_eq_productHammingDistance,
    p10_1k_chunkedWord_projected]
  rw [p10_1k_chunkedWord_projected]
  rw [hproduct]
  simpa [chunkHammingDistance, hammingDist] using hlocal

/-- The changed chunk of a residual coordinate flip is its local projected
neighbor. -/
theorem p10_1k_projectedWord_flip_changed_chunk (d : ℕ) (s : Fin d → Bool)
    (j : Fin d) :
    p10_1k_chunkedWord d (p10_1k_projectedWord d (p10_1kFlipCoordinate s j))
        (p10_1k_chunkCoordinateEquiv d j).1 =
      projectedNeighbor
        (p10_1k_chunkedWord d s (p10_1k_chunkCoordinateEquiv d j).1)
        (p10_1k_chunkCoordinateEquiv d j).2 := by
  rw [p10_1k_chunkedWord_projected]
  simp only [productProject]
  rw [p10_1k_chunkedWord_flip_changed]
  rfl

/-- Every other chunk is unchanged after projecting a residual coordinate flip. -/
theorem p10_1k_projectedWord_flip_unchanged_chunk (d : ℕ) (s : Fin d → Bool)
    (j : Fin d) (i : Fin d.bitIndices.length)
    (hi : i ≠ (p10_1k_chunkCoordinateEquiv d j).1) :
    p10_1k_chunkedWord d (p10_1k_projectedWord d (p10_1kFlipCoordinate s j)) i =
      chunkProject (p10_1k_chunkedWord d s i) := by
  rw [p10_1k_chunkedWord_projected]
  simp only [productProject]
  rw [p10_1k_chunkedWord_flip_unchanged d s j i hi]

/-- Residual neighbors changed in different chunks have different projected
sites. -/
theorem p10_1k_projectedNeighbors_distinct_chunks (d : ℕ) (s : Fin d → Bool)
    (j k : Fin d)
    (hjk : (p10_1k_chunkCoordinateEquiv d j).1 ≠
      (p10_1k_chunkCoordinateEquiv d k).1) :
    p10_1k_projectedWord d (p10_1kFlipCoordinate s j) ≠
      p10_1k_projectedWord d (p10_1kFlipCoordinate s k) := by
  intro heq
  let e := p10_1k_chunkCoordinateEquiv d
  have hchunk := congrArg (fun v : Fin d → Bool =>
    p10_1k_chunkedWord d v (e j).1) heq
  have hlocal :
      projectedNeighbor (p10_1k_chunkedWord d s (e j).1) (e j).2 =
        chunkProject (p10_1k_chunkedWord d s (e j).1) := by
    calc
      projectedNeighbor (p10_1k_chunkedWord d s (e j).1) (e j).2 =
          p10_1k_chunkedWord d (p10_1k_projectedWord d
            (p10_1kFlipCoordinate s j)) (e j).1 :=
        (p10_1k_projectedWord_flip_changed_chunk d s j).symm
      _ = p10_1k_chunkedWord d (p10_1k_projectedWord d
            (p10_1kFlipCoordinate s k)) (e j).1 := hchunk
      _ = chunkProject (p10_1k_chunkedWord d s (e j).1) :=
        p10_1k_projectedWord_flip_unchanged_chunk d s k (e j).1 hjk
  exact p10_1k_projectedNeighbor_ne_projectedCenter
    (fun g => p10_1k_chunkGroup_two_add d (e j).1 g)
    (p10_1k_chunkedWord d s (e j).1) (e j).2 hlocal

/-- If two residual neighbors project to the same site, their flipped
coordinates belong to the same chunk. -/
theorem p10_1k_projectedNeighbors_same_chunk_of_eq (d : ℕ) (s : Fin d → Bool)
    (j k : Fin d)
    (heq : p10_1k_projectedWord d (p10_1kFlipCoordinate s j) =
      p10_1k_projectedWord d (p10_1kFlipCoordinate s k)) :
    (p10_1k_chunkCoordinateEquiv d j).1 =
      (p10_1k_chunkCoordinateEquiv d k).1 := by
  by_contra hne
  exact (p10_1k_projectedNeighbors_distinct_chunks d s j k hne) heq

/-- Split the cube coordinates into a special prefix and a residual suffix. -/
noncomputable def p10_1kCoordinateSplit {n m : ℕ} (hm : m ≤ n) :
    Fin n ≃ Fin m ⊕ Fin (n - m) :=
  ((finSumFinEquiv (m := m) (n := n - m)).trans
    (finCongr (Nat.add_sub_of_le hm))).symm

/-- The corresponding split of cube words into a special slice and a residual word. -/
noncomputable def p10_1kSliceWordEquiv {n m : ℕ} (hm : m ≤ n) :
    (Fin n → Bool) ≃ (Fin m → Bool) × (Fin (n - m) → Bool) :=
  (Equiv.piCongrLeft (fun _ : Fin m ⊕ Fin (n - m) => Bool)
      (p10_1kCoordinateSplit hm)).trans
    (Equiv.sumPiEquivProdPi (fun _ => Bool))

/-- The special-coordinate slice of a cube vertex. -/
noncomputable def p10_1kSpecialSlice {n m : ℕ} (hm : m ≤ n) (v : Fin n → Bool) : Fin m → Bool :=
  (p10_1kSliceWordEquiv hm v).1

/-- The residual word of a cube vertex after removing its special coordinates. -/
noncomputable def p10_1kResidualWord {n m : ℕ} (hm : m ≤ n) (v : Fin n → Bool) :
    Fin (n - m) → Bool :=
  (p10_1kSliceWordEquiv hm v).2

/-- The actual cube vertex obtained by flipping one residual coordinate. -/
noncomputable def p10_1kResidualFlipVertex {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (j : Fin (n - m)) : Fin n → Bool :=
  (p10_1kSliceWordEquiv hm).symm
    (p10_1kSpecialSlice hm v,
      p10_1kFlipCoordinate (p10_1kResidualWord hm v) j)

/-- The actual cube vertex obtained by flipping one special coordinate. -/
noncomputable def p10_1kSpecialFlipVertex {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (i : Fin m) : Fin n → Bool :=
  (p10_1kSliceWordEquiv hm).symm
    (p10_1kFlipCoordinate (p10_1kSpecialSlice hm v) i,
      p10_1kResidualWord hm v)

/-- A special-coordinate flip has the expected special slice. -/
theorem p10_1kSpecialFlipVertex_specialSlice {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (i : Fin m) :
    p10_1kSpecialSlice hm (p10_1kSpecialFlipVertex hm v i) =
      p10_1kFlipCoordinate (p10_1kSpecialSlice hm v) i := by
  simp [p10_1kSpecialSlice, p10_1kSpecialFlipVertex]

/-- A special-coordinate flip leaves the residual word unchanged. -/
theorem p10_1kSpecialFlipVertex_residualWord {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (i : Fin m) :
    p10_1kResidualWord hm (p10_1kSpecialFlipVertex hm v i) =
      p10_1kResidualWord hm v := by
  simp [p10_1kResidualWord, p10_1kSpecialFlipVertex]

/-- A residual-coordinate flip leaves the special slice unchanged. -/
theorem p10_1kResidualFlipVertex_specialSlice {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (j : Fin (n - m)) :
    p10_1kSpecialSlice hm (p10_1kResidualFlipVertex hm v j) =
      p10_1kSpecialSlice hm v := by
  simp [p10_1kSpecialSlice, p10_1kResidualFlipVertex]

/-- The residual word of a residual-coordinate flip is the specified flip. -/
theorem p10_1kResidualFlipVertex_residualWord {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (j : Fin (n - m)) :
    p10_1kResidualWord hm (p10_1kResidualFlipVertex hm v j) =
      p10_1kFlipCoordinate (p10_1kResidualWord hm v) j := by
  simp [p10_1kResidualWord, p10_1kResidualFlipVertex]

private noncomputable def p10_1k_hammingDiffEquiv {A B : Type*} [Fintype A]
    [Fintype B] (e : A ≃ B) (f g : B → Bool) :
    {a : A // f (e a) ≠ g (e a)} ≃ {b : B // f b ≠ g b} where
  toFun x := ⟨e x.1, by simpa using x.2⟩
  invFun x := ⟨e.symm x.1, by simpa using x.2⟩
  left_inv := by intro x; cases x; simp
  right_inv := by intro x; cases x; simp

/-- Hamming distance is invariant under a coordinate equivalence. -/
private theorem p10_1k_hammingDist_domain_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f g : B → Bool) :
    hammingDist (fun a => f (e a)) (fun a => g (e a)) = hammingDist f g := by
  calc
    hammingDist (fun a => f (e a)) (fun a => g (e a)) =
        Fintype.card {a : A // f (e a) ≠ g (e a)} := by
      simp [hammingDist, Fintype.card_subtype]
    _ = Fintype.card {b : B // f b ≠ g b} :=
      Fintype.card_congr (p10_1k_hammingDiffEquiv e f g)
    _ = hammingDist f g := by simp [hammingDist, Fintype.card_subtype]

/-- Hamming distance on a sum type splits into the two component distances. -/
private theorem p10_1k_hammingDist_sum {A B : Type*} [Fintype A] [Fintype B]
    (f f' : A → Bool) (g g' : B → Bool) :
    hammingDist (Sum.elim f g) (Sum.elim f' g') =
      hammingDist f f' + hammingDist g g' := by
  classical
  let e : {x : A ⊕ B // Sum.elim f g x ≠ Sum.elim f' g' x} ≃
      ({x : A // f x ≠ f' x} ⊕ {y : B // g y ≠ g' y}) := {
    toFun := fun x => by
      rcases x with ⟨z, hz⟩
      cases z with
      | inl a => exact Sum.inl ⟨a, by simpa using hz⟩
      | inr b => exact Sum.inr ⟨b, by simpa using hz⟩
    invFun := fun x => by
      cases x with
      | inl a => exact ⟨Sum.inl a.1, by simpa using a.2⟩
      | inr b => exact ⟨Sum.inr b.1, by simpa using b.2⟩
    left_inv := by
      rintro ⟨x, hx⟩
      apply Subtype.ext
      cases x <;> rfl
    right_inv := by
      rintro (⟨a, ha⟩ | ⟨b, hb⟩) <;> rfl
  }
  calc
    hammingDist (Sum.elim f g) (Sum.elim f' g') =
        Fintype.card {x : A ⊕ B // Sum.elim f g x ≠ Sum.elim f' g' x} := by
      simp [hammingDist, Fintype.card_subtype]
    _ = Fintype.card ({x : A // f x ≠ f' x} ⊕ {y : B // g y ≠ g' y}) :=
      Fintype.card_congr e
    _ = Fintype.card {x : A // f x ≠ f' x} + Fintype.card {y : B // g y ≠ g' y} :=
      Fintype.card_sum
    _ = hammingDist f f' + hammingDist g g' := by
      simp [hammingDist, Fintype.card_subtype]

/-- Splitting coordinates adds the Hamming distances in the special and residual words. -/
theorem p10_1kSliceHammingDist {n m : ℕ} (hm : m ≤ n) (v w : Fin n → Bool) :
    hammingDist v w =
      hammingDist (p10_1kSpecialSlice hm v) (p10_1kSpecialSlice hm w) +
        hammingDist (p10_1kResidualWord hm v) (p10_1kResidualWord hm w) := by
  let e := p10_1kCoordinateSplit hm
  let p := p10_1kSliceWordEquiv hm v
  let q := p10_1kSliceWordEquiv hm w
  let f := Equiv.piCongrLeft (fun _ : Fin m ⊕ Fin (n - m) => Bool) e v
  let g := Equiv.piCongrLeft (fun _ : Fin m ⊕ Fin (n - m) => Bool) e w
  have hv : (fun x => f (e x)) = v := by
    funext x
    simp [f, e]
  have hw : (fun x => g (e x)) = w := by
    funext x
    simp [g, e]
  have hf : f = Sum.elim (fun i => f (Sum.inl i)) (fun j => f (Sum.inr j)) := by
    funext x
    cases x <;> rfl
  have hg : g = Sum.elim (fun i => g (Sum.inl i)) (fun j => g (Sum.inr j)) := by
    funext x
    cases x <;> rfl
  calc
    hammingDist v w = hammingDist (fun x => f (e x)) (fun x => g (e x)) := by
      rw [hv, hw]
    _ = hammingDist f g := p10_1k_hammingDist_domain_equiv e f g
    _ = hammingDist (p10_1kSpecialSlice hm v) (p10_1kSpecialSlice hm w) +
        hammingDist (p10_1kResidualWord hm v) (p10_1kResidualWord hm w) := by
      rw [hf, hg, p10_1k_hammingDist_sum]
      simp [p10_1kSpecialSlice, p10_1kResidualWord, p10_1kSliceWordEquiv, f, g, e]

/-- An edge changes either one special coordinate or one residual coordinate. -/
theorem p10_1k_adjacentCoordinates_split {n m : ℕ} (hm : m ≤ n)
    {v w : Fin n → Bool} (hadj : (cube n).Adj v w) :
    (hammingDist (p10_1kSpecialSlice hm v) (p10_1kSpecialSlice hm w) = 1 ∧
      p10_1kResidualWord hm v = p10_1kResidualWord hm w) ∨
    (p10_1kSpecialSlice hm v = p10_1kSpecialSlice hm w ∧
      hammingDist (p10_1kResidualWord hm v) (p10_1kResidualWord hm w) = 1) := by
  change hammingDist v w = 1 at hadj
  rw [p10_1kSliceHammingDist hm v w] at hadj
  have hcases :
      (hammingDist (p10_1kSpecialSlice hm v) (p10_1kSpecialSlice hm w) = 1 ∧
        hammingDist (p10_1kResidualWord hm v) (p10_1kResidualWord hm w) = 0) ∨
      (hammingDist (p10_1kSpecialSlice hm v) (p10_1kSpecialSlice hm w) = 0 ∧
        hammingDist (p10_1kResidualWord hm v) (p10_1kResidualWord hm w) = 1) := by
    omega
  rcases hcases with ⟨hspecial, hresidual⟩ | ⟨hspecial, hresidual⟩
  · exact Or.inl ⟨hspecial, (hammingDist_eq_zero.mp hresidual)⟩
  · exact Or.inr ⟨(hammingDist_eq_zero.mp hspecial), hresidual⟩

/-- Flipping one residual coordinate gives an ordinary cube edge. -/
theorem p10_1kResidualFlipVertex_adjacent {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (j : Fin (n - m)) :
    (cube n).Adj v (p10_1kResidualFlipVertex hm v j) := by
  change hammingDist v (p10_1kResidualFlipVertex hm v j) = 1
  rw [p10_1kSliceHammingDist hm v (p10_1kResidualFlipVertex hm v j),
    p10_1kResidualFlipVertex_specialSlice,
    p10_1kResidualFlipVertex_residualWord,
    p10_1kFlipCoordinate_hammingDist]
  simp

private theorem p10_1k_even_iff_not_even_succ (r : ℕ) :
    Even r ↔ ¬ Even (r + 1) := by
  constructor
  · intro hr hsucc
    exact (Nat.not_even_iff_odd.mpr hr.add_one) hsucc
  · intro hsucc
    rcases Nat.even_or_odd r with hr | hr
    · exact hr
    · exact (hsucc hr.add_one).elim

/-- Adjacent cube vertices lie in opposite parity classes. -/
private theorem p10_1k_evenRole_flip_of_hammingDist_one {n : ℕ}
    {u v : Fin n → Bool} (h : hammingDist u v = 1) :
    IsEvenRole u ↔ ¬ IsEvenRole v := by
  classical
  have hone : (Finset.univ.filter fun i : Fin n => u i ≠ v i).card = 1 := by
    simpa [hammingDist] using h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
  have hi_mem : i ∈ Finset.univ.filter (fun j : Fin n => u j ≠ v j) := by
    rw [hi]
    simp
  have hdiff : u i ≠ v i := (Finset.mem_filter.mp hi_mem).2
  have hsame : ∀ j, j ≠ i → u j = v j := by
    intro j hji
    by_contra hne
    have hj_mem : j ∈ Finset.univ.filter (fun t : Fin n => u t ≠ v t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hi] at hj_mem
    exact hji (Finset.mem_singleton.mp hj_mem)
  let A := Finset.univ.filter (fun j : Fin n => u j = true)
  let B := Finset.univ.filter (fun j : Fin n => v j = true)
  have hbit : (u i = false ∧ v i = true) ∨ (u i = true ∧ v i = false) := by
    cases hu : u i <;> cases hv : v i <;> simp_all
  rcases hbit with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hset : B = insert i A := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B, hu, hv]
      · have hsame' := hsame j hji
        simp [A, B, hji, hsame']
    have hi_notA : i ∉ A := by simp [A, hu]
    have hcard : B.card = A.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hi_notA]
    change Even A.card ↔ ¬ Even B.card
    rw [hcard]
    exact p10_1k_even_iff_not_even_succ A.card
  · have hset : A = insert i B := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B, hu, hv]
      · have hsame' := hsame j hji
        simp [A, B, hji, hsame']
    have hi_notB : i ∉ B := by simp [B, hv]
    have hcard : A.card = B.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hi_notB]
    change Even A.card ↔ ¬ Even B.card
    rw [hcard]
    exact Nat.even_add_one

/-- Flipping one special coordinate gives an ordinary cube edge. -/
theorem p10_1kSpecialFlipVertex_adjacent {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (i : Fin m) :
    (cube n).Adj v (p10_1kSpecialFlipVertex hm v i) := by
  change hammingDist v (p10_1kSpecialFlipVertex hm v i) = 1
  rw [p10_1kSliceHammingDist hm v (p10_1kSpecialFlipVertex hm v i),
    p10_1kSpecialFlipVertex_specialSlice,
    p10_1kSpecialFlipVertex_residualWord,
    p10_1kFlipCoordinate_hammingDist]
  simp

/-- A word at Hamming distance one is obtained by flipping one coordinate. -/
private theorem p10_1k_flipCoordinate_of_hammingDist_one {d : ℕ}
    (s t : Fin d → Bool) (h : hammingDist s t = 1) :
    ∃ j : Fin d, t = p10_1kFlipCoordinate s j := by
  classical
  have hcard : (Finset.univ.filter (fun i : Fin d => s i ≠ t i)).card = 1 := by
    simpa [hammingDist] using h
  obtain ⟨j, hfilter⟩ := Finset.card_eq_one.mp hcard
  refine ⟨j, ?_⟩
  funext k
  have hk : s k ≠ t k ↔ k = j := by
    have hmem : k ∈ Finset.univ.filter (fun i : Fin d => s i ≠ t i) ↔ k = j := by
      rw [hfilter]
      simp
    simpa using hmem
  by_cases hkj : k = j
  · subst k
    have hne : s j ≠ t j := hk.2 rfl
    cases hs : s j <;> cases ht : t j <;> simp_all [p10_1kFlipCoordinate]
  · have heq : s k = t k := by
      by_contra hne
      exact hkj (hk.1 hne)
    simp [p10_1kFlipCoordinate, hkj, heq]

/-- The projected center site attached to a cube vertex. -/
noncomputable def p10_1kProjectedVertex {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) :
  (Fin m → Bool) × (Fin (n - m) → Bool) :=
  (p10_1kSpecialSlice hm v,
    p10_1k_projectedWord (n - m) (p10_1kResidualWord hm v))

/-- A residual-coordinate cube edge changes only its projected residual site. -/
theorem p10_1kProjectedVertex_residualFlipVertex {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (j : Fin (n - m)) :
    p10_1kProjectedVertex hm (p10_1kResidualFlipVertex hm v j) =
      (p10_1kSpecialSlice hm v,
        p10_1k_projectedWord (n - m)
          (p10_1kFlipCoordinate (p10_1kResidualWord hm v) j)) := by
  simp [p10_1kProjectedVertex, p10_1kResidualFlipVertex_specialSlice,
    p10_1kResidualFlipVertex_residualWord]

/-- A special-coordinate edge moves to the adjacent special slice and keeps
the projected residual site fixed. -/
theorem p10_1kProjectedVertex_specialFlipVertex {n m : ℕ} (hm : m ≤ n)
    (v : Fin n → Bool) (i : Fin m) :
    p10_1kProjectedVertex hm (p10_1kSpecialFlipVertex hm v i) =
      (p10_1kFlipCoordinate (p10_1kSpecialSlice hm v) i,
        p10_1k_projectedWord (n - m) (p10_1kResidualWord hm v)) := by
  simp [p10_1kProjectedVertex, p10_1kSpecialFlipVertex_specialSlice,
    p10_1kSpecialFlipVertex_residualWord]

/-- Every cube edge either changes one special coordinate or keeps the slice
fixed and moves the projected residual site by at most three bits. -/
theorem p10_1k_projectedVertex_edge {n m : ℕ} (hm : m ≤ n)
    {v w : Fin n → Bool} (hadj : (cube n).Adj v w) :
    (hammingDist (p10_1kSpecialSlice hm v) (p10_1kSpecialSlice hm w) = 1 ∧
      p10_1k_projectedWord (n - m) (p10_1kResidualWord hm v) =
        p10_1k_projectedWord (n - m) (p10_1kResidualWord hm w)) ∨
    (p10_1kSpecialSlice hm v = p10_1kSpecialSlice hm w ∧
      hammingDist (p10_1k_projectedWord (n - m) (p10_1kResidualWord hm v))
        (p10_1k_projectedWord (n - m) (p10_1kResidualWord hm w)) ≤ 3) := by
  rcases p10_1k_adjacentCoordinates_split hm hadj with hspecial | hresidual
  · exact Or.inl ⟨hspecial.1, congrArg (p10_1k_projectedWord (n - m)) hspecial.2⟩
  · obtain ⟨j, hflip⟩ := p10_1k_flipCoordinate_of_hammingDist_one
      (p10_1kResidualWord hm v) (p10_1kResidualWord hm w) hresidual.2
    refine Or.inr ⟨hresidual.1, ?_⟩
    rw [hflip]
    exact p10_1k_projectedWord_flip_hammingDist_le_three (n - m)
      (p10_1kResidualWord hm v) j

/-- An edge that stays in its special slice flips one residual coordinate. -/
theorem p10_1k_adjacent_residual_same_slice_flip {n m : ℕ} (hm : m ≤ n)
    {v w : Fin n → Bool} (hadj : (cube n).Adj v w)
    (hslice : p10_1kSpecialSlice hm v = p10_1kSpecialSlice hm w) :
    ∃ j : Fin (n - m),
      p10_1kResidualWord hm w =
        p10_1kFlipCoordinate (p10_1kResidualWord hm v) j := by
  rcases p10_1k_adjacentCoordinates_split hm hadj with hspecial | hresidual
  · have hdist := hspecial.1
    rw [hslice] at hdist
    simp at hdist
  · obtain ⟨j, hflip⟩ := p10_1k_flipCoordinate_of_hammingDist_one
      (p10_1kResidualWord hm v) (p10_1kResidualWord hm w) hresidual.2
    exact ⟨j, hflip⟩

abbrev P10_1kOddRole (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}
abbrev P10_1kEvenRole (n : ℕ) := {v : CubeVertex n // IsEvenRole v}
abbrev P10_1kProjectedSite (n m : ℕ) :=
  (Fin m → Bool) × (Fin (n - m) → Bool)

/-- The odd neighbor of an even role obtained by flipping one coordinate. -/
def p10_1kFlipOddRole {n : ℕ} (a : P10_1kEvenRole n) (j : Fin n) :
    P10_1kOddRole n := by
  refine ⟨p10_1kFlipCoordinate a.1 j, ?_⟩
  have hadj : (cube n).Adj a.1 (p10_1kFlipCoordinate a.1 j) := by
    change hammingDist a.1 (p10_1kFlipCoordinate a.1 j) = 1
    exact p10_1kFlipCoordinate_hammingDist n a.1 j
  exact (p10_1k_evenRole_flip_of_hammingDist_one hadj).mp a.2

/-- The coordinate flip defining an odd role is an adjacent cube vertex. -/
theorem p10_1kFlipOddRole_adjacent {n : ℕ} (a : P10_1kEvenRole n)
    (j : Fin n) :
    (cube n).Adj a.1 (p10_1kFlipOddRole a j).1 := by
  change hammingDist a.1 (p10_1kFlipCoordinate a.1 j) = 1
  exact p10_1kFlipCoordinate_hammingDist n a.1 j

/-- Every coordinate gives a distinct odd neighbor of a fixed even role. -/
theorem p10_1kFlipOddRole_injective {n : ℕ} (a : P10_1kEvenRole n) :
    Function.Injective (p10_1kFlipOddRole a) := by
  intro i j hij
  have hword : p10_1kFlipCoordinate a.1 i = p10_1kFlipCoordinate a.1 j :=
    congrArg Subtype.val hij
  apply Fin.ext
  by_contra hne
  have hbit := congrFun hword i
  simp [p10_1kFlipCoordinate] at hbit
  exact hne (congrArg Fin.val hbit)

/-- Every odd neighbor of an even role is the flip of a unique coordinate. -/
theorem p10_1kFlipOddRole_surjective {n : ℕ} (a : P10_1kEvenRole n)
    (b : P10_1kOddRole n) (hadj : (cube n).Adj a.1 b.1) :
    ∃ j : Fin n, p10_1kFlipOddRole a j = b := by
  have hdist : hammingDist a.1 b.1 = 1 := by exact hadj
  obtain ⟨j, hflip⟩ := p10_1k_flipCoordinate_of_hammingDist_one a.1 b.1 hdist
  refine ⟨j, ?_⟩
  apply Subtype.ext
  exact hflip.symm

/-- The ordinary odd neighbors of an even role, indexed by its `n` cube
coordinates. -/
noncomputable def p10_1kStarNeighborEquiv {n : ℕ} (a : P10_1kEvenRole n) :
    Fin n ≃ {b : P10_1kOddRole n // (cube n).Adj a.1 b.1} := by
  classical
  exact {
    toFun := fun j => ⟨p10_1kFlipOddRole a j, p10_1kFlipOddRole_adjacent a j⟩
    invFun := fun b => Classical.choose
      (p10_1kFlipOddRole_surjective a b.1 b.2)
    left_inv := by
      intro j
      apply p10_1kFlipOddRole_injective a
      exact Classical.choose_spec
        (p10_1kFlipOddRole_surjective a (p10_1kFlipOddRole a j)
          (p10_1kFlipOddRole_adjacent a j))
    right_inv := by
      intro b
      apply Subtype.ext
      exact Classical.choose_spec (p10_1kFlipOddRole_surjective a b.1 b.2) }

/-- A cube star has exactly `n` odd neighbors. -/
theorem p10_1kStarNeighbor_card {n : ℕ} (a : P10_1kEvenRole n)
    [Fintype (P10_1kOddRole n)]
    [DecidablePred (fun b : P10_1kOddRole n => (cube n).Adj a.1 b.1)] :
    Fintype.card {b : P10_1kOddRole n // (cube n).Adj a.1 b.1} = n := by
  classical
  calc
    Fintype.card {b : P10_1kOddRole n // (cube n).Adj a.1 b.1} =
        Fintype.card (Fin n) := Fintype.card_congr (p10_1kStarNeighborEquiv a).symm
    _ = n := by simp

/-- At one even cube vertex, labels indexed by its `n` coordinates and hit by
one positive-mass atom admit a normalized row supported on every incident
edge. -/
theorem p10_1k_starRow_of_commonHitAtom {n N : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (a : P10_1kEvenRole n) (μ : Law N) (lab : Fin n → Fin N)
    (x : Fin N) (hx : 0 < μ.w x)
    (hhit : ∀ i, Hits E G x (lab i)) :
    ∃ row : Fin N → ℝ,
      (∀ y, 0 ≤ row y) ∧
      (∑ y, row y = 1) ∧
      (∀ y, row y ≠ 0 → ∀ b : P10_1kOddRole n,
        ∀ hadj : (cube n).Adj a.1 b.1,
          Hits E G y (lab ((p10_1kStarNeighborEquiv a).symm ⟨b, hadj⟩))) := by
  classical
  have hmass := p10_1kCommonNeighborSet_mass_pos_of_atom E G μ lab x hx hhit
  have hsupport := p10_1kCommonNeighborSubrow_support E G lab μ
  have hsum := p10_1kCommonNeighborSubrow_sum E G lab μ
  refine ⟨p10_1kCommonNeighborSubrow E G lab μ, hsupport.1, ?_, ?_⟩
  · simpa [hmass] using hsum
  · intro y hy b hadj
    exact hsupport.2 y hy ((p10_1kStarNeighborEquiv a).symm ⟨b, hadj⟩)

/-- A successful fixed-list outcome and one positive-mass tuple entry construct
an injective local labeling of an even star together with its normalized row. -/
theorem p10_1k_successfulFixedList_starRows {n N r k : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ} {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (μ : Fin r → Law N) (gain : ℝ) (W : Fin r → Fin k → Fin N)
    (hgood : ¬ fixedListFailure E G (p10_1kClusterPrior data)
      data.D μ gain W)
      (hExp : (n : ℝ) ≤ Real.exp ((n : ℝ) ^ ζ - (k : ℝ) * (r : ℝ)))
    (a : P10_1kEvenRole n) (b : Fin r) (i : Fin k)
    (hweight : 0 < (μ b).w (W b i)) :
    ∃ j, 0 < data.lam j ∧
      ∃ lab : Fin n → Fin N, Function.Injective lab ∧
        (∀ t, 0 < (data.D j).w (lab t)) ∧
        (∀ t b' i', Hits E G (W b' i') (lab t)) ∧
        ∃ row : Fin N → ℝ,
          (∀ y, 0 ≤ row y) ∧
          (∑ y, row y = 1) ∧
          (∀ y, row y ≠ 0 → ∀ b' : P10_1kOddRole n,
            ∀ hadj : (cube n).Adj a.1 b'.1,
              Hits E G y (lab ((p10_1kStarNeighborEquiv a).symm ⟨b', hadj⟩))) := by
  obtain ⟨j, hprior, lab, hinj, hsupport, hhit⟩ :=
    p10_1k_successfulFixedList_injective_labels E G ζ
      (p10_1kClusterPrior data) data.D μ gain W hgood data.D_atom hExp
  have hstarHit : ∀ t : Fin n, Hits E G (W b i) (lab t) :=
    fun t => hhit t b i
  obtain ⟨row, hnonneg, hsum, hedge⟩ :=
    p10_1k_starRow_of_commonHitAtom E G a (μ b) lab (W b i) hweight hstarHit
  exact ⟨j, hprior, lab, hinj, hsupport, hhit, row, hnonneg, hsum, hedge⟩

/-- A failure-probability bound below one produces a positive-weight tuple
array and the associated local injective star labeling and row. -/
theorem p10_1k_clusterData_localStar_of_failure_bound {n N r k : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ} {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (μ : Fin r → Law N) (gain ε : ℝ)
    (hfail : (p10_1kTupleArrayLaw (k := k) μ).pr
      (fixedListFailure (k := k) (q := data.K) E G
        (p10_1kClusterPrior data) data.D μ gain) ≤ ε)
    (hε : ε < 1)
    (hExp : (n : ℝ) ≤ Real.exp ((n : ℝ) ^ ζ - (k : ℝ) * (r : ℝ)))
    (a : P10_1kEvenRole n) (b : Fin r) (i : Fin k) :
    ∃ W, 0 < tupleArrayWeight (k := k) μ W ∧
      ∃ j, 0 < data.lam j ∧
        ∃ lab : Fin n → Fin N, Function.Injective lab ∧
          (∀ t, 0 < (data.D j).w (lab t)) ∧
          (∀ t b' i', Hits E G (W b' i') (lab t)) ∧
          ∃ row : Fin N → ℝ,
            (∀ y, 0 ≤ row y) ∧
            (∑ y, row y = 1) ∧
            (∀ y, row y ≠ 0 → ∀ b' : P10_1kOddRole n,
              ∀ hadj : (cube n).Adj a.1 b'.1,
                Hits E G y (lab ((p10_1kStarNeighborEquiv a).symm ⟨b', hadj⟩))) := by
  obtain ⟨W, hgood, hW⟩ := p10_1k_fixedList_successful_tuple_exists
    E G (p10_1kClusterPrior data) data.D μ gain ε hfail hε
  have hweight := p10_1k_tupleArrayWeight_entries_pos μ W hW
  obtain ⟨j, hprior, lab, hinj, hsupport, hhit, row, hnonneg, hsum, hedge⟩ :=
    p10_1k_successfulFixedList_starRows data μ gain W hgood hExp a b i (hweight b i)
  exact ⟨W, hW, j, hprior, lab, hinj, hsupport, hhit, row, hnonneg, hsum, hedge⟩

/-- The complete local output for one even star after a successful-list test. -/
def P10_1kLocalStarWitness {n N r k : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {ζ δ : ℝ} {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (μ : Fin r → Law N) (a : P10_1kEvenRole n) : Prop :=
  ∃ W, 0 < tupleArrayWeight (k := k) μ W ∧
    ∃ j, 0 < data.lam j ∧
      ∃ lab : Fin n → Fin N, Function.Injective lab ∧
        (∀ t, 0 < (data.D j).w (lab t)) ∧
        (∀ t b i, Hits E G (W b i) (lab t)) ∧
        ∃ row : Fin N → ℝ,
          (∀ y, 0 ≤ row y) ∧
          (∑ y, row y = 1) ∧
          (∀ y, row y ≠ 0 → ∀ b : P10_1kOddRole n,
            ∀ hadj : (cube n).Adj a.1 b.1,
              Hits E G y (lab ((p10_1kStarNeighborEquiv a).symm ⟨b, hadj⟩)))

/-- For every sufficiently large dimension, every selected PCluster patch and
one-shot discrepancy instance has a local successful row construction at each
even star. -/
theorem p10_1k_clusterData_localStars_eventually
    (hfixed : P10_1cFixedListTest) (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
        (X Y A B : Finset (Fin N))
        (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B),
        A ⊆ X → B ⊆ Y →
        DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
        ∀ a : P10_1kEvenRole n,
          P10_1kLocalStarWitness (k := p10_1kTupleListLength n δ) data
            (fun _ : Fin (p10_1kFixedListBlockCount n δ) => data.μ) a := by
  have hfixedEvent := p10_1k_clusterData_fixedList_probability_eventually
    hfixed η₀ ζ δ hη₀ hζ hδ hδsmall
  have hcountEvent := p10_1k_fixedList_counts_positive_eventually δ hδ
  have hminOuter : min (min η₀ ζ) 1 ≤ min (min 1 ζ) 1 := by
    have hleOne : min (min η₀ ζ) 1 ≤ 1 := min_le_right _ _
    have hleZeta : min (min η₀ ζ) 1 ≤ ζ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hleMin : min (min η₀ ζ) 1 ≤ min 1 ζ := le_min hleOne hleZeta
    have heq : min (min 1 ζ) 1 = min 1 ζ := min_eq_left (min_le_left _ _)
    simpa [heq] using hleMin
  have hδsmall' : δ < min (min 1 ζ) 1 / 2000 :=
    lt_of_lt_of_le hδsmall
      (div_le_div_of_nonneg_right hminOuter (by norm_num))
  have hExpEvent := p10_1k_fixedList_hit_support_scale_eventually ζ δ hζ hδ hδsmall'
  filter_upwards [hfixedEvent, hcountEvent, hExpEvent]
    with n hfixedN hcounts hExpN
  let r : ℕ := p10_1kFixedListBlockCount n δ
  let k : ℕ := p10_1kTupleListLength n δ
  let gain : ℝ := (n : ℝ) ^ (-δ)
  have hrpos : 0 < r := hcounts.2.1
  have hkpos : 0 < k := hcounts.2.2
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hgain : 0 < gain := Real.rpow_pos_of_pos hnreal _
  have hExp : (n : ℝ) ≤ Real.exp ((n : ℝ) ^ ζ - (k : ℝ) * (r : ℝ)) := by
    simpa [r, k, p10_1kFixedListBlockCount, p10_1kTupleListLength] using hExpN
  intro N E G X Y A B data hAX hBY hdisc
  obtain ⟨c₅, hc₅, hfail⟩ := hfixedN N E G X Y A B data hAX hBY hdisc
  have hepsilon : Real.exp (-c₅ * gain ^ 2 * (k : ℝ)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hpos : 0 < c₅ * gain ^ 2 * (k : ℝ) := by positivity
    nlinarith [hpos]
  intro a
  let b : Fin r := ⟨0, hrpos⟩
  let i : Fin k := ⟨0, hkpos⟩
  have hfail' : (p10_1kTupleArrayLaw (k := k)
      (fun _ : Fin r => data.μ)).pr
      (fixedListFailure (k := k) (q := data.K) E G
        (p10_1kClusterPrior data) data.D (fun _ : Fin r => data.μ) gain) ≤
      Real.exp (-c₅ * gain ^ 2 * (k : ℝ)) := by
    simpa [r, k, gain, p10_1kFixedListBlockCount, p10_1kTupleListLength] using hfail
  have hlocal := p10_1k_clusterData_localStar_of_failure_bound data
    (fun _ : Fin r => data.μ) gain (Real.exp (-c₅ * gain ^ 2 * (k : ℝ)))
    hfail' hepsilon hExp a b i
  simpa [P10_1kLocalStarWitness] using hlocal

/-- The projected even sites in one fixed special slice. -/
noncomputable def p10_1kProjectedEvenSites {n m : ℕ} (hm : m ≤ n)
    (z : Fin m → Bool) : Finset (Fin (n - m) → Bool) := by
  classical
  exact (Finset.univ.filter fun a : P10_1kEvenRole n =>
    p10_1kSpecialSlice hm a.1 = z).image fun a =>
      p10_1k_projectedWord (n - m) (p10_1kResidualWord hm a.1)

/-- Every actual even role in the slice contributes its projected residual
site to the height device's site set. -/
theorem p10_1kProjectedEvenRole_mem_sites {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) :
    p10_1k_projectedWord (n - m) (p10_1kResidualWord hm a.1) ∈
      p10_1kProjectedEvenSites hm (p10_1kSpecialSlice hm a.1) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩

/-- The odd role at the other end of a chosen special-coordinate edge. -/
noncomputable def p10_1kSpecialFlipOddRole {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (i : Fin m) : P10_1kOddRole n :=
  ⟨p10_1kSpecialFlipVertex hm a.1 i, by
    have hadj := p10_1kSpecialFlipVertex_adjacent hm a.1 i
    exact (p10_1k_evenRole_flip_of_hammingDist_one hadj).mp a.2⟩

/-- The projected site of a special odd neighbor is in the adjacent special
slice and keeps the residual component fixed. -/
theorem p10_1kSpecialFlipOddRole_site {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (i : Fin m) :
    p10_1kProjectedVertex hm (p10_1kSpecialFlipOddRole hm a i).1 =
      (p10_1kFlipCoordinate (p10_1kSpecialSlice hm a.1) i,
        p10_1k_projectedWord (n - m) (p10_1kResidualWord hm a.1)) := by
  simpa [p10_1kSpecialFlipOddRole] using
    p10_1kProjectedVertex_specialFlipVertex hm a.1 i

/-- Distinct special coordinates give distinct odd roles at a fixed even
center. -/
theorem p10_1kSpecialFlipOddRole_injective {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) :
    Function.Injective (p10_1kSpecialFlipOddRole hm a) := by
  intro i j hrole
  have hslice := congrArg (p10_1kSpecialSlice hm) (congrArg Subtype.val hrole)
  simp only [p10_1kSpecialFlipOddRole] at hslice
  rw [p10_1kSpecialFlipVertex_specialSlice,
    p10_1kSpecialFlipVertex_specialSlice] at hslice
  by_contra hij
  have hbit := congrFun hslice i
  simp [p10_1kFlipCoordinate, hij] at hbit

/-- Residual odd neighbors of an even role that lie in a specified projected
site in the same special slice. -/
noncomputable def p10_1kResidualIncidentOddGroup {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (q : P10_1kProjectedSite n m) : Finset (P10_1kOddRole n) := by
  classical
  exact Finset.univ.filter fun b =>
    p10_1kSpecialSlice hm b.1 = p10_1kSpecialSlice hm a.1 ∧
      (cube n).Adj a.1 b.1 ∧ p10_1kProjectedVertex hm b.1 = q

/-- Odd neighbors incident to an even role in a different special slice. -/
noncomputable def p10_1kSpecialIncidentOddGroup {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (q : P10_1kProjectedSite n m) : Finset (P10_1kOddRole n) := by
  classical
  exact Finset.univ.filter fun b =>
    (cube n).Adj a.1 b.1 ∧ p10_1kProjectedVertex hm b.1 = q

/-- Every special-slice neighbor group contains at most one odd role. -/
theorem p10_1k_specialIncidentOddGroup_card_le_one {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (q : P10_1kProjectedSite n m)
    (hq : q.1 ≠ p10_1kSpecialSlice hm a.1) :
    Fintype.card {b : P10_1kOddRole n // b ∈ p10_1kSpecialIncidentOddGroup hm a q} ≤ 1 := by
  classical
  apply Fintype.card_le_one_iff_subsingleton.mpr
  refine ⟨?_⟩
  intro x y
  have hx := (Finset.mem_filter.mp x.2).2
  have hy := (Finset.mem_filter.mp y.2).2
  have hsliceX : p10_1kSpecialSlice hm x.1.1 = q.1 := by
    simpa [p10_1kProjectedVertex] using congrArg Prod.fst hx.2
  have hsliceY : p10_1kSpecialSlice hm y.1.1 = q.1 := by
    simpa [p10_1kProjectedVertex] using congrArg Prod.fst hy.2
  rcases p10_1k_adjacentCoordinates_split hm hx.1 with hspecialX | hresidualX
  · rcases p10_1k_adjacentCoordinates_split hm hy.1 with hspecialY | hresidualY
    · apply Subtype.ext
      apply Subtype.ext
      apply (p10_1kSliceWordEquiv hm).injective
      apply Prod.ext
      · exact hsliceX.trans hsliceY.symm
      · calc
          p10_1kResidualWord hm x.1.1 = p10_1kResidualWord hm a.1 := hspecialX.2.symm
          _ = p10_1kResidualWord hm y.1.1 := hspecialY.2
    · have hqeq : q.1 = p10_1kSpecialSlice hm a.1 :=
        hsliceY.symm.trans hresidualY.1.symm
      exact (hq hqeq).elim
  · have hqeq : q.1 = p10_1kSpecialSlice hm a.1 :=
      hsliceX.symm.trans hresidualX.1.symm
    exact (hq hqeq).elim

/-- The odd role at the other end of a chosen residual edge from an even role. -/
noncomputable def p10_1kResidualFlipOddRole {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (j : Fin (n - m)) : P10_1kOddRole n :=
  ⟨p10_1kResidualFlipVertex hm a.1 j, by
    have hadj := p10_1kResidualFlipVertex_adjacent hm a.1 j
    exact (p10_1k_evenRole_flip_of_hammingDist_one hadj).mp a.2⟩

/-- The projected site of a residual odd neighbor is the corresponding local
projected residual neighbor in the same special slice. -/
theorem p10_1kResidualFlipOddRole_site {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (j : Fin (n - m)) :
    p10_1kProjectedVertex hm (p10_1kResidualFlipOddRole hm a j).1 =
      (p10_1kSpecialSlice hm a.1,
        p10_1k_projectedWord (n - m)
          (p10_1kFlipCoordinate (p10_1kResidualWord hm a.1) j)) := by
  simpa [p10_1kResidualFlipOddRole] using
    p10_1kProjectedVertex_residualFlipVertex hm a.1 j

/-- Every residual odd group in a projected site injects into the fiber of
residual coordinate flips projecting to that site's residual word. -/
theorem p10_1k_residualIncidentOddGroup_card_le_fiber {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (q : P10_1kProjectedSite n m)
    (_hq : q.1 = p10_1kSpecialSlice hm a.1) :
    Fintype.card {b : P10_1kOddRole n // b ∈ p10_1kResidualIncidentOddGroup hm a q} ≤
      Fintype.card {j : Fin (n - m) //
        p10_1k_projectedWord (n - m)
          (p10_1kFlipCoordinate (p10_1kResidualWord hm a.1) j) = q.2} := by
  classical
  let group := p10_1kResidualIncidentOddGroup hm a q
  let fiber := {j : Fin (n - m) //
    p10_1k_projectedWord (n - m)
      (p10_1kFlipCoordinate (p10_1kResidualWord hm a.1) j) = q.2}
  have hdata (b : {b : P10_1kOddRole n // b ∈ group}) :
      p10_1kSpecialSlice hm b.1.1 = p10_1kSpecialSlice hm a.1 ∧
        (cube n).Adj a.1 b.1.1 ∧ p10_1kProjectedVertex hm b.1.1 = q :=
    (Finset.mem_filter.mp b.2).2
  let chosenCoordinate (b : {b : P10_1kOddRole n // b ∈ group}) : Fin (n - m) :=
    Classical.choose (p10_1k_adjacent_residual_same_slice_flip hm
      (hdata b).2.1 (hdata b).1.symm)
  have hchosen (b : {b : P10_1kOddRole n // b ∈ group}) :
      p10_1kResidualWord hm b.1.1 =
        p10_1kFlipCoordinate (p10_1kResidualWord hm a.1) (chosenCoordinate b) := by
    exact Classical.choose_spec (p10_1k_adjacent_residual_same_slice_flip hm
      (hdata b).2.1 (hdata b).1.symm)
  let f : {b : P10_1kOddRole n // b ∈ group} → fiber := fun b =>
    ⟨chosenCoordinate b, by
      have hsite := congrArg Prod.snd (hdata b).2.2
      change p10_1k_projectedWord (n - m) (p10_1kResidualWord hm b.1.1) = q.2 at hsite
      rw [hchosen b] at hsite
      exact hsite⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply (p10_1kSliceWordEquiv hm).injective
    have hxmem := hdata x
    have hymem := hdata y
    have hcoord : chosenCoordinate x = chosenCoordinate y :=
      congrArg Subtype.val hxy
    have hres : p10_1kResidualWord hm x.1.1 = p10_1kResidualWord hm y.1.1 := by
      calc
        p10_1kResidualWord hm x.1.1 =
            p10_1kFlipCoordinate (p10_1kResidualWord hm a.1) (chosenCoordinate x) :=
          hchosen x
        _ = p10_1kFlipCoordinate (p10_1kResidualWord hm a.1) (chosenCoordinate y) := by
          rw [hcoord]
        _ = p10_1kResidualWord hm y.1.1 := (hchosen y).symm
    apply Prod.ext
    · calc
        p10_1kSpecialSlice hm x.1.1 = p10_1kSpecialSlice hm a.1 := hxmem.1
        _ = p10_1kSpecialSlice hm y.1.1 := hymem.1.symm
    · exact hres
  exact Fintype.card_le_of_injective f hf

/-- Distinct residual coordinates give distinct odd roles at a fixed even
center. -/
theorem p10_1kResidualFlipOddRole_injective {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) :
    Function.Injective (p10_1kResidualFlipOddRole hm a) := by
  intro j k hrole
  have hword := congrArg Subtype.val hrole
  have hres :
      p10_1kFlipCoordinate (p10_1kResidualWord hm a.1) j =
        p10_1kFlipCoordinate (p10_1kResidualWord hm a.1) k := by
    simpa only [p10_1kResidualFlipOddRole,
      p10_1kResidualFlipVertex_residualWord] using
      congrArg (p10_1kResidualWord hm) hword
  by_contra hjk
  have hbit := congrFun hres j
  simp [p10_1kFlipCoordinate, hjk] at hbit

/-- Residual odd roles at the same projected site come from the same chunk. -/
theorem p10_1kResidualFlipOddRole_same_chunk {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (j k : Fin (n - m))
    (heq : p10_1kProjectedVertex hm (p10_1kResidualFlipOddRole hm a j).1 =
      p10_1kProjectedVertex hm (p10_1kResidualFlipOddRole hm a k).1) :
    (p10_1k_chunkCoordinateEquiv (n - m) j).1 =
      (p10_1k_chunkCoordinateEquiv (n - m) k).1 := by
  apply p10_1k_projectedNeighbors_same_chunk_of_eq
  have hres := congrArg Prod.snd heq
  simpa only [p10_1kResidualFlipOddRole_site] using hres

/-- A nonempty global projected-neighbor fiber injects into the local neighbor
fiber of its unique changed chunk. -/
theorem p10_1k_projectedNeighborFiber_card_le_chunk (d : ℕ) (s t : Fin d → Bool)
    (hne : ∃ j : Fin d,
      p10_1k_projectedWord d (p10_1kFlipCoordinate s j) = t) :
    ∃ i : Fin d.bitIndices.length,
      (∃ g : P10_1kChunkGroup d i,
        projectedNeighbor (p10_1k_chunkedWord d s i) g =
          p10_1k_chunkedWord d t i) ∧
      Fintype.card {j : Fin d //
        p10_1k_projectedWord d (p10_1kFlipCoordinate s j) = t} ≤
      Fintype.card {g : P10_1kChunkGroup d i //
        projectedNeighbor (p10_1k_chunkedWord d s i) g =
          p10_1k_chunkedWord d t i} := by
  classical
  obtain ⟨j₀, hj₀⟩ := hne
  let e := p10_1k_chunkCoordinateEquiv d
  let i := (e j₀).1
  let LocalFiber := fun k : Fin d.bitIndices.length =>
    {g : P10_1kChunkGroup d k //
      projectedNeighbor (p10_1k_chunkedWord d s k) g =
        p10_1k_chunkedWord d t k}
  let f : {j : Fin d //
      p10_1k_projectedWord d (p10_1kFlipCoordinate s j) = t} →
      Σ k : Fin d.bitIndices.length, LocalFiber k := fun x =>
    ⟨(e x.1).1, ⟨(e x.1).2, by
      have hglobal := congrArg (p10_1k_chunkedWord d) x.2
      have hsite := congrFun hglobal (e x.1).1
      rw [p10_1k_projectedWord_flip_changed_chunk d s x.1] at hsite
      exact hsite⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hcoord : e x.1 = e y.1 := by
      have hcoord := congrArg
        (fun z : Σ k : Fin d.bitIndices.length, LocalFiber k =>
          (⟨z.1, z.2.1⟩ : P10_1kChunkCoordinate d)) hxy
      simpa [f] using hcoord
    exact e.injective hcoord
  have hempty (k : Fin d.bitIndices.length) (hk : k ≠ i) : IsEmpty (LocalFiber k) := by
    refine ⟨?_⟩
    intro x
    have htarget : p10_1k_chunkedWord d t k =
        p10_1k_chunkedWord d
          (p10_1k_projectedWord d (p10_1kFlipCoordinate s j₀)) k := by
      exact (congrFun (congrArg (p10_1k_chunkedWord d) hj₀) k).symm
    have hunchanged := p10_1k_projectedWord_flip_unchanged_chunk d s j₀ k hk
    have hbad : projectedNeighbor (p10_1k_chunkedWord d s k) x.1 =
        chunkProject (p10_1k_chunkedWord d s k) := by
      calc
        projectedNeighbor (p10_1k_chunkedWord d s k) x.1 =
            p10_1k_chunkedWord d t k := x.2
        _ = p10_1k_chunkedWord d
            (p10_1k_projectedWord d (p10_1kFlipCoordinate s j₀)) k := htarget
        _ = chunkProject (p10_1k_chunkedWord d s k) := hunchanged
    exact p10_1k_projectedNeighbor_ne_projectedCenter
      (fun g => p10_1k_chunkGroup_two_add d k g)
      (p10_1k_chunkedWord d s k) x.1 hbad
  have hcardZero (k : Fin d.bitIndices.length) (hk : k ≠ i) :
      Fintype.card (LocalFiber k) = 0 :=
    Fintype.card_eq_zero_iff.mpr (hempty k hk)
  have hsum : (∑ k : Fin d.bitIndices.length, Fintype.card (LocalFiber k)) =
      Fintype.card (LocalFiber i) := by
    exact Fintype.sum_eq_single i (fun k hk => by rw [hcardZero k hk])
  have hcardSigma : Fintype.card (Σ k : Fin d.bitIndices.length, LocalFiber k) =
      Fintype.card (LocalFiber i) := by
    rw [Fintype.card_sigma]
    exact hsum
  refine ⟨i, ?_, ?_⟩
  · refine ⟨(e j₀).2, ?_⟩
    have hglobal := congrArg (p10_1k_chunkedWord d) hj₀
    have hsite := congrFun hglobal i
    rw [p10_1k_projectedWord_flip_changed_chunk d s j₀] at hsite
    exact hsite
  · calc
      Fintype.card {j : Fin d //
          p10_1k_projectedWord d (p10_1kFlipCoordinate s j) = t} ≤
          Fintype.card (Σ k : Fin d.bitIndices.length, LocalFiber k) :=
        Fintype.card_le_of_injective f hf
      _ = Fintype.card (LocalFiber i) := hcardSigma

/-- The ordinary neighbor multiplicity is two off the center-syndrome case;
the exceptional fiber is bounded by the size of its chunk. -/
theorem p10_1k_projectedNeighborFiber_card_bound (d : ℕ) (s t : Fin d → Bool)
    (hne : ∃ j : Fin d,
      p10_1k_projectedWord d (p10_1kFlipCoordinate s j) = t) :
    ∃ i : Fin d.bitIndices.length,
      Fintype.card {j : Fin d //
        p10_1k_projectedWord d (p10_1kFlipCoordinate s j) = t} ≤
        if chunkSyndrome (p10_1k_chunkedWord d s i) = 0 then
          Fintype.card (P10_1kChunkGroup d i) else 2 := by
  obtain ⟨i, hlocal, hcard⟩ := p10_1k_projectedNeighborFiber_card_le_chunk d s t hne
  have hmult := p10_1k_local_projectedNeighbor_fiber_card
    (fun g => p10_1k_chunkGroup_two_add d i g)
    (p10_1k_chunkedWord d s i) (p10_1k_chunkedWord d t i) hlocal
  refine ⟨i, ?_⟩
  calc
    Fintype.card {j : Fin d //
        p10_1k_projectedWord d (p10_1kFlipCoordinate s j) = t} ≤
        Fintype.card {g : P10_1kChunkGroup d i //
          projectedNeighbor (p10_1k_chunkedWord d s i) g =
            p10_1k_chunkedWord d t i} := hcard
    _ = if chunkSyndrome (p10_1k_chunkedWord d s i) = 0 then
          Fintype.card (P10_1kChunkGroup d i) else 2 := hmult

/-- An actual residual incident odd-role group has multiplicity at most two,
except for the syndrome-zero chunk fiber. -/
theorem p10_1k_residualIncidentOddGroup_card_bound {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (q : P10_1kProjectedSite n m)
    (hnon : (p10_1kResidualIncidentOddGroup hm a q).Nonempty) :
    ∃ i : Fin (n - m).bitIndices.length,
      Fintype.card {b : P10_1kOddRole n //
        b ∈ p10_1kResidualIncidentOddGroup hm a q} ≤
        if chunkSyndrome
            (p10_1k_chunkedWord (n - m) (p10_1kResidualWord hm a.1) i) = 0 then
          Fintype.card (P10_1kChunkGroup (n - m) i) else 2 := by
  classical
  obtain ⟨b, hb⟩ := hnon
  have hdata := (Finset.mem_filter.mp hb).2
  have hq : q.1 = p10_1kSpecialSlice hm a.1 := by
    calc
      q.1 = (p10_1kProjectedVertex hm b.1).1 :=
        (congrArg Prod.fst hdata.2.2).symm
      _ = p10_1kSpecialSlice hm a.1 := hdata.1
  obtain ⟨j, hflip⟩ := p10_1k_adjacent_residual_same_slice_flip hm
    hdata.2.1 hdata.1.symm
  have hne : ∃ j : Fin (n - m),
      p10_1k_projectedWord (n - m)
        (p10_1kFlipCoordinate (p10_1kResidualWord hm a.1) j) = q.2 := by
    refine ⟨j, ?_⟩
    have hproj := congrArg Prod.snd hdata.2.2
    change p10_1k_projectedWord (n - m) (p10_1kResidualWord hm b.1) = q.2 at hproj
    rw [hflip] at hproj
    exact hproj
  obtain ⟨i, hfiber⟩ := p10_1k_projectedNeighborFiber_card_bound
    (n - m) (p10_1kResidualWord hm a.1) q.2 hne
  have hgroup := p10_1k_residualIncidentOddGroup_card_le_fiber hm a q hq
  exact ⟨i, hgroup.trans hfiber⟩

/-- A radius-three Hamming ball in a `d`-cube has at most `(d+1)^3`
vertices, by encoding each vertex with its at most three changed coordinates. -/
theorem p10_1k_hammingBall_three_card_le_cube {d : ℕ} (q : Fin d → Bool) :
    (Finset.univ.filter fun v : Fin d → Bool => hammingDist q v ≤ 3).card ≤
      (d + 1) ^ 3 := by
  classical
  let B : Finset (Fin d → Bool) :=
    Finset.univ.filter fun v => hammingDist q v ≤ 3
  let diff (v : Fin d → Bool) : Finset (Fin d) :=
    Finset.univ.filter fun i => q i ≠ v i
  have hdiffCard (v : {v : Fin d → Bool // v ∈ B}) : (diff v.1).card ≤ 3 := by
    have hball : hammingDist q v.1 ≤ 3 := (Finset.mem_filter.mp v.2).2
    simpa [diff, hammingDist] using hball
  let code (v : {v : Fin d → Bool // v ∈ B}) : Fin 3 → Option (Fin d) :=
    fun j => if hj : j.val < (diff v.1).card then
      some ((diff v.1).equivFin.symm ⟨j.val, hj⟩).1 else none
  have hcodeMem (v : {v : Fin d → Bool // v ∈ B}) (i : Fin d) :
      i ∈ diff v.1 ↔ ∃ j : Fin 3, code v j = some i := by
    constructor
    · intro hi
      let k := (diff v.1).equivFin ⟨i, hi⟩
      have hk3 : k.val < 3 := lt_of_lt_of_le k.isLt (hdiffCard v)
      let j : Fin 3 := ⟨k.val, hk3⟩
      refine ⟨j, ?_⟩
      have hj : j.val < (diff v.1).card := by simpa [j] using k.isLt
      have hfin : (⟨j.val, hj⟩ : Fin (diff v.1).card) = k := Fin.ext rfl
      have hval := congrArg Subtype.val (congrArg (diff v.1).equivFin.symm hfin)
      have hval' : ((diff v.1).equivFin.symm ⟨j.val, hj⟩).1 = i := by
        simpa [k] using hval
      simp [code, hj, hval']
    · rintro ⟨j, hj⟩
      by_cases hsmall : j.val < (diff v.1).card
      · have hval : ((diff v.1).equivFin.symm
            ⟨j.val, hsmall⟩).1 = i := by
          have hsome : some ((diff v.1).equivFin.symm
              ⟨j.val, hsmall⟩).1 = some i := by
            simpa [code, hsmall] using hj
          exact Option.some.inj hsome
        have hmem : ((diff v.1).equivFin.symm
            ⟨j.val, hsmall⟩).1 ∈ diff v.1 :=
          ((diff v.1).equivFin.symm ⟨j.val, hsmall⟩).2
        simpa [hval] using hmem
      · simp [code, hsmall] at hj
  have hcode : Function.Injective code := by
    intro v w hvw
    apply Subtype.ext
    have hdiffEq : diff v.1 = diff w.1 := by
      apply Finset.ext
      intro i
      rw [hcodeMem v i, hcodeMem w i]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, by simpa [hvw] using hj⟩
      · rintro ⟨j, hj⟩
        exact ⟨j, by simpa [hvw] using hj⟩
    funext i
    by_cases hi : i ∈ diff v.1
    · have hi' : i ∈ diff w.1 := by rw [← hdiffEq]; exact hi
      have hv : q i ≠ v.1 i := (Finset.mem_filter.mp hi).2
      have hw : q i ≠ w.1 i := (Finset.mem_filter.mp hi').2
      cases hq : q i <;> cases hvv : v.1 i <;> cases hww : w.1 i <;>
        simp_all
    · have hi' : i ∉ diff w.1 := by rw [← hdiffEq]; exact hi
      have hv : q i = v.1 i := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      have hw : q i = w.1 i := by
        by_contra hne
        exact hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      rw [← hv, ← hw]
  have hcard := Fintype.card_le_of_injective code hcode
  calc
    B.card = Fintype.card {v : Fin d → Bool // v ∈ B} := by simp
    _ ≤ Fintype.card (Fin 3 → Option (Fin d)) := hcard
    _ = (d + 1) ^ 3 := by simp

/-- Projected sites that may meet the odd groups at an even center: one special
coordinate away in the slice, or at residual distance at most three. -/
noncomputable def p10_1kProjectedNeighborEnvelope {n m : ℕ}
    (q : P10_1kProjectedSite n m) : Finset (P10_1kProjectedSite n m) := by
  classical
  exact
    (Finset.univ.filter fun z : Fin m → Bool => hammingDist q.1 z = 1).image
      (fun z => (z, q.2)) ∪
      (Finset.univ.filter fun t : Fin (n - m) → Bool => hammingDist q.2 t ≤ 3).image
      (fun t => (q.1, t))

/-- The projected-neighbor envelope has polynomial size: at most `m` special
neighbors and one residual radius-three ball. -/
theorem p10_1kProjectedNeighborEnvelope_card_le {n m : ℕ}
    (q : P10_1kProjectedSite n m) :
    (p10_1kProjectedNeighborEnvelope q).card ≤ m + (n - m + 1) ^ 3 := by
  classical
  let special : Finset (P10_1kProjectedSite n m) :=
    (Finset.univ.filter fun z : Fin m → Bool => hammingDist q.1 z = 1).image
      (fun z => (z, q.2))
  let residual : Finset (P10_1kProjectedSite n m) :=
    (Finset.univ.filter fun t : Fin (n - m) → Bool => hammingDist q.2 t ≤ 3).image
      (fun t => (q.1, t))
  have hspecial : special.card ≤ m := by
    have hsubset : (Finset.univ.filter fun z : Fin m → Bool =>
        hammingDist q.1 z = 1) ⊆
        (Finset.univ : Finset (Fin m)).image (p10_1kFlipCoordinate q.1) := by
      intro z hz
      have hdist := (Finset.mem_filter.mp hz).2
      obtain ⟨j, hflip⟩ := p10_1k_flipCoordinate_of_hammingDist_one q.1 z hdist
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hflip.symm⟩
    calc
      special.card ≤
          (Finset.univ.filter fun z : Fin m → Bool => hammingDist q.1 z = 1).card :=
        Finset.card_image_le
      _ ≤ ((Finset.univ : Finset (Fin m)).image
          (p10_1kFlipCoordinate q.1)).card := Finset.card_le_card hsubset
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
      _ = m := by simp
  have hresidual : residual.card ≤ (n - m + 1) ^ 3 := by
    calc
      residual.card ≤
          (Finset.univ.filter fun t : Fin (n - m) → Bool =>
            hammingDist q.2 t ≤ 3).card := Finset.card_image_le
      _ ≤ (n - m + 1) ^ 3 := p10_1k_hammingBall_three_card_le_cube q.2
  have hunion : p10_1kProjectedNeighborEnvelope q = special ∪ residual := by
    simp [special, residual, p10_1kProjectedNeighborEnvelope]
  rw [hunion]
  calc
    (special ∪ residual).card ≤ special.card + residual.card :=
      Finset.card_union_le special residual
    _ ≤ m + (n - m + 1) ^ 3 := Nat.add_le_add hspecial hresidual

/-- All present prospective IDs whose centers can be queried by one projected
odd group, over every incident site and height. -/
noncomputable def p10_1kGroupPositionCandidates {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (P : P10_1kProspectiveId n m δ → Bool) :
    Finset (P10_1kProspectiveId n m δ) := by
  classical
  let p := p10_1kHeightParams n m δ
  exact (p10_1kProjectedNeighborEnvelope q).biUnion fun site =>
    (Finset.univ : Finset (Fin (p.H + 1))).biUnion fun j =>
      (p10_1kHeightEligibleIds p (fun loc => P (site.1, loc)) site.2 j).image
        (fun loc => (site.1, loc))

/-- If every incident site-level has at most `2λ` positions, the group has at
most envelope-size times the number of levels times `2λ` candidate IDs. -/
theorem p10_1kGroupPositionCandidates_card_bound {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (P : P10_1kProspectiveId n m δ → Bool)
    (hpositions : ∀ site ∈ p10_1kProjectedNeighborEnvelope q,
      ∀ j : Fin ((p10_1kHeightParams n m δ).H + 1),
        (p10_1kHeightPositionCount (p10_1kHeightParams n m δ)
          (fun loc => P (site.1, loc)) site.2 j : ℝ) ≤
            2 * (p10_1kHeightParams n m δ).lam) :
    ((p10_1kGroupPositionCandidates δ q P).card : ℝ) ≤
      (p10_1kProjectedNeighborEnvelope q).card *
        ((p10_1kHeightParams n m δ).H + 1 : ℕ) *
        (2 * (p10_1kHeightParams n m δ).lam) := by
  classical
  let p := p10_1kHeightParams n m δ
  let Env := p10_1kProjectedNeighborEnvelope q
  let siteWord (site : P10_1kProjectedSite n m) : CubeVertex p.d := by
    change Fin p.d → Bool
    simpa [p, p10_1kHeightParams] using site.2
  let ids (site : P10_1kProjectedSite n m) (j : Fin (p.H + 1)) :=
    p10_1kHeightEligibleIds p (fun loc => P (site.1, loc)) (siteWord site) j
  let siteCandidates (site : P10_1kProjectedSite n m) :=
    (Finset.univ : Finset (Fin (p.H + 1))).biUnion fun j =>
      (ids site j).image (fun loc => (site.1, loc))
  have hsiteNat (site : P10_1kProjectedSite n m) :
      (siteCandidates site).card ≤ ∑ j : Fin (p.H + 1), (ids site j).card := by
    calc
      (siteCandidates site).card ≤
          ∑ j : Fin (p.H + 1), ((ids site j).image (fun loc => (site.1, loc))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ j : Fin (p.H + 1), (ids site j).card :=
        Finset.sum_le_sum fun j hj => Finset.card_image_le
  have hsiteReal (site : P10_1kProjectedSite n m) (hsite : site ∈ Env) :
      ((siteCandidates site).card : ℝ) ≤ (p.H + 1 : ℕ) * (2 * p.lam) := by
    have hcast : ((siteCandidates site).card : ℝ) ≤
        ∑ j : Fin (p.H + 1), ((ids site j).card : ℝ) := by
      exact_mod_cast hsiteNat site
    calc
      ((siteCandidates site).card : ℝ) ≤
          ∑ j : Fin (p.H + 1), ((ids site j).card : ℝ) := hcast
      _ ≤ ∑ j : Fin (p.H + 1), (2 * p.lam) := by
        apply Finset.sum_le_sum
        intro j hj
        have hsiteWord : siteWord site = site.2 := by
          have hd : p.d = n - m := rfl
          cases hd
          rfl
        have hpositionBound :
            (p10_1kHeightPositionCount p (fun loc => P (site.1, loc))
              (siteWord site) j : ℝ) ≤ 2 * p.lam := by
          rw [hsiteWord]
          simpa [p] using hpositions site hsite j
        change ((p10_1kHeightEligibleIds p
          (fun loc => P (site.1, loc)) (siteWord site) j).card : ℝ) ≤ 2 * p.lam
        rw [p10_1kHeightEligibleIds_card]
        exact hpositionBound
      _ = (p.H + 1 : ℕ) * (2 * p.lam) := by simp
  have houterNat :
      (p10_1kGroupPositionCandidates δ q P).card ≤
        ∑ site ∈ Env, (siteCandidates site).card := by
    simp only [p10_1kGroupPositionCandidates, p, Env, ids, siteCandidates]
    exact Finset.card_biUnion_le
  have houterReal :
      ((p10_1kGroupPositionCandidates δ q P).card : ℝ) ≤
        ∑ site ∈ Env, ((siteCandidates site).card : ℝ) := by
    exact_mod_cast houterNat
  calc
    ((p10_1kGroupPositionCandidates δ q P).card : ℝ) ≤
        ∑ site ∈ Env, ((siteCandidates site).card : ℝ) := houterReal
    _ ≤ ∑ site ∈ Env, ((p.H + 1 : ℕ) * (2 * p.lam)) := by
      apply Finset.sum_le_sum
      intro site hsite
      exact hsiteReal site hsite
    _ = (p10_1kProjectedNeighborEnvelope q).card *
        ((p10_1kHeightParams n m δ).H + 1 : ℕ) *
        (2 * (p10_1kHeightParams n m δ).lam) := by
      simp [Env, p]
      ring

/-- The number of subsets of a finite candidate set with size at most `r` is
at most the number of `r`-tuples padded by an empty symbol. -/
private theorem p10_1k_finsetSubsets_card_le_pow {α : Type*} [Fintype α]
    (r : ℕ) :
    ((Finset.univ : Finset (Finset α)).filter fun s => s.card ≤ r).card ≤
      (Fintype.card α + 1) ^ r := by
  classical
  let S := (Finset.univ : Finset (Finset α)).filter fun s => s.card ≤ r
  let code (s : {s // s ∈ S}) : Fin r → Option α := fun j =>
    if hj : j.val < s.1.card then some ((s.1.equivFin.symm ⟨j.val, hj⟩).1) else none
  have hcodeMem (s : {s // s ∈ S}) (a : α) :
      a ∈ s.1 ↔ ∃ j : Fin r, code s j = some a := by
    constructor
    · intro ha
      let k := s.1.equivFin ⟨a, ha⟩
      have hk : k.val < s.1.card := k.isLt
      have hr : k.val < r := lt_of_lt_of_le hk (Finset.mem_filter.mp s.2).2
      let j : Fin r := ⟨k.val, hr⟩
      refine ⟨j, ?_⟩
      have hj : j.val < s.1.card := by simpa [j] using hk
      have hfin : (⟨j.val, hj⟩ : Fin s.1.card) = k := Fin.ext rfl
      have hval := congrArg Subtype.val (congrArg s.1.equivFin.symm hfin)
      have hval' : (s.1.equivFin.symm ⟨j.val, hj⟩).1 = a := by
        simpa [k] using hval
      simp [code, hj, hval']
    · rintro ⟨j, hj⟩
      by_cases hsmall : j.val < s.1.card
      · have hval : (s.1.equivFin.symm ⟨j.val, hsmall⟩).1 = a := by
          have hsome : some (s.1.equivFin.symm ⟨j.val, hsmall⟩).1 = some a := by
            simpa [code, hsmall] using hj
          exact Option.some.inj hsome
        have hmem : (s.1.equivFin.symm ⟨j.val, hsmall⟩).1 ∈ s.1 :=
          (s.1.equivFin.symm ⟨j.val, hsmall⟩).2
        simpa [hval] using hmem
      · simp [code, hsmall] at hj
  have hcode : Function.Injective code := by
    intro s t hst
    apply Subtype.ext
    apply Finset.ext
    intro a
    rw [hcodeMem s a, hcodeMem t a]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by simpa [hst] using hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by simpa [hst] using hj⟩
  have hcard := Fintype.card_le_of_injective code hcode
  calc
    S.card = Fintype.card {s // s ∈ S} := by simp
    _ ≤ Fintype.card (Fin r → Option α) := hcard
    _ = (Fintype.card α + 1) ^ r := by simp

/-- A family of hypothetical lists of size at most `r` drawn from a
candidate-ID set has cardinality at most `(C.card+1)^r`. -/
theorem p10_1kCandidateListFamily_card_le {I : Type*} [Fintype I]
    (C : Finset I) (r : ℕ) :
    ((Finset.univ : Finset (Finset {id // id ∈ C})).filter
      fun D => D.card ≤ r).card ≤ (C.card + 1) ^ r := by
  simpa using p10_1k_finsetSubsets_card_le_pow
    (α := {id // id ∈ C}) r

/-- The logarithm of the bounded-size candidate-list count is linear in the
list-size bound and in the logarithm of the candidate-set size. -/
theorem p10_1kCandidateListFamily_log_card_bound {I : Type*} [Fintype I]
    (C : Finset I) (r : ℕ) :
    Real.log
      ((((Finset.univ : Finset (Finset {id // id ∈ C})).filter
        fun D => D.card ≤ r).card : ℝ) + 1) ≤
      Real.log 2 + (r : ℝ) * Real.log ((C.card : ℝ) + 1) := by
  let L : Finset (Finset {id // id ∈ C}) :=
    (Finset.univ : Finset (Finset {id // id ∈ C})).filter fun D => D.card ≤ r
  have hcount : L.card ≤ (C.card + 1) ^ r := by
    simpa [L] using p10_1kCandidateListFamily_card_le C r
  have hnat : L.card + 1 ≤ (C.card + 1) ^ r + 1 := Nat.add_le_add_right hcount 1
  have hcast : (L.card : ℝ) + 1 ≤ ((C.card + 1) ^ r : ℕ) + 1 := by
    exact_mod_cast hnat
  have hpowCast : ((C.card + 1) ^ r : ℕ) = ((C.card : ℝ) + 1) ^ r := by
    norm_cast
  have hbase : 1 ≤ (C.card : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg C.card)
  have hpow : 1 ≤ ((C.card : ℝ) + 1) ^ r := one_le_pow₀ hbase
  have hplus : (L.card : ℝ) + 1 ≤ 2 * ((C.card : ℝ) + 1) ^ r := by
    rw [hpowCast] at hcast
    nlinarith [hcast, hpow]
  calc
    Real.log ((L.card : ℝ) + 1) ≤
        Real.log (2 * ((C.card : ℝ) + 1) ^ r) :=
      Real.log_le_log (by positivity) hplus
    _ = Real.log 2 + (r : ℝ) * Real.log ((C.card : ℝ) + 1) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]

/-- The projected neighbor envelope is symmetric in its two sites. -/
theorem p10_1kProjectedNeighborEnvelope_symm {n m : ℕ}
    (q s : P10_1kProjectedSite n m) :
    s ∈ p10_1kProjectedNeighborEnvelope q ↔
      q ∈ p10_1kProjectedNeighborEnvelope s := by
  classical
  have hforward : ∀ q s : P10_1kProjectedSite n m,
      s ∈ p10_1kProjectedNeighborEnvelope q →
      q ∈ p10_1kProjectedNeighborEnvelope s := by
    intro q s h
    rcases Finset.mem_union.mp h with hspecial | hresidual
    · obtain ⟨z, hz, hpair⟩ := Finset.mem_image.mp hspecial
      have hdist := (Finset.mem_filter.mp hz).2
      have hs1 : s.1 = z := (congrArg Prod.fst hpair).symm
      have hs2 : s.2 = q.2 := (congrArg Prod.snd hpair).symm
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨q.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [hs1]
        simpa [hammingDist_comm] using hdist
      · apply Prod.ext
        · rfl
        · exact hs2
    · obtain ⟨t, ht, hpair⟩ := Finset.mem_image.mp hresidual
      have hdist := (Finset.mem_filter.mp ht).2
      have hs1 : s.1 = q.1 := (congrArg Prod.fst hpair).symm
      have hs2 : s.2 = t := (congrArg Prod.snd hpair).symm
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨q.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [hs2]
        simpa [hammingDist_comm] using hdist
      · apply Prod.ext
        · exact hs1
        · rfl
  exact ⟨hforward q s, hforward s q⟩

/-- Inside one special slice, an envelope site is within residual distance
three of its center site. -/
theorem p10_1k_envelope_same_slice_residual_dist_le_three {n m : ℕ}
    (q s : P10_1kProjectedSite n m)
    (hmem : s ∈ p10_1kProjectedNeighborEnvelope q)
    (hslice : s.1 = q.1) : hammingDist q.2 s.2 ≤ 3 := by
  classical
  rcases Finset.mem_union.mp hmem with hspecial | hresidual
  · obtain ⟨z, hz, hpair⟩ := Finset.mem_image.mp hspecial
    have hdist := (Finset.mem_filter.mp hz).2
    have hzeq : z = q.1 := (congrArg Prod.fst hpair).trans hslice
    rw [hzeq] at hdist
    simp at hdist
  · obtain ⟨t, ht, hpair⟩ := Finset.mem_image.mp hresidual
    have hdist := (Finset.mem_filter.mp ht).2
    have hteq : t = s.2 := congrArg Prod.snd hpair
    simpa [hteq] using hdist

/-- The envelope residual-distance bound also holds in the reverse order. -/
theorem p10_1k_envelope_same_slice_residual_dist_le_three_symm {n m : ℕ}
    (q s : P10_1kProjectedSite n m)
    (hmem : s ∈ p10_1kProjectedNeighborEnvelope q)
    (hslice : s.1 = q.1) : hammingDist s.2 q.2 ≤ 3 := by
  simpa [hammingDist_comm] using
    p10_1k_envelope_same_slice_residual_dist_le_three q s hmem hslice

/-- Odd roles are grouped by their special slice and projected residual word. -/
noncomputable def p10_1kOddGroupRoles {n m : ℕ} (hm : m ≤ n)
    (q : P10_1kProjectedSite n m) : Finset (P10_1kOddRole n) := by
  classical
  exact Finset.univ.filter fun b => p10_1kProjectedVertex hm b.1 = q

/-- Distinct projected odd groups incident to one even role. -/
noncomputable def p10_1kIncidentOddGroups {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) : Finset (P10_1kProjectedSite n m) := by
  classical
  exact (Finset.univ.filter fun b : P10_1kOddRole n =>
    (cube n).Adj a.1 b.1).image (fun b => p10_1kProjectedVertex hm b.1)

/-- An incident group is exactly the projection of an odd neighbor. -/
theorem p10_1k_mem_incidentOddGroups {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) (q : P10_1kProjectedSite n m) :
    q ∈ p10_1kIncidentOddGroups hm a ↔
      ∃ b : P10_1kOddRole n, (cube n).Adj a.1 b.1 ∧
        p10_1kProjectedVertex hm b.1 = q := by
  classical
  simp [p10_1kIncidentOddGroups]

/-- Every projected odd group incident to an even role lies in its projected
neighbor envelope. -/
theorem p10_1k_incidentOddGroups_subset_envelope {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) :
    p10_1kIncidentOddGroups hm a ⊆
      p10_1kProjectedNeighborEnvelope (p10_1kProjectedVertex hm a.1) := by
  classical
  intro q hq
  obtain ⟨b, hadj, hbq⟩ := (p10_1k_mem_incidentOddGroups hm a q).mp hq
  rcases p10_1k_projectedVertex_edge hm hadj with hspecial | hresidual
  · apply Finset.mem_union.mpr
    left
    have hsite : p10_1kProjectedVertex hm b.1 =
        (p10_1kSpecialSlice hm b.1,
          p10_1k_projectedWord (n - m) (p10_1kResidualWord hm a.1)) := by
      apply Prod.ext
      · rfl
      · simpa [p10_1kProjectedVertex] using hspecial.2.symm
    have hpair : (p10_1kSpecialSlice hm b.1,
        p10_1k_projectedWord (n - m) (p10_1kResidualWord hm a.1)) = q :=
      hsite.symm.trans hbq
    apply Finset.mem_image.mpr
    refine ⟨p10_1kSpecialSlice hm b.1, ?_, hpair⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hspecial.1⟩
  · apply Finset.mem_union.mpr
    right
    have hsite : p10_1kProjectedVertex hm b.1 =
        (p10_1kSpecialSlice hm a.1,
          p10_1k_projectedWord (n - m) (p10_1kResidualWord hm b.1)) := by
      apply Prod.ext
      · exact hresidual.1.symm
      · rfl
    have hpair : (p10_1kSpecialSlice hm a.1,
        p10_1k_projectedWord (n - m) (p10_1kResidualWord hm b.1)) = q :=
      hsite.symm.trans hbq
    apply Finset.mem_image.mpr
    refine ⟨p10_1k_projectedWord (n - m) (p10_1kResidualWord hm b.1), ?_, hpair⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hresidual.2⟩

/-- The projected site of an even role adjacent to an odd role lies in the
odd role's symmetric projected-neighbor envelope. -/
theorem p10_1k_evenSite_mem_oddGroupEnvelope_of_adjacent {n m : ℕ}
    (hm : m ≤ n) (a : P10_1kEvenRole n) (b : P10_1kOddRole n)
    (hadj : (cube n).Adj a.1 b.1) :
    p10_1kProjectedVertex hm a.1 ∈
      p10_1kProjectedNeighborEnvelope (p10_1kProjectedVertex hm b.1) := by
  have hgroup : p10_1kProjectedVertex hm b.1 ∈ p10_1kIncidentOddGroups hm a :=
    (p10_1k_mem_incidentOddGroups hm a
      (p10_1kProjectedVertex hm b.1)).2 ⟨b, hadj, rfl⟩
  have henv := p10_1k_incidentOddGroups_subset_envelope hm a hgroup
  exact (p10_1kProjectedNeighborEnvelope_symm
    (p10_1kProjectedVertex hm a.1) (p10_1kProjectedVertex hm b.1)).mp henv

/-- Candidate tuple-array IDs queried by one projected odd group, using the
selected center at each site in its envelope. -/
noncomputable def p10_1kOddGroupTupleIdScope {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc) :
    Finset (P10_1kProspectiveId n m δ) := by
  classical
  exact (p10_1kProjectedNeighborEnvelope q).biUnion fun site =>
    (selected site).elim ∅ (fun loc => {(site.1, loc)})

/-- Selected center IDs in an odd group's own special slice. -/
noncomputable def p10_1kOddGroupOwnTupleIds {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc) :
    Finset (P10_1kProspectiveId n m δ) := by
  classical
  exact (p10_1kOddGroupTupleIdScope δ q selected).filter
    (fun id => id.1 = q.1)

/-- Every own-slice ID in an odd-group scope has a selected envelope-site
preimage. -/
theorem p10_1k_ownTupleId_source {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (id : P10_1kProspectiveId n m δ)
    (hid : id ∈ p10_1kOddGroupOwnTupleIds δ q selected) :
    ∃ site loc, site ∈ p10_1kProjectedNeighborEnvelope q ∧
      site.1 = q.1 ∧ selected site = some loc ∧ id = (site.1, loc) := by
  classical
  have hidParts := Finset.mem_filter.mp hid
  rcases Finset.mem_biUnion.mp hidParts.1 with ⟨site, hsite, hidSite⟩
  cases hselected : selected site with
  | none => simp [hselected] at hidSite
  | some loc =>
    have hidEq : id = (site.1, loc) := by simpa [hselected] using hidSite
    have hslice : site.1 = q.1 := by
      calc
        site.1 = id.1 := (congrArg Prod.fst hidEq).symm
        _ = q.1 := hidParts.2
    exact ⟨site, loc, hsite, hslice, hselected, hidEq⟩

/-- Selected sites of the odd group's own special slice. -/
noncomputable def p10_1kOddGroupOwnSelectedSites {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc) :
    Finset (P10_1kProjectedSite n m) := by
  classical
  exact (p10_1kProjectedNeighborEnvelope q).filter fun site =>
    site.1 = q.1 ∧ (selected site).isSome

/-- Selected sites in special slices adjacent to the odd group's own slice. -/
noncomputable def p10_1kOddGroupExternalSelectedSites {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc) :
    Finset (P10_1kProjectedSite n m) := by
  classical
  exact (p10_1kProjectedNeighborEnvelope q).filter fun site =>
    site.1 ≠ q.1 ∧ (selected site).isSome

/-- An envelope site with a selected center contributes its global ID to the
projected group's tuple-array scope. -/
theorem p10_1k_mem_oddGroupTupleIdScope {n m : ℕ} (δ : ℝ)
    (q site : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (loc : (p10_1kHeightParams n m δ).Loc)
    (hsite : site ∈ p10_1kProjectedNeighborEnvelope q)
    (hselected : selected site = some loc) :
    (site.1, loc) ∈
      p10_1kOddGroupTupleIdScope δ q selected := by
  classical
  unfold p10_1kOddGroupTupleIdScope
  apply Finset.mem_biUnion.mpr
  refine ⟨site, hsite, ?_⟩
  simp [hselected]

/-- At most `m` selected envelope sites lie in a special slice adjacent to
the odd group's own slice. -/
theorem p10_1kOddGroupExternalSelectedSites_card_le {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc) :
    (p10_1kOddGroupExternalSelectedSites δ q selected).card ≤ m := by
  classical
  let special : Finset (P10_1kProjectedSite n m) :=
    (Finset.univ : Finset (Fin m)).image fun i =>
      (p10_1kFlipCoordinate q.1 i, q.2)
  have hsubset : p10_1kOddGroupExternalSelectedSites δ q selected ⊆ special := by
    intro site hsite
    have henv : site ∈ p10_1kProjectedNeighborEnvelope q :=
      (Finset.mem_filter.mp hsite).1
    have hdiff : site.1 ≠ q.1 := (Finset.mem_filter.mp hsite).2.1
    rcases Finset.mem_union.mp henv with hspecial | hresidual
    · obtain ⟨z, hz, hpair⟩ := Finset.mem_image.mp hspecial
      have hdist := (Finset.mem_filter.mp hz).2
      obtain ⟨i, hflip⟩ := p10_1k_flipCoordinate_of_hammingDist_one q.1 z hdist
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      calc
        (p10_1kFlipCoordinate q.1 i, q.2) = (z, q.2) := by rw [hflip]
        _ = site := hpair
    · obtain ⟨t, ht, hpair⟩ := Finset.mem_image.mp hresidual
      have hslice : site.1 = q.1 := (congrArg Prod.fst hpair).symm
      exact (hdiff hslice).elim
  calc
    (p10_1kOddGroupExternalSelectedSites δ q selected).card ≤ special.card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
    _ = m := by simp

/-- The global scope has at most `T` own-slice IDs and one external ID per
special neighbor, once the local height-fan bound is available. -/
theorem p10_1kOddGroupTupleIdScope_card_le {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (T : ℕ)
    (hown : (p10_1kOddGroupOwnTupleIds δ q selected).card ≤ T) :
    (p10_1kOddGroupTupleIdScope δ q selected).card ≤ T + m := by
  classical
  let scope := p10_1kOddGroupTupleIdScope δ q selected
  let own := p10_1kOddGroupOwnTupleIds δ q selected
  let externalIds := scope.filter (fun id => id.1 ≠ q.1)
  let externalSites := p10_1kOddGroupExternalSelectedSites δ q selected
  let p := p10_1kHeightParams n m δ
  let defaultLoc : p.Loc := (fun _ => false, ⟨0, by omega⟩)
  let f : P10_1kProjectedSite n m → P10_1kProspectiveId n m δ :=
    fun site => (site.1, (selected site).getD defaultLoc)
  have hpart : scope = own ∪ externalIds := by
    ext id
    by_cases hid : id.1 = q.1 <;> simp [scope, own, externalIds, hid,
      p10_1kOddGroupOwnTupleIds]
  have hdisjoint : Disjoint own externalIds := by
    apply Finset.disjoint_left.mpr
    intro id hidOwn hidExternal
    exact (Finset.mem_filter.mp hidExternal).2
      (Finset.mem_filter.mp hidOwn).2
  have hExtSubset : externalIds ⊆ externalSites.image f := by
    intro id hid
    have hidScope : id ∈ scope := (Finset.mem_filter.mp hid).1
    have hidExternal : id.1 ≠ q.1 := (Finset.mem_filter.mp hid).2
    rcases Finset.mem_biUnion.mp hidScope with ⟨site, hsite, hidSite⟩
    cases hselected : selected site with
    | none => simp [hselected] at hidSite
    | some loc =>
      have hidEq : id = (site.1, loc) := by simpa [hselected] using hidSite
      have hsiteExternal : site ∈ externalSites := by
        apply Finset.mem_filter.mpr
        refine ⟨hsite, ?_, ?_⟩
        · intro heq
          apply hidExternal
          exact (congrArg Prod.fst hidEq).trans heq
        · simp [hselected]
      rw [hidEq]
      apply Finset.mem_image.mpr
      refine ⟨site, hsiteExternal, ?_⟩
      simp [f, hselected]
  have hcardScope : scope.card = own.card + externalIds.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisjoint]
  have hExternal : externalIds.card ≤ m := by
    calc
      externalIds.card ≤ (externalSites.image f).card := Finset.card_le_card hExtSubset
      _ ≤ externalSites.card := Finset.card_image_le
      _ ≤ m := p10_1kOddGroupExternalSelectedSites_card_le δ q selected
  calc
    (p10_1kOddGroupTupleIdScope δ q selected).card =
        own.card + externalIds.card := hcardScope
    _ ≤ T + m := Nat.add_le_add hown hExternal

/-- The fixed-list test event for one projected odd group, using the tuple
arrays at the selected IDs in its projected-neighbor envelope. -/
noncomputable def p10_1kProjectedGroupFixedListFailure
    {n N m k : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {ζ δ : ℝ} {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (μ : P10_1kProspectiveId n m δ → Law N)
    (group : P10_1kProjectedSite n m) (gain : ℝ)
    (W : P10_1kProspectiveId n m δ → Fin k → Fin N) : Prop := by
  classical
  let S := p10_1kOddGroupTupleIdScope δ group selected
  let e : Fin S.card ≃ {id // id ∈ S} := S.equivFin.symm
  exact fixedListFailure E G (p10_1kClusterPrior data) data.D
    (fun b => μ (e b).1) gain (fun b i => W (e b).1 i)

/-- A projected group's fixed-list failure depends only on the tuple arrays at
the group's selected scope IDs. -/
theorem p10_1kProjectedGroupFixedListFailure_depends_on_scope
    {n N m k : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {ζ δ : ℝ} {A B : Finset (Fin N)}
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (μ : P10_1kProspectiveId n m δ → Law N)
    (group : P10_1kProjectedSite n m) (gain : ℝ)
    (W W' : P10_1kProspectiveId n m δ → Fin k → Fin N)
    (hW : ∀ id ∈ p10_1kOddGroupTupleIdScope δ group selected,
      W id = W' id) :
    p10_1kProjectedGroupFixedListFailure data selected μ group gain W ↔
      p10_1kProjectedGroupFixedListFailure data selected μ group gain W' := by
  classical
  let S := p10_1kOddGroupTupleIdScope δ group selected
  let e : Fin S.card ≃ {id // id ∈ S} := S.equivFin.symm
  simpa [p10_1kProjectedGroupFixedListFailure, S, e] using
    (p10_1k_fixedListFailure_depends_on_scope E G
      (p10_1kClusterPrior data) data.D (fun b => μ (e b).1) gain
      S e W W' hW)

/-- A successful height selection returns an active eligible center at the
site's own height, and that level is not bad. -/
theorem p10_1k_selection_spec_of_some {p : HDParams}
    (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties)
    (v : CubeVertex p.d) (ℓ : p.Loc)
    (hsel : p.selection Sites P A E τ v = some ℓ) :
    ∃ j : Fin (p.H + 1),
      p.height Sites P A E p.Rlong v = j.val ∧ j.val < p.H ∧
        ¬ p.Bad P A E v j ∧ ℓ ∈ E v j ∧ A ℓ = true := by
  classical
  let h := p.height Sites P A E p.Rlong v
  have hh : h < p.H := by
    by_contra hnot
    simp [HDParams.selection, HDParams.selectionAt, h, hnot] at hsel
  let j : Fin (p.H + 1) := ⟨h, by omega⟩
  have hbad : ¬ p.Bad P A E v j := by
    intro hbad
    simp [HDParams.selection, HDParams.selectionAt, h, hh, j, hbad] at hsel
  have hsel' := hsel
  simp [HDParams.selection, HDParams.selectionAt, h, hh, j, hbad] at hsel'
  rcases hsel' with ⟨hne, hchosen⟩
  let active : Finset p.Loc := (E v j).filter (fun x => A x = true)
  let priorities := active.image (p.priority τ (v, j))
  have hneP : priorities.Nonempty := by
    rcases hne with ⟨x, hx⟩
    exact ⟨p.priority τ (v, j) x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  let q := priorities.min' hneP
  have hmem : ∃ x, x ∈ active ∧ p.priority τ (v, j) x = q := by
    obtain ⟨x, hx⟩ := Finset.mem_image.mp (Finset.min'_mem priorities hneP)
    exact ⟨x, hx.1, hx.2⟩
  have hchosen' : Classical.choose hmem = ℓ := by
    simpa [active, priorities, q, j] using hchosen
  obtain ⟨hactive, hpriority⟩ := Classical.choose_spec hmem
  rw [hchosen'] at hactive
  have hfilter := Finset.mem_filter.mp hactive
  refine ⟨j, rfl, hh, hbad, hfilter.1, ?_⟩
  simpa using hfilter.2

/-- Legality upgrades a selected center to a present position at its selected
level and within the height-device search radius. -/
theorem p10_1k_selection_legal_spec_of_some {p : HDParams}
    (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties)
    (hlegal : p.Legal P E Sites) (v : CubeVertex p.d) (hv : v ∈ Sites)
    (ℓ : p.Loc) (hsel : p.selection Sites P A E τ v = some ℓ) :
    ∃ j : Fin (p.H + 1),
      p.height Sites P A E p.Rlong v = j.val ∧ j.val < p.H ∧
        ¬ p.Bad P A E v j ∧ ℓ ∈ E v j ∧ A ℓ = true ∧
        P ℓ = true ∧ ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r := by
  obtain ⟨j, hheight, hj, hbad, hE, hA⟩ :=
    p10_1k_selection_spec_of_some Sites P A E τ v ℓ hsel
  have hLegalAt := hlegal v hv j
  obtain ⟨hEligible, hcount⟩ := hLegalAt
  obtain ⟨hP, hlevel, hdist⟩ := hEligible ℓ hE
  exact ⟨j, hheight, hj, hbad, hE, hA, hP, hlevel, hdist⟩

/-- An own-slice tuple ID has a source site at which its height selection is
legal and nonbad. -/
private theorem p10_1k_ownTupleId_selection_spec {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hmatch : ∀ v, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites)
    (id : P10_1kProspectiveId n m δ)
    (hid : id ∈ p10_1kOddGroupOwnTupleIds δ q selected) :
    ∃ v loc j, v ∈ Sites ∧ (q.1, v) ∈ p10_1kProjectedNeighborEnvelope q ∧
      selected (q.1, v) = some loc ∧ id = (q.1, loc) ∧
      (p10_1kHeightParams n m δ).height Sites P A E
        (p10_1kHeightParams n m δ).Rlong v = j.val ∧
      j.val < (p10_1kHeightParams n m δ).H ∧
      ¬ (p10_1kHeightParams n m δ).Bad P A E v j ∧
      loc ∈ E v j ∧ A loc = true ∧ P loc = true ∧
      loc.2 = j ∧ hammingDist loc.1 v ≤ (p10_1kHeightParams n m δ).r := by
  obtain ⟨site, loc, henv, hslice, hselected, hidEq⟩ :=
    p10_1k_ownTupleId_source δ q selected id hid
  have hsiteEq : (q.1, site.2) = site := Prod.ext hslice.symm rfl
  have henv' : (q.1, site.2) ∈ p10_1kProjectedNeighborEnvelope q := by
    rw [hsiteEq]
    exact henv
  have hselected' : selected (q.1, site.2) = some loc := by
    exact (congrArg selected hsiteEq).trans hselected
  have hv : site.2 ∈ Sites := hinSites site.2 loc hselected'
  have hselect : (p10_1kHeightParams n m δ).selection Sites P A E τ site.2 =
      some loc := by
    rw [← hmatch site.2]
    exact hselected'
  obtain ⟨j, hheight, hj, hbad, hE, hA, hP, hlevel, hdist⟩ :=
    p10_1k_selection_legal_spec_of_some Sites P A E τ hlegal
      site.2 hv loc hselect
  have hidEq' : id = (q.1, loc) := by
    calc
      id = (site.1, loc) := hidEq
      _ = (q.1, loc) := by rw [hslice]
  exact ⟨site.2, loc, j, hv, henv', hselected', hidEq', hheight, hj, hbad,
    hE, hA, hP, hlevel, hdist⟩

/-- A finite set whose level map has at most `L` values and at most `M`
members per level has size at most `L * M`. -/
private theorem p10_1k_card_le_levels_mul {α β : Type*} [DecidableEq β]
    (S : Finset α) (level : α → β) (levels : Finset β) (L M : ℕ)
    (hcover : ∀ a ∈ S, level a ∈ levels)
    (hlevels : levels.card ≤ L)
    (hfiber : ∀ b ∈ levels, (S.filter fun a => level a = b).card ≤ M) :
    S.card ≤ L * M := by
  have hsum : S.card =
      ∑ b ∈ levels, (S.filter fun a => level a = b).card := by
    simpa using Finset.card_eq_sum_card_fiberwise hcover
  calc
    S.card = ∑ b ∈ levels, (S.filter fun a => level a = b).card := hsum
    _ ≤ ∑ b ∈ levels, M := by
      apply Finset.sum_le_sum
      intro b hb
      exact hfiber b hb
    _ = levels.card * M := by simp
    _ ≤ L * M := Nat.mul_le_mul_right M hlevels

/-- Under GoodHeights, selected IDs in one own-slice group occupy at most
three height levels. -/
theorem p10_1kOddGroupOwnTupleIds_level_image_card_le_three
    {n m : ℕ} (δ : ℝ) (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hgood : (p10_1kHeightParams n m δ).GoodHeights Sites P A E)
    (hmatch : ∀ v, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites) :
    ((p10_1kOddGroupOwnTupleIds δ q selected).image
      (fun id => id.2.2.val)).card ≤ 3 := by
  classical
  let p := p10_1kHeightParams n m δ
  let Own := p10_1kOddGroupOwnTupleIds δ q selected
  let level : P10_1kProspectiveId n m δ → ℕ := fun id => id.2.2.val
  by_cases hnon : Own.Nonempty
  · obtain ⟨id₀, hid₀⟩ := hnon
    obtain ⟨v₀, loc₀, j₀, hv₀, henv₀, hsel₀, hid₀eq, hheight₀,
      hj₀, hbad₀, hE₀, hA₀, hP₀, hlevel₀, hdist₀⟩ :=
      p10_1k_ownTupleId_selection_spec δ q selected Sites P A E τ
        hlegal hmatch hinSites id₀ hid₀
    have hsiteQ₀ : hammingDist q.2 v₀ ≤ 3 :=
      p10_1k_envelope_same_slice_residual_dist_le_three q (q.1, v₀) henv₀ rfl
    have hbaseHeight : p.height Sites P A E p.Rlong v₀ = level id₀ := by
      calc
        p.height Sites P A E p.Rlong v₀ = j₀.val := hheight₀
        _ = loc₀.2.val := congrArg Fin.val hlevel₀.symm
        _ = level id₀ := by dsimp [level]; rw [hid₀eq]
    let base := level id₀
    let interval := Finset.Icc (base - 1) (base + 1)
    have hlevelWithin (id : P10_1kProspectiveId n m δ)
        (hid : id ∈ Own) : level id ∈ interval := by
      obtain ⟨v, loc, j, hv, henv, hsel, hideq, hheight, hj, hbad,
        hE, hA, hP, hlevel, hdist⟩ :=
        p10_1k_ownTupleId_selection_spec δ q selected Sites P A E τ
          hlegal hmatch hinSites id hid
      have hsiteQ : hammingDist q.2 v ≤ 3 :=
        p10_1k_envelope_same_slice_residual_dist_le_three q (q.1, v) henv rfl
      let qres : CubeVertex (n - m) := q.2
      have hsiteQ₀' : hammingDist v₀ qres ≤ 3 := by
        change hammingDist v₀ q.2 ≤ 3
        exact p10_1k_envelope_same_slice_residual_dist_le_three_symm
          q (q.1, v₀) henv₀ rfl
      have hsiteQ' : hammingDist qres v ≤ 3 := by
        change hammingDist q.2 v ≤ 3
        exact hsiteQ
      have hsiteV : hammingDist v₀ v ≤ p.D := by
        have hsiteV₆ : hammingDist v₀ v ≤ 6 := by
          calc
            hammingDist v₀ v ≤ hammingDist v₀ qres + hammingDist qres v :=
              hammingDist_triangle v₀ qres v
            _ ≤ 3 + 3 := add_le_add hsiteQ₀' hsiteQ'
            _ = 6 := by norm_num
        simpa [p, p10_1kHeightParams] using hsiteV₆
      have hvariation := (hgood v₀ hv₀).2.2 v hv hsiteV
      have hbaseLevel : level id₀ = loc₀.2.val := by
        dsimp [level]
        rw [hid₀eq]
      have hlevelId : level id = loc.2.val := by
        dsimp [level]
        rw [hideq]
      have hvariation' :
          |(level id₀ : ℤ) - (level id : ℤ)| ≤ 1 := by
        rw [hbaseHeight, hheight, ← hlevel] at hvariation
        simpa [hbaseLevel, hlevelId] using hvariation
      have hBounds := abs_le.mp hvariation'
      apply Finset.mem_Icc.mpr
      constructor <;> dsimp [base] <;> omega
    have hlevelsSubset :
        (Own.image level) ⊆ interval := by
      intro j hj
      obtain ⟨id, hid, rfl⟩ := Finset.mem_image.mp hj
      exact hlevelWithin id hid
    have hintervalCard : interval.card ≤ 3 := by
      dsimp [interval]
      simp only [Nat.card_Icc]
      omega
    calc
      (Own.image level).card ≤ interval.card := Finset.card_le_card hlevelsSubset
      _ ≤ 3 := hintervalCard
  · have hempty : Own = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
    simp [Own, hempty]

private theorem p10_1k_cube_hammingDist_comm {d : ℕ}
    (u v : CubeVertex d) : hammingDist u v = hammingDist v u := by
  exact _root_.hammingDist_comm u v

/-- At a fixed selected height, the own-slice IDs inject into the nonbad
crowd around one selected site. -/
theorem p10_1kOddGroupOwnTupleIds_height_fiber_mass_bound
    {n m : ℕ} (δ : ℝ) (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hgood : (p10_1kHeightParams n m δ).GoodHeights Sites P A E)
    (hmatch : ∀ v, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites)
    (b : ℕ)
    (hfiber : ∃ id ∈ p10_1kOddGroupOwnTupleIds δ q selected,
      id.2.2.val = b) :
    (((p10_1kOddGroupOwnTupleIds δ q selected).filter
      (fun id => id.2.2.val = b)).card : ℝ) ≤
        (n : ℝ) ^ (p10_1kHeightParams n m δ).b := by
  classical
  let p := p10_1kHeightParams n m δ
  let Own := p10_1kOddGroupOwnTupleIds δ q selected
  let Fiber := Own.filter (fun id => id.2.2.val = b)
  obtain ⟨id₀, hid₀, hlevel₀⟩ := hfiber
  obtain ⟨v₀, loc₀, j₀, hv₀, henv₀, hsel₀, hid₀eq, hheight₀,
    hj₀, hbad₀, hE₀, hA₀, hP₀, hlocLevel₀, hdist₀⟩ :=
    p10_1k_ownTupleId_selection_spec δ q selected Sites P A E τ
      hlegal hmatch hinSites id₀ hid₀
  let level : P10_1kProspectiveId n m δ → ℕ := fun id => id.2.2.val
  have hlevelId₀ : level id₀ = loc₀.2.val := by
    dsimp [level]
    rw [hid₀eq]
  have hj₀b : j₀.val = b := by
    calc
      j₀.val = loc₀.2.val := congrArg Fin.val hlocLevel₀.symm
      _ = level id₀ := hlevelId₀.symm
      _ = b := hlevel₀
  have hheightB : p.height Sites P A E p.Rlong v₀ = b :=
    hheight₀.trans hj₀b
  have hgood₀ := hgood v₀ hv₀
  have hbH : b < p.H := by
    rw [← hheightB]
    exact hgood₀.1
  let j : Fin (p.H + 1) := ⟨b, by omega⟩
  have hnoBadN : ¬ p.BadN P A E v₀ b := by
    rw [← hheightB]
    exact hgood₀.2.1
  have hnotBad₀ : ¬ p.Bad P A E v₀ j := by
    intro hbad
    apply hnoBadN
    refine ⟨by omega, ?_⟩
    simpa [j] using hbad
  let qres : CubeVertex p.d := q.2
  have hq₀ : hammingDist v₀ qres ≤ 3 := by
    change hammingDist v₀ q.2 ≤ 3
    exact p10_1k_envelope_same_slice_residual_dist_le_three_symm
      q (q.1, v₀) henv₀ rfl
  let crowd : Finset (CubeVertex p.d) :=
    Finset.univ.filter fun u =>
      P (u, j) = true ∧ A (u, j) = true ∧
        hammingDist u v₀ ≤ p.r + p.D
  have hnotCrowded : ¬ (p.n : ℝ) ^ p.b < (crowd.card : ℝ) := by
    intro hlarge
    apply hnotBad₀
    right
    simpa [HDParams.Bad, crowd] using hlarge
  have hcrowd : (crowd.card : ℝ) ≤ (p.n : ℝ) ^ p.b := le_of_not_gt hnotCrowded
  have hmap : Set.MapsTo (fun id : P10_1kProspectiveId n m δ => id.2.1)
      (Fiber : Set (P10_1kProspectiveId n m δ)) (crowd : Set (CubeVertex p.d)) := by
    intro id hid
    have hparts := Finset.mem_filter.mp hid
    have hown : id ∈ Own := hparts.1
    obtain ⟨v, loc, j', hv, henv, hsel, hideq, hheight, hj', hbad,
      hE, hA, hP, hlocLevel, hdist⟩ :=
      p10_1k_ownTupleId_selection_spec δ q selected Sites P A E τ
        hlegal hmatch hinSites id hown
    have hlevelId : level id = loc.2.val := by
      dsimp [level]
      rw [hideq]
    have hlocVal : loc.2.val = b := hlevelId.symm.trans hparts.2
    have hlocEq : loc.2 = j := Fin.ext hlocVal
    have hq : hammingDist qres v ≤ 3 := by
      change hammingDist q.2 v ≤ 3
      exact p10_1k_envelope_same_slice_residual_dist_le_three
        q (q.1, v) henv rfl
    have hbaseDist : hammingDist v v₀ ≤ p.D := by
      -- The reverse envelope bound for `v₀` and the forward bound for `v`
      -- place both sites within three residual steps of `q`.
      have hqv₀ : hammingDist qres v₀ ≤ 3 := by
        rw [p10_1k_cube_hammingDist_comm]
        exact hq₀
      have hvq : hammingDist v qres ≤ 3 := by
        rw [p10_1k_cube_hammingDist_comm]
        exact hq
      have hdistV : hammingDist v v₀ ≤ 6 := by
        calc
          hammingDist v v₀ ≤ hammingDist v qres + hammingDist qres v₀ :=
            hammingDist_triangle v qres v₀
          _ ≤ 3 + 3 := add_le_add hvq hqv₀
          _ = 6 := by norm_num
      simpa [p, p10_1kHeightParams] using hdistV
    have hcenter : hammingDist loc.1 v₀ ≤ p.r + p.D := by
      calc
        hammingDist loc.1 v₀ ≤ hammingDist loc.1 v + hammingDist v v₀ :=
          hammingDist_triangle loc.1 v v₀
        _ ≤ p.r + p.D := add_le_add hdist hbaseDist
    have hPj : P (loc.1, j) = true := by
      rw [← hlocEq]
      exact hP
    have hAj : A (loc.1, j) = true := by
      rw [← hlocEq]
      exact hA
    have hcenterMap : hammingDist id.2.1 v₀ ≤ p.r + p.D := by
      rw [hideq]
      exact hcenter
    have hPmap : P (id.2.1, j) = true := by
      rw [hideq]
      exact hPj
    have hAmap : A (id.2.1, j) = true := by
      rw [hideq]
      exact hAj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hPmap, hAmap, hcenterMap⟩
  have hinj : (Fiber : Set (P10_1kProspectiveId n m δ)).InjOn
      (fun id => id.2.1) := by
    intro id₁ h₁ id₂ h₂ hcenters
    have hparts₁ := Finset.mem_filter.mp h₁
    have hparts₂ := Finset.mem_filter.mp h₂
    have hslice₁ : id₁.1 = q.1 := by
      have hown := Finset.mem_filter.mp hparts₁.1
      exact hown.2
    have hslice₂ : id₂.1 = q.1 := by
      have hown := Finset.mem_filter.mp hparts₂.1
      exact hown.2
    have hfin₁ : id₁.2.2.val = b := hparts₁.2
    have hfin₂ : id₂.2.2.val = b := hparts₂.2
    apply Prod.ext
    · exact hslice₁.trans hslice₂.symm
    · apply Prod.ext
      · exact hcenters
      · exact Fin.ext (hfin₁.trans hfin₂.symm)
  have hcard := Finset.card_le_card_of_injOn
    (fun id : P10_1kProspectiveId n m δ => id.2.1) hmap hinj
  have hcardReal : (Fiber.card : ℝ) ≤ (crowd.card : ℝ) := by
    exact_mod_cast hcard
  calc
    (Fiber.card : ℝ) ≤ (crowd.card : ℝ) := hcardReal
    _ ≤ (p.n : ℝ) ^ p.b := hcrowd
    _ = (n : ℝ) ^ (p10_1kHeightParams n m δ).b := by rfl

/-- The selected own-slice IDs have at most three height fibers, each bounded
by the nonbad crowd threshold. -/
theorem p10_1kOddGroupOwnTupleIds_card_le_three_mul_ceil
    {n m : ℕ} (δ : ℝ) (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hgood : (p10_1kHeightParams n m δ).GoodHeights Sites P A E)
    (hmatch : ∀ v, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites) :
    (p10_1kOddGroupOwnTupleIds δ q selected).card ≤
      3 * Nat.ceil ((n : ℝ) ^ (p10_1kHeightParams n m δ).b) := by
  classical
  let p := p10_1kHeightParams n m δ
  let Own := p10_1kOddGroupOwnTupleIds δ q selected
  let level : P10_1kProspectiveId n m δ → ℕ := fun id => id.2.2.val
  let T : ℕ := Nat.ceil ((n : ℝ) ^ p.b)
  have hlevels : (Own.image level).card ≤ 3 := by
    simpa [Own, level] using
      p10_1kOddGroupOwnTupleIds_level_image_card_le_three
        δ q selected Sites P A E τ hlegal hgood hmatch hinSites
  apply p10_1k_card_le_levels_mul Own level (Own.image level) 3 T
  · intro id hid
    exact Finset.mem_image.mpr ⟨id, hid, rfl⟩
  · exact hlevels
  · intro b hb
    obtain ⟨id, hid, hlevel⟩ := Finset.mem_image.mp hb
    have hmass := p10_1kOddGroupOwnTupleIds_height_fiber_mass_bound
      δ q selected Sites P A E τ hlegal hgood hmatch hinSites b ⟨id, hid, hlevel⟩
    have hmass' : ((Own.filter (fun id => level id = b)).card : ℝ) ≤
        (n : ℝ) ^ p.b := by
      simpa [Own, level] using hmass
    have hceil : (n : ℝ) ^ p.b ≤ (T : ℝ) := by
      dsimp [T]
      exact Nat.le_ceil _
    have hreal : ((Own.filter (fun id => level id = b)).card : ℝ) ≤
        (T : ℝ) := hmass'.trans hceil
    exact_mod_cast hreal

/-- Once the exponent gap absorbs the rounding constants, the own-slice
fan is bounded by the height-count scale used by P10.1c. -/
theorem p10_1kOddGroupOwnTupleIds_card_le_heightCount
    {n m : ℕ} (δ : ℝ) (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hgood : (p10_1kHeightParams n m δ).GoodHeights Sites P A E)
    (hmatch : ∀ v, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites)
    (hn : 2 ≤ n) (hδ : 0 < δ)
    (hgap : 6 * (n : ℝ) ^ (140 * δ) < (n : ℝ) ^ (141 * δ)) :
    (p10_1kOddGroupOwnTupleIds δ q selected).card ≤
      p10_1kHeightCount n δ := by
  classical
  let x : ℝ := (n : ℝ) ^ (140 * δ)
  let y : ℝ := (n : ℝ) ^ (141 * δ)
  have hxone : 1 ≤ x := by
    dsimp [x]
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    calc
      1 = (n : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ (n : ℝ) ^ (140 * δ) :=
        Real.rpow_le_rpow_of_exponent_le hnreal (by positivity)
  have hceilX : (Nat.ceil x : ℝ) ≤ x + 1 := by
    have hceilNat : Nat.ceil x ≤ Nat.floor x + 1 := Nat.ceil_le_floor_add_one x
    have hcast : (Nat.ceil x : ℝ) ≤ (Nat.floor x : ℝ) + 1 := by
      exact_mod_cast hceilNat
    have hfloor := Nat.floor_le (by positivity : 0 ≤ x)
    linarith
  have hrounded : ((3 * Nat.ceil x : ℕ) : ℝ) ≤ y := by
    calc
      ((3 * Nat.ceil x : ℕ) : ℝ) = 3 * (Nat.ceil x : ℝ) := by norm_num
      _ ≤ 3 * (x + 1) := by gcongr
      _ ≤ 6 * x := by nlinarith [hxone]
      _ ≤ y := le_of_lt (by simpa [x, y] using hgap)
  have hyceil : y ≤ (Nat.ceil y : ℝ) := Nat.le_ceil y
  have hnat : 3 * Nat.ceil x ≤ Nat.ceil y := by
    exact_mod_cast hrounded.trans hyceil
  have hfan := p10_1kOddGroupOwnTupleIds_card_le_three_mul_ceil
    δ q selected Sites P A E τ hlegal hgood hmatch hinSites
  have hfan' : (p10_1kOddGroupOwnTupleIds δ q selected).card ≤
      3 * Nat.ceil x := by
    simpa [x, p10_1kHeightParams] using hfan
  simpa [y, p10_1kHeightCount] using hfan'.trans hnat

/-- With the special-slice count chosen by Proposition 10.1, the full
projected-group scope fits in the rounded fixed-list block count. -/
theorem p10_1kOddGroupTupleIdScope_card_le_fixedListBlockCount
    {n : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n (p10_1kSpecialCount n δ))
    (selected : P10_1kProjectedSite n (p10_1kSpecialCount n δ) →
      Option (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Loc)
    (Sites : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Sites)
    (P A : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Loc → Bool)
    (E : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).EligMap)
    (τ : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Ties)
    (hlegal : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Legal P E Sites)
    (hgood : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).GoodHeights
      Sites P A E)
    (hmatch : ∀ v, selected (q.1, v) =
      (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).selection
        Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites)
    (hn : 2 ≤ n) (hδ : 0 < δ)
    (hgap : 6 * (n : ℝ) ^ (140 * δ) < (n : ℝ) ^ (141 * δ)) :
    (p10_1kOddGroupTupleIdScope δ q selected).card ≤
      p10_1kFixedListBlockCount n δ := by
  have hown := p10_1kOddGroupOwnTupleIds_card_le_heightCount
    δ q selected Sites P A E τ hlegal hgood hmatch hinSites hn hδ hgap
  have hscope := p10_1kOddGroupTupleIdScope_card_le δ q selected
    (p10_1kHeightCount n δ) hown
  simpa [p10_1kFixedListBlockCount, p10_1kSpecialCount, Nat.add_comm] using hscope

/-- The projected-group scope fits P10.1c's block count eventually, uniformly
over legal GoodHeights selectors. -/
theorem p10_1kOddGroupTupleIdScope_card_le_fixedListBlockCount_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (q : P10_1kProjectedSite n (p10_1kSpecialCount n δ))
        (selected : P10_1kProjectedSite n (p10_1kSpecialCount n δ) →
          Option (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Loc)
        (Sites : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Sites)
        (P A : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Loc → Bool)
        (E : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).EligMap)
        (τ : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Ties),
        (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Legal P E Sites →
        (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).GoodHeights
          Sites P A E →
        (∀ v, selected (q.1, v) =
          (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).selection
            Sites P A E τ v) →
        (∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites) →
        (p10_1kOddGroupTupleIdScope δ q selected).card ≤
          p10_1kFixedListBlockCount n δ := by
  have hgap : ∀ᶠ n : ℕ in atTop,
      6 * (n : ℝ) ^ (140 * δ) < (n : ℝ) ^ (141 * δ) :=
    p10_1k_eventually_power_gap (by nlinarith [hδ])
      (by norm_num : (0 : ℝ) < 6)
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hgap, hnlarge] with n hgap hn
  intro q selected Sites P A E τ hlegal hgood hmatch hinSites
  exact p10_1kOddGroupTupleIdScope_card_le_fixedListBlockCount
    δ q selected Sites P A E τ hlegal hgood hmatch hinSites hn hδ hgap

private theorem p10_1k_fixedList_scope_premises_mono
    {k r s : ℕ} {wν w cap z bound : ℝ}
    (hs : s ≤ r)
    (hwidth : wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤ w)
    (hlog : Real.log ((r : ℝ) + 1) ≤ cap)
    (herror : ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp z ≤ bound) :
    wν + Real.log 4 + 2 * (k : ℝ) * (s : ℝ) ≤ w ∧
      Real.log ((s : ℝ) + 1) ≤ cap ∧
      ((s : ℝ) + 1) * (k : ℝ) * (s : ℝ) * Real.exp z ≤ bound := by
  have hsR : (s : ℝ) ≤ (r : ℝ) := by exact_mod_cast hs
  have hsPlus : (s : ℝ) + 1 ≤ (r : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hs 1
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hsNonneg : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hsize : 2 * (k : ℝ) * (s : ℝ) ≤ 2 * (k : ℝ) * (r : ℝ) := by
    calc
      2 * (k : ℝ) * (s : ℝ) = 2 * ((k : ℝ) * (s : ℝ)) := by ring
      _ ≤ 2 * ((k : ℝ) * (r : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsR hk) (by norm_num)
      _ = 2 * (k : ℝ) * (r : ℝ) := by ring
  have hprod : ((s : ℝ) + 1) * (k : ℝ) * (s : ℝ) ≤
      ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) := by
    calc
      ((s : ℝ) + 1) * (k : ℝ) * (s : ℝ) ≤
          ((r : ℝ) + 1) * (k : ℝ) * (s : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsPlus hk) hsNonneg
      _ ≤ ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) :=
        mul_le_mul_of_nonneg_left hsR (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · linarith [hwidth, hsize]
  · exact (Real.log_le_log (by positivity) hsPlus).trans hlog
  · calc
      ((s : ℝ) + 1) * (k : ℝ) * (s : ℝ) * Real.exp z ≤
          ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp z :=
        mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg z)
      _ ≤ bound := herror

/-- For a fixed pre-cluster group scope, the local fixed-list failure has the
P10.1c exponential probability bound. -/
theorem p10_1kProjectedGroupFailure_probability_bound
    {n N m k : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {ζ δ : ℝ} {A B X Y : Finset (Fin N)}
    (hfixed : P10_1cFixedListTest)
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (hBY : B ⊆ Y) (η₀ : ℝ)
    (hdisc : DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀)
      ((n : ℝ) ^ (-η₀)))
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (μ : P10_1kProspectiveId n m δ → Law N)
    (group : P10_1kProjectedSite n m)
    (hμscope : ∀ id ∈ p10_1kOddGroupTupleIdScope δ group selected,
      (μ id).SupportedIn X ∧ (μ id).WidthLE ((n : ℝ) ^ δ))
    (hε : 0 ≤ (n : ℝ) ^ (-η₀))
    (hεa : 100 * (n : ℝ) ^ (-η₀) ≤ (n : ℝ) ^ (-δ))
    (ha : (n : ℝ) ^ (-δ) ≤ 1 / 10)
    (hwidth : (n : ℝ) ^ δ + Real.log 4 +
      2 * (k : ℝ) *
        ((p10_1kOddGroupTupleIdScope δ group selected).card : ℝ) ≤
          (n : ℝ) ^ η₀)
    (hlog : Real.log
      (((p10_1kOddGroupTupleIdScope δ group selected).card : ℝ) + 1) ≤
        ((n : ℝ) ^ (-δ)) ^ 2 * (k : ℝ) / 100)
    (herror :
      (((p10_1kOddGroupTupleIdScope δ group selected).card : ℝ) + 1) *
        (k : ℝ) *
        ((p10_1kOddGroupTupleIdScope δ group selected).card : ℝ) *
        Real.exp ((n : ℝ) ^ δ - (n : ℝ) ^ η₀) ≤
          Real.exp (-(((n : ℝ) ^ (-δ)) ^ 2 * (k : ℝ)) / 50))
    (defaultTuple : Fin k → Fin N) :
    ∃ c₅ : ℝ, 0 < c₅ ∧
      (p10_1kIdTupleArrayLaw (k := k) μ).pr
        (p10_1kProjectedGroupFixedListFailure data selected μ group
          ((n : ℝ) ^ (-δ))) ≤
        Real.exp (-c₅ * ((n : ℝ) ^ (-δ)) ^ 2 * (k : ℝ)) := by
  let S := p10_1kOddGroupTupleIdScope δ group selected
  let e : Fin S.card ≃ {id // id ∈ S} := S.equivFin.symm
  let μblocks : Fin S.card → Law N := fun b => μ (e b).1
  have hblocks : ∀ b, (μblocks b).SupportedIn X ∧
      (μblocks b).WidthLE ((n : ℝ) ^ δ) := by
    intro b
    exact hμscope (e b).1 (e b).2
  let ρ := p10_1kClusterPrior data
  let ν := p10_1kClusterAggregate data
  have hν : ν.WidthLE ((n : ℝ) ^ δ) := by
    intro y
    exact p10_1kClusterAggregate_width data y
  have hD : ∀ j, (data.D j).SupportedIn Y := by
    intro j y hy
    exact data.D_supported j y (fun hyB => hy (hBY hyB))
  have haggregate : ∀ y, (∑ j, ρ.w j * (data.D j).w y) ≤ 4 * ν.w y := by
    intro y
    have heq : (∑ j, ρ.w j * (data.D j).w y) = ν.w y := by
      simp [ρ, ν, p10_1kClusterAggregate, p10_1kClusterPrior, Law.mix]
    rw [heq]
    have hnonneg := ν.nonneg y
    nlinarith
  obtain ⟨c₅, hc₅, hfail⟩ := p10_1kIdTupleArrayLaw_fixedListFailure_test_bound
    hfixed μ S S.card e E X Y G ρ data.D ν
      ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) ((n : ℝ) ^ (-δ))
      ((n : ℝ) ^ δ) ((n : ℝ) ^ δ)
      hblocks hν hD haggregate hdisc hε hεa ha hwidth hlog herror defaultTuple
  have hfail' :
      (p10_1kIdTupleArrayLaw (k := k) μ).pr
        (p10_1kProjectedGroupFixedListFailure data selected μ group
          ((n : ℝ) ^ (-δ))) ≤
        Real.exp (-c₅ * ((n : ℝ) ^ (-δ)) ^ 2 * (k : ℝ)) := by
    change (p10_1kIdTupleArrayLaw (k := k) μ).pr (fun W =>
      fixedListFailure E G (p10_1kClusterPrior data) data.D μblocks
        ((n : ℝ) ^ (-δ)) (fun b i => W (e b).1 i)) ≤ _
    exact hfail
  exact ⟨c₅, hc₅, hfail'⟩

/-- Apply the projected-group fixed-list estimate using the global rounded
block-count premises, once the scope is known to fit that count. -/
theorem p10_1kProjectedGroupFailure_probability_bound_from_block_count
    {n N m k : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {ζ δ : ℝ} {A B X Y : Finset (Fin N)}
    (hfixed : P10_1cFixedListTest)
    (data : P10_1kClusterData (n := n) (N := N) E G ζ δ A B)
    (hBY : B ⊆ Y) (η₀ : ℝ)
    (hdisc : DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀)
      ((n : ℝ) ^ (-η₀)))
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (μ : P10_1kProspectiveId n m δ → Law N)
    (group : P10_1kProjectedSite n m)
    (hμscope : ∀ id ∈ p10_1kOddGroupTupleIdScope δ group selected,
      (μ id).SupportedIn X ∧ (μ id).WidthLE ((n : ℝ) ^ δ))
    (hε : 0 ≤ (n : ℝ) ^ (-η₀))
    (hεa : 100 * (n : ℝ) ^ (-η₀) ≤ (n : ℝ) ^ (-δ))
    (ha : (n : ℝ) ^ (-δ) ≤ 1 / 10)
    (hwidth : (n : ℝ) ^ δ + Real.log 4 +
      2 * (k : ℝ) * (p10_1kFixedListBlockCount n δ : ℝ) ≤
        (n : ℝ) ^ η₀)
    (hlog : Real.log
      ((p10_1kFixedListBlockCount n δ : ℝ) + 1) ≤
        ((n : ℝ) ^ (-δ)) ^ 2 * (k : ℝ) / 100)
    (herror : ((p10_1kFixedListBlockCount n δ : ℝ) + 1) * (k : ℝ) *
      (p10_1kFixedListBlockCount n δ : ℝ) *
      Real.exp ((n : ℝ) ^ δ - (n : ℝ) ^ η₀) ≤
        Real.exp (-(((n : ℝ) ^ (-δ)) ^ 2 * (k : ℝ)) / 50))
    (hscope : (p10_1kOddGroupTupleIdScope δ group selected).card ≤
      p10_1kFixedListBlockCount n δ)
    (defaultTuple : Fin k → Fin N) :
    ∃ c₅ : ℝ, 0 < c₅ ∧
      (p10_1kIdTupleArrayLaw (k := k) μ).pr
        (p10_1kProjectedGroupFixedListFailure data selected μ group
          ((n : ℝ) ^ (-δ))) ≤
        Real.exp (-c₅ * ((n : ℝ) ^ (-δ)) ^ 2 * (k : ℝ)) := by
  have hmono := p10_1k_fixedList_scope_premises_mono
    hscope hwidth hlog herror
  exact p10_1kProjectedGroupFailure_probability_bound hfixed data hBY η₀ hdisc
    selected μ group hμscope hε hεa ha hmono.1 hmono.2.1 hmono.2.2 defaultTuple

/-- Under the rounded Section 10 scales, every legal GoodHeights projected
group has the repaired P10.1c exponential fixed-list failure bound. -/
theorem p10_1kProjectedGroupFailure_probability_bound_eventually
    (hfixed : P10_1cFixedListTest) (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
        (Ac Bc X Y : Finset (Fin N))
        (data : P10_1kClusterData (n := n) (N := N) E G ζ δ Ac Bc),
        Ac ⊆ X → Bc ⊆ Y →
        DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀)
          ((n : ℝ) ^ (-η₀)) →
        ∀ (q : P10_1kProjectedSite n (p10_1kSpecialCount n δ))
          (selected : P10_1kProjectedSite n (p10_1kSpecialCount n δ) →
            Option (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Loc)
          (Sites : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Sites)
          (P Act : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Loc → Bool)
          (SelElig : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).EligMap)
          (τ : (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Ties),
          (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).Legal
            P SelElig Sites →
          (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).GoodHeights
            Sites P Act SelElig →
          (∀ v, selected (q.1, v) =
            (p10_1kHeightParams n (p10_1kSpecialCount n δ) δ).selection
              Sites P Act SelElig τ v) →
          (∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites) →
          ∀ (μ : P10_1kProspectiveId n (p10_1kSpecialCount n δ) δ → Law N),
            (∀ id ∈ p10_1kOddGroupTupleIdScope δ q selected,
              (μ id).SupportedIn X ∧ (μ id).WidthLE ((n : ℝ) ^ δ)) →
            (Fin (p10_1kTupleListLength n δ) → Fin N) →
            ∃ c₅ : ℝ, 0 < c₅ ∧
              (p10_1kIdTupleArrayLaw
                (k := p10_1kTupleListLength n δ) μ).pr
                (p10_1kProjectedGroupFixedListFailure data selected μ q
                  ((n : ℝ) ^ (-δ))) ≤
              Real.exp (-c₅ * ((n : ℝ) ^ (-δ)) ^ 2 *
                (p10_1kTupleListLength n δ : ℝ)) := by
  have hbasic := p10_1k_fixedList_basic_premises_eventually
    η₀ ζ δ hη₀ hζ hδ hδsmall
  have hexception := p10_1k_fixedList_exceptional_premise_eventually
    η₀ ζ δ hη₀ hζ hδ hδsmall
  have hscopeEvent :=
    p10_1kOddGroupTupleIdScope_card_le_fixedListBlockCount_eventually δ hδ
  filter_upwards [hbasic, hexception, hscopeEvent] with n hb he hs
  let r : ℕ := p10_1kFixedListBlockCount n δ
  let k : ℕ := p10_1kTupleListLength n δ
  let ε : ℝ := (n : ℝ) ^ (-η₀)
  let a : ℝ := (n : ℝ) ^ (-δ)
  let w : ℝ := (n : ℝ) ^ η₀
  let wμ : ℝ := (n : ℝ) ^ δ
  let wν : ℝ := (n : ℝ) ^ δ
  have hb' : 0 ≤ ε ∧ 100 * ε ≤ a ∧ a ≤ 1 / 10 ∧
      wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤ w ∧
      Real.log ((r : ℝ) + 1) ≤ a ^ 2 * (k : ℝ) / 100 := by
    simpa [r, k, ε, a, w, wμ, wν, p10_1kFixedListBlockCount,
      p10_1kTupleListLength] using hb
  have he' : ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) *
      Real.exp (wμ - w) ≤ Real.exp (-(a ^ 2 * (k : ℝ)) / 50) := by
    simpa [r, k, ε, a, w, wμ, wν, p10_1kFixedListBlockCount,
      p10_1kTupleListLength] using he
  rcases hb' with ⟨hε, hεa, ha, hwidth, hlog⟩
  intro N E G Ac Bc X Y data hAX hBY hdisc
    q selected Sites P Act SelElig τ hlegal hgood hmatch hinSites μ hμscope
    defaultTuple
  have hscope := hs q selected Sites P Act SelElig τ
    hlegal hgood hmatch hinSites
  have hwidth' : (n : ℝ) ^ δ + Real.log 4 +
      2 * (k : ℝ) * (r : ℝ) ≤ (n : ℝ) ^ η₀ := by
    simpa [r, k, w, wν] using hwidth
  have hlog' : Real.log ((r : ℝ) + 1) ≤
      ((n : ℝ) ^ (-δ)) ^ 2 * (k : ℝ) / 100 := by
    simpa [r, k, a] using hlog
  have herror' : ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) *
      Real.exp ((n : ℝ) ^ δ - (n : ℝ) ^ η₀) ≤
        Real.exp (-(((n : ℝ) ^ (-δ)) ^ 2 * (k : ℝ)) / 50) := by
    simpa [r, k, a, w, wμ] using he'
  have hscope' : (p10_1kOddGroupTupleIdScope δ q selected).card ≤ r := by
    simpa [r] using hscope
  exact p10_1kProjectedGroupFailure_probability_bound_from_block_count
    hfixed data hBY η₀ hdisc selected μ q hμscope hε hεa ha
    hwidth' hlog' herror' hscope' defaultTuple

/-- An even role meets at most `n` projected odd groups, since its `n` ordinary
neighbors cover the incident group set. -/
theorem p10_1k_incidentOddGroups_card_le {n m : ℕ} (hm : m ≤ n)
    (a : P10_1kEvenRole n) :
    (p10_1kIncidentOddGroups hm a).card ≤ n := by
  classical
  let S := Finset.univ.image (fun j : Fin n =>
    p10_1kProjectedVertex hm (p10_1kFlipCoordinate a.1 j))
  have hsubset : p10_1kIncidentOddGroups hm a ⊆ S := by
    intro q hq
    obtain ⟨b, hadj, hbq⟩ := (p10_1k_mem_incidentOddGroups hm a q).mp hq
    have hdist : hammingDist a.1 b.1 = 1 := by exact hadj
    obtain ⟨j, hflip⟩ := p10_1k_flipCoordinate_of_hammingDist_one a.1 b.1 hdist
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    calc
      p10_1kProjectedVertex hm (p10_1kFlipCoordinate a.1 j) =
          p10_1kProjectedVertex hm b.1 := by rw [hflip]
      _ = q := hbq
  calc
    (p10_1kIncidentOddGroups hm a).card ≤ S.card := Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

/-- A projected odd group contains at most the residual projection fiber size. -/
theorem p10_1k_oddGroup_card_le (n m : ℕ) (hm : m ≤ n)
    (q : P10_1kProjectedSite n m) :
    Fintype.card {b : P10_1kOddRole n // b ∈ p10_1kOddGroupRoles hm q} ≤
      2 ^ (∑ i : Fin (n - m).bitIndices.length, (n - m).bitIndices.get i) := by
  classical
  by_cases hnon : (p10_1kOddGroupRoles hm q).Nonempty
  · obtain ⟨b, hb⟩ := hnon
    have hbsite : p10_1kProjectedVertex hm b.1 = q := by
      simpa [p10_1kOddGroupRoles] using hb
    let s₀ := p10_1kResidualWord hm b.1
    let f : {b : P10_1kOddRole n // b ∈ p10_1kOddGroupRoles hm q} →
        {s : Fin (n - m) → Bool //
          p10_1k_projectedWord (n - m) s = q.2} := fun x =>
      ⟨p10_1kResidualWord hm x.1.1, by
        have hxsite : p10_1kProjectedVertex hm x.1.1 = q := by
          simpa [p10_1kOddGroupRoles] using x.2
        exact congrArg Prod.snd hxsite⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply (p10_1kSliceWordEquiv hm).injective
      have hxsite : p10_1kProjectedVertex hm x.1.1 = q := by
        simpa [p10_1kOddGroupRoles] using x.2
      have hysite : p10_1kProjectedVertex hm y.1.1 = q := by
        simpa [p10_1kOddGroupRoles] using y.2
      apply Prod.ext
      · exact (congrArg Prod.fst hxsite).trans (congrArg Prod.fst hysite).symm
      · exact congrArg Subtype.val hxy
    have hcard := Fintype.card_le_of_injective f hf
    have htarget : q.2 = p10_1k_projectedWord (n - m) s₀ := by
      exact (congrArg Prod.snd hbsite).symm
    have hfiber : Fintype.card {s : Fin (n - m) → Bool //
        p10_1k_projectedWord (n - m) s = q.2} =
        2 ^ (∑ i : Fin (n - m).bitIndices.length, (n - m).bitIndices.get i) := by
      simpa [htarget, s₀] using p10_1k_projectedFiber_card_eq_pow (n - m) s₀
    exact hcard.trans (le_of_eq hfiber)
  · have hgroup : p10_1kOddGroupRoles hm q = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnon
    simp [hgroup]

/-- Multiply pointwise likelihood comparisons when the left factors are nonnegative. -/
theorem p10_1k_product_likelihood_comparison
    {A B : Type*} [Fintype A] [Fintype B] {m : ℕ}
    (L Q : Fin m → A → B → ℝ) (s : Fin m → ℝ)
    (hL : ∀ i a b, 0 ≤ L i a b)
    (hcompare : ∀ i a b, L i a b ≤ Real.exp (s i) * Q i a b) :
    ∀ a b, (∏ i : Fin m, L i a b) ≤
      Real.exp (∑ i : Fin m, s i) * ∏ i : Fin m, Q i a b := by
  intro a b
  calc
    (∏ i : Fin m, L i a b) ≤ ∏ i : Fin m, (Real.exp (s i) * Q i a b) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hL i a b
      · intro i hi
        exact hcompare i a b
    _ = (∏ i : Fin m, Real.exp (s i)) * ∏ i : Fin m, Q i a b :=
      Finset.prod_mul_distrib
    _ = Real.exp (∑ i : Fin m, s i) * ∏ i : Fin m, Q i a b := by
      rw [← Real.exp_sum]

end HypercubeRamsey.S10
