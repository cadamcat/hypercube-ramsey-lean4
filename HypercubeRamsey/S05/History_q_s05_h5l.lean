import HypercubeRamsey.S05.Experiment
import HypercubeRamsey.Tools.CubeGeometry

namespace HypercubeRamsey.Lane_q_s05_h5l

open Classical
open Filter
open OAI.HypercubeRamsey
open scoped Topology

noncomputable def pinDirac5 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ω₀ : Ω) : FinProb Ω where
  w ω := if ω = ω₀ then 1 else 0
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp

private noncomputable def oddSignFiber {n m : ℕ} (g : ChunkGeometry5 n m) (t : CubeVertex m) :
    Finset (OddRole5 n) := Finset.univ.filter fun r => g.sign r.1 = t

theorem hammingDist_symm5 {m : ℕ} (x y : CubeVertex m) :
    HypercubeRamsey.hammingDist x y = HypercubeRamsey.hammingDist y x := by
  simp [HypercubeRamsey.hammingDist, ne_comm]

theorem oddSignFiber_card {n m : ℕ} (g : ChunkGeometry5 n m)
    (hG : ChunkEstimates5 g) (t : CubeVertex m) :
    ((oddSignFiber g t).card : ℝ) * (2 : ℝ) ^ m = Fintype.card (OddRole5 n) := by
  classical
  let V : Finset (CubeVertex n) :=
    Finset.univ.filter fun x => ¬ IsEvenRole x ∧ g.sign x = t
  let R : Finset (CubeVertex n) := Finset.univ.filter fun x => ¬ IsEvenRole x
  have hVcard : Fintype.card {x : CubeVertex n // x ∈ V} = V.card := by
    exact Fintype.card_coe V
  have hRcard : Fintype.card {x : CubeVertex n // x ∈ R} = R.card := by
    exact Fintype.card_coe R
  let eV : {r : OddRole5 n // g.sign r.1 = t} ≃ {x : CubeVertex n // x ∈ V} := {
    toFun := fun r => ⟨r.1.1, by simpa [V] using And.intro r.1.2 r.2⟩
    invFun := fun x => ⟨⟨x.1, (Finset.mem_filter.mp x.2).2.1⟩,
      (Finset.mem_filter.mp x.2).2.2⟩
    left_inv := by intro r; cases r; rfl
    right_inv := by intro x; cases x; rfl
  }
  have eR : (OddRole5 n) ≃ {x : CubeVertex n // x ∈ R} := {
    toFun := fun r => ⟨r.1, by simpa [R] using r.2⟩
    invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
    left_inv := by intro r; cases r; rfl
    right_inv := by intro x; cases x; rfl
  }
  have hEqV : (oddSignFiber g t).card = V.card := by
    calc
      (oddSignFiber g t).card = Fintype.card {r : OddRole5 n // g.sign r.1 = t} := by
        simpa [oddSignFiber] using (Fintype.card_coe (oddSignFiber g t)).symm
      _ = Fintype.card {x : CubeVertex n // x ∈ V} := Fintype.card_congr eV
      _ = V.card := hVcard
  have hEqR : (Fintype.card (OddRole5 n) : ℝ) = (R.card : ℝ) := by
    calc
      (Fintype.card (OddRole5 n) : ℝ) = (Fintype.card {x : CubeVertex n // x ∈ R} : ℝ) :=
        congrArg (fun k : ℕ => (k : ℝ)) (Fintype.card_congr eR)
      _ = (R.card : ℝ) := by rw [hRcard]
  have hUniform := hG.sign_uniform false t
  have hUniform' : (V.card : ℝ) * (2 : ℝ) ^ m = (R.card : ℝ) := by
    simpa [V, R] using hUniform
  calc
    ((oddSignFiber g t).card : ℝ) * (2 : ℝ) ^ m =
        (V.card : ℝ) * (2 : ℝ) ^ m := by rw [hEqV]
    _ = (R.card : ℝ) := hUniform'
    _ = Fintype.card (OddRole5 n) := hEqR.symm

theorem oddNearSign_card_le {n m : ℕ} (g : ChunkGeometry5 n m)
    (hG : ChunkEstimates5 g) (t : CubeVertex m) (d : ℕ) :
    ((Finset.univ.filter fun r : OddRole5 n =>
        hammingDist (g.sign r.1) t ≤ d).card : ℝ) ≤
      ((Finset.univ.filter fun s : CubeVertex m => hammingDist s t ≤ d).card : ℝ) *
        (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := by
  classical
  let S : Finset (CubeVertex m) := Finset.univ.filter fun s => hammingDist s t ≤ d
  let A : Finset (OddRole5 n) := Finset.univ.filter fun r => hammingDist (g.sign r.1) t ≤ d
  have hsub : A ⊆ S.biUnion (oddSignFiber g) := by
    intro r hr
    have hrA := (Finset.mem_filter.mp hr).2
    refine Finset.mem_biUnion.mpr ⟨g.sign r.1, ?_, ?_⟩
    · simpa [S] using hrA
    · simp [oddSignFiber]
  have hcard : (A.card : ℝ) ≤ ∑ s ∈ S, ((oddSignFiber g s).card : ℝ) := by
    calc
      (A.card : ℝ) ≤ ((S.biUnion (oddSignFiber g)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ s ∈ S, ((oddSignFiber g s).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
  have hsum : ∑ s ∈ S, ((oddSignFiber g s).card : ℝ) =
      (S.card : ℝ) * (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := by
    calc
      ∑ s ∈ S, ((oddSignFiber g s).card : ℝ) =
          ∑ s ∈ S, (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := by
            apply Finset.sum_congr rfl
            intro s hs
            apply (eq_div_iff (pow_ne_zero _ (by norm_num))).2
            have h := oddSignFiber_card g hG s
            nlinarith [h]
      _ = (S.card : ℝ) * (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  rw [show (Finset.univ.filter fun r : OddRole5 n =>
      hammingDist (g.sign r.1) t ≤ d) = A by rfl,
    show (Finset.univ.filter fun s : CubeVertex m => hammingDist s t ≤ d) = S by rfl]
  calc
    (A.card : ℝ) ≤ ∑ s ∈ S, ((oddSignFiber g s).card : ℝ) := hcard
    _ = (S.card : ℝ) * (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := hsum

theorem pi_expect_singleton5 {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (P : I → FinProb Ω) (i : I) (F : Ω → ℝ) (ω₀ : Ω) :
    (FinProb.pi P).expect (fun ω => F (ω i)) = (P i).expect F := by
  classical
  let f : (∀ j : I, Ω) → ℝ := fun ω => F (ω i)
  have hdep : FinProb.DependsOn f {i} := by
    intro ω ω' hagree
    simp [f, hagree i (by simp)]
  let J := {j : I // j ∈ ({i} : Finset I)}
  letI : Unique J := {
    default := ⟨i, Finset.mem_singleton_self i⟩
    uniq := by
      intro j
      apply Subtype.ext
      exact Finset.mem_singleton.mp j.property
  }
  let e : (∀ j : J, Ω) ≃ Ω := Equiv.piUnique (fun _ : J => Ω)
  have h := FinProb.pi_expect_depends P {i} f (fun _ => ω₀) hdep
  calc
    (FinProb.pi P).expect (fun ω => F (ω i)) =
          (FinProb.pi (fun j : J => P j.1)).expect
          (fun a => f ((Equiv.piEquivPiSubtypeProd (fun j => j ∈ ({i} : Finset I))
            (fun _ => Ω)).symm (a, fun _ => ω₀))) := by
          simpa [f, J] using h
    _ = (P i).expect F := by
      simp only [FinProb.expect, FinProb.pi]
      calc
        (∑ a : ∀ j : J, Ω,
              (∏ j : J, (P j.1).w (a j)) *
              f ((Equiv.piEquivPiSubtypeProd (fun j => j ∈ ({i} : Finset I))
                (fun _ => Ω)).symm (a, fun _ => ω₀))) =
            ∑ a : ∀ j : J, Ω, (P i).w (a default) * F (a default) := by
              apply Finset.sum_congr rfl
              intro a ha
              have hdefault : (⟨i, Finset.mem_singleton_self i⟩ : J) = default :=
                Subsingleton.elim _ _
              have hdefaultVal : (default : J).1 = i := congrArg Subtype.val hdefault.symm
              calc
                (∏ j : J, (P j.1).w (a j)) *
                    f ((Equiv.piEquivPiSubtypeProd (fun j => j ∈ ({i} : Finset I))
                      (fun _ => Ω)).symm (a, fun _ => ω₀)) =
                    (P (default : J).1).w (a default) * F (a default) := by
                      rw [Fintype.prod_unique]
                      simp only [f, Equiv.piEquivPiSubtypeProd_symm_apply,
                        dif_pos (Finset.mem_singleton_self i)]
                      rw [hdefault]
                _ = (P i).w (a default) * F (a default) := by rw [hdefaultVal]
        _ = ∑ y : Ω, (P i).w y * F y := by
              simpa [e, Equiv.piUnique] using
                (Equiv.sum_comp e (fun y : Ω => (P i).w y * F y))
        _ = (P i).expect F := rfl

theorem oddNearSign_entropy_card_le {n m : ℕ} (g : ChunkGeometry5 n m)
    (hG : ChunkEstimates5 g) (t : CubeVertex m) (d : ℕ)
    (hm : 0 < m) (hd : d ≤ m / 2) :
    ((Finset.univ.filter fun r : OddRole5 n =>
        hammingDist (g.sign r.1) t ≤ d).card : ℝ) ≤
      Real.exp (Real.binEntropy ((d : ℝ) / m) * m) *
        (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := by
  have hball := HypercubeRamsey.hammingBall_volume_bound hm hd t
  have hball' : ((Finset.univ.filter fun s : CubeVertex m =>
      hammingDist s t ≤ d).card : ℝ) ≤ Real.exp (Real.binEntropy ((d : ℝ) / m) * m) := by
    simpa [HypercubeRamsey.hammingBall, HypercubeRamsey.hammingDist, ne_comm] using hball
  have hnear := oddNearSign_card_le g hG t d
  have hfactor : 0 ≤ (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := by positivity
  calc
    ((Finset.univ.filter fun r : OddRole5 n =>
        hammingDist (g.sign r.1) t ≤ d).card : ℝ) ≤
        ((Finset.univ.filter fun s : CubeVertex m => hammingDist s t ≤ d).card : ℝ) *
          (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := hnear
    _ = ((Finset.univ.filter fun s : CubeVertex m => hammingDist s t ≤ d).card : ℝ) *
          ((Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m) := by ring
    _ ≤ Real.exp (Real.binEntropy ((d : ℝ) / m) * m) *
          ((Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_right hball' hfactor
    _ = Real.exp (Real.binEntropy ((d : ℝ) / m) * m) *
          (Fintype.card (OddRole5 n) : ℝ) / (2 : ℝ) ^ m := by ring

theorem sqrtRadiusRatio_tendsto {γ K' χ : ℝ} (p : Params5 γ K' χ) (C : ℕ) :
    Tendsto (fun n => (C : ℝ) * (Nat.sqrt (p.m n) : ℝ) / (p.m n : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ p.alpha) atTop atTop :=
    (tendsto_rpow_atTop p.halpha.1).comp tendsto_natCast_atTop_atTop
  have hm (n : ℕ) : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := by
    dsimp [Params5.m]
    exact Nat.le_ceil _
  have hmTop : Tendsto (fun n => (p.m n : ℝ)) atTop atTop := tendsto_atTop_mono hm hpow
  have hrootTop : Tendsto (fun n => (Nat.sqrt (p.m n) : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    let k : ℕ := ⌈max b 0⌉₊
    have hk : ∀ᶠ n : ℕ in atTop, (k : ℝ) ^ 2 ≤ (p.m n : ℝ) :=
      hmTop.eventually_ge_atTop ((k : ℝ) ^ 2)
    filter_upwards [hk] with n hn
    have hn' : k ^ 2 ≤ p.m n := by exact_mod_cast hn
    have hroot : k ≤ Nat.sqrt (p.m n) := Nat.le_sqrt'.2 hn'
    have hceil : max b 0 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.le_ceil (max b 0))
    exact (le_max_left b 0).trans (hceil.trans (by exact_mod_cast hroot))
  have hInv : Tendsto (fun n => (Nat.sqrt (p.m n) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hrootTop
  have hUpper : Tendsto (fun n => (C : ℝ) * (Nat.sqrt (p.m n) : ℝ)⁻¹) atTop (𝓝 0) :=
    by simpa using tendsto_const_nhds.mul hInv
  have hle : ∀ n : ℕ,
      (C : ℝ) * (Nat.sqrt (p.m n) : ℝ) / (p.m n : ℝ) ≤
        (C : ℝ) * (Nat.sqrt (p.m n) : ℝ)⁻¹ := by
    intro n
    by_cases hmzero : p.m n = 0
    · simp [hmzero]
    · have hmnNat : 1 ≤ p.m n := Nat.one_le_iff_ne_zero.mpr hmzero
      have hmpos : 0 < (p.m n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hmzero)
      have hsNat : 1 ≤ Nat.sqrt (p.m n) := Nat.le_sqrt'.2 (by omega)
      have hspos : 0 < (Nat.sqrt (p.m n) : ℝ) := by exact_mod_cast hsNat
      have hsqNat := Nat.sqrt_le' (p.m n)
      have hsq : (Nat.sqrt (p.m n) : ℝ) ^ 2 ≤ (p.m n : ℝ) := by exact_mod_cast hsqNat
      have hC : 0 ≤ (C : ℝ) := by positivity
      have hmul : (C : ℝ) * (Nat.sqrt (p.m n) : ℝ) ^ 2 ≤
          (C : ℝ) * (p.m n : ℝ) := mul_le_mul_of_nonneg_left hsq hC
      apply (div_le_iff₀ hmpos).2
      calc
        (C : ℝ) * (Nat.sqrt (p.m n) : ℝ) ≤
            (C : ℝ) * (p.m n : ℝ) / (Nat.sqrt (p.m n) : ℝ) :=
          (le_div_iff₀ hspos).2 (by nlinarith)
        _ = (C : ℝ) * (Nat.sqrt (p.m n) : ℝ)⁻¹ * (p.m n : ℝ) := by ring
  apply squeeze_zero (fun n => div_nonneg (by positivity) (Nat.cast_nonneg _)) hle
  simpa [div_eq_mul_inv] using hUpper

theorem entropySqrtRadius_eventually {γ K' χ : ℝ} (p : Params5 γ K' χ) (C : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      Real.binEntropy ((C : ℝ) * (Nat.sqrt (p.m n) : ℝ) / (p.m n : ℝ)) < Real.log 2 / 2 := by
  have hratio := sqrtRadiusRatio_tendsto p C
  have hent : Tendsto
      (fun n => Real.binEntropy ((C : ℝ) * (Nat.sqrt (p.m n) : ℝ) / (p.m n : ℝ)))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.binEntropy_continuous.continuousAt.tendsto.comp hratio
  have hpos : 0 < Real.log 2 / 2 := by positivity
  exact (hent.eventually (Iio_mem_nhds hpos))

theorem nearLoadExp_tendsto {γ K' χ : ℝ} (p : Params5 γ K' χ) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp
      ((p.m n : ℝ) ^ (15 / 100 : ℝ) - (Real.log 2 / 2) * (p.m n : ℝ)))
      atTop (𝓝 0) := by
  let m : ℕ → ℝ := fun n => (p.m n : ℝ)
  let a : ℝ := Real.log 2 / 2
  let b : ℝ := a / 2
  let r : ℝ := 2 / p.alpha
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hr : 0 < r := by dsimp [r]; exact div_pos (by norm_num) p.halpha.1
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ p.alpha) atTop atTop :=
    (tendsto_rpow_atTop p.halpha.1).comp tendsto_natCast_atTop_atTop
  have hmle (n : ℕ) : (n : ℝ) ^ p.alpha ≤ m n := by
    dsimp [m, Params5.m]
    exact Nat.le_ceil _
  have hmTop : Tendsto m atTop atTop := tendsto_atTop_mono hmle hpow
  have hneg : Tendsto (fun n => m n ^ (-(17 / 20 : ℝ))) atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17 / 20)).comp hmTop
  have hsmall : ∀ᶠ n : ℕ in atTop, m n ^ (-(17 / 20 : ℝ)) < b :=
    hneg.eventually (Iio_mem_nhds hb)
  have hDL : ∀ᶠ n : ℕ in atTop, m n ^ (15 / 100 : ℝ) < b * m n := by
    filter_upwards [hmTop.eventually_gt_atTop 0, hsmall] with n hmn hs
    have hratio : m n ^ (15 / 100 : ℝ) / m n = m n ^ (-(17 / 20 : ℝ)) := by
      have h := Real.rpow_sub hmn
        (15 / 100 : ℝ) 1
      have hexp : (15 / 100 : ℝ) - 1 = -(17 / 20 : ℝ) := by norm_num
      rw [hexp] at h
      simpa only [Real.rpow_one] using h.symm
    exact (div_lt_iff₀ hmn).1 (by rw [hratio]; exact hs)
  have hNpow : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ m n ^ r := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hmono := Real.rpow_le_rpow (by positivity) (hmle n) hr.le
    have hrid : p.alpha * r = 2 := by
      dsimp [r]
      field_simp [ne_of_gt p.halpha.1]
    have hpowEq : ((n : ℝ) ^ p.alpha) ^ r = (n : ℝ) ^ 2 := by
      calc
        ((n : ℝ) ^ p.alpha) ^ r = (n : ℝ) ^ (p.alpha * r) :=
          (Real.rpow_mul hnpos.le p.alpha r).symm
        _ = (n : ℝ) ^ 2 := by simpa [hrid]
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc
      (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      _ = ((n : ℝ) ^ p.alpha) ^ r := hpowEq.symm
      _ ≤ m n ^ r := hmono
  have hscaled : Tendsto (fun n => b * m n) atTop atTop := hmTop.const_mul_atTop hb
  have hbase : Tendsto (fun n => (b * m n) ^ r * Real.exp (-(b * m n)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, neg_one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero r 1 one_pos).comp hscaled
  let C : ℝ := b ^ (-r)
  have hC : 0 < C := by dsimp [C]; positivity
  have hupper : Tendsto (fun n => C * ((b * m n) ^ r * Real.exp (-(b * m n))))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hbase
  have hscale (n : ℕ) (hnm : 0 < m n) : C * (b * m n) ^ r = m n ^ r := by
    dsimp [C]
    rw [Real.mul_rpow hb.le hnm.le, Real.rpow_neg hb.le]
    field_simp
  have hle : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.exp (m n ^ (15 / 100 : ℝ) - a * m n) ≤
        C * ((b * m n) ^ r * Real.exp (-(b * m n))) := by
    filter_upwards [hNpow, hmTop.eventually_gt_atTop 0, hDL] with n hn hnpos hdl
    have hExp : m n ^ (15 / 100 : ℝ) - a * m n ≤ -(b * m n) := by
      dsimp [a, b] at *
      nlinarith
    calc
      (n : ℝ) * Real.exp (m n ^ (15 / 100 : ℝ) - a * m n) ≤
          m n ^ r * Real.exp (-(b * m n)) := by
            apply mul_le_mul hn (Real.exp_le_exp.mpr hExp) (Real.exp_nonneg _) (by positivity)
      _ = C * ((b * m n) ^ r * Real.exp (-(b * m n))) := by
            rw [← hscale n hnpos]
            ring
  apply squeeze_zero' (Eventually.of_forall fun n =>
    mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)) hle
  simpa [a, m] using hupper

theorem entropy_fraction_exp_bound {m : ℕ} (hm : 0 < m) (t : ℝ)
    (hE : Real.binEntropy t ≤ Real.log 2 / 2) :
    Real.exp (Real.binEntropy t * m) / (2 : ℝ) ^ m ≤
      Real.exp (-(Real.log 2 / 2) * m) := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hpow : (2 : ℝ) ^ m = Real.exp (Real.log 2 * m) := by
    calc
      (2 : ℝ) ^ m = (Real.exp (Real.log 2)) ^ m := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp (Real.log 2 * m) := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hpow, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith [hE]

theorem halfPowerTail_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : Tendsto
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ) * Real.exp (-(Real.log 2) * (n : ℝ)))
      atTop (𝓝 0) := by
    exact (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (Real.log 2) hlog).comp
      tendsto_natCast_atTop_atTop
  have hexp : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have heq (n : ℕ) :
      (n : ℝ) * (1 / 2 : ℝ) ^ n =
        (n : ℝ) ^ (1 : ℝ) * Real.exp (-(Real.log 2) * (n : ℝ)) := by
    calc
      (n : ℝ) * (1 / 2 : ℝ) ^ n = (n : ℝ) * (Real.exp (-(Real.log 2))) ^ n := by rw [hexp]
      _ = (n : ℝ) * Real.exp ((-(Real.log 2)) * (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ = _ := by simp
  exact hbase.congr' (Eventually.of_forall (fun n => (heq n).symm))

theorem pi_expect_prod5 {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → FinProb α) (f : ι → α → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).expect (f i) := by
  classical
  rw [FinProb.expect]
  change (∑ ω : (ι → α), (∏ i, (P i).w (ω i)) * ∏ i, f i (ω i)) = _
  calc
    (∑ ω : (ι → α), (∏ i, (P i).w (ω i)) * ∏ i, f i (ω i)) =
        ∑ ω : (ι → α), ∏ i, ((P i).w (ω i) * f i (ω i)) := by
      apply Finset.sum_congr rfl
      intro ω hω
      exact (Finset.prod_mul_distrib).symm
    _ = ∏ i : ι, ∑ a : α, (P i).w a * f i a := by rw [Fintype.prod_sum]
    _ = ∏ i : ι, (P i).expect (f i) := by simp [FinProb.expect]

theorem bayes_posterior_mean5 {A O : Type*} [Fintype A] [DecidableEq A] [Fintype O]
    (P : FinProb A) (L : A → FinProb O) (a₀ fallback : A) :
    ∑ o : O, (∑ a : A, P.w a * (L a).w o) *
        (HypercubeRamsey.normalize5 (fun a => P.w a * (L a).w o) fallback).w a₀ = P.w a₀ := by
  classical
  let evidence : O → ℝ := fun o => ∑ a : A, P.w a * (L a).w o
  have hterm (o : O) (a : A) : 0 ≤ P.w a * (L a).w o :=
    mul_nonneg (P.nonneg a) ((L a).nonneg o)
  have hevidence (o : O) : 0 ≤ evidence o := by
    dsimp [evidence]
    exact Finset.sum_nonneg fun a _ => hterm o a
  have hmax (o : O) :
      (∑ a : A, max 0 (P.w a * (L a).w o)) = evidence o := by
    simp only [evidence]
    apply Finset.sum_congr rfl
    intro a ha
    exact max_eq_right (hterm o a)
  have hpoint (o : O) : evidence o *
      (HypercubeRamsey.normalize5 (fun a => P.w a * (L a).w o) fallback).w a₀ =
        P.w a₀ * (L a₀).w o := by
    by_cases he : 0 < evidence o
    · have hpost :
      (HypercubeRamsey.normalize5 (fun a => P.w a * (L a).w o) fallback).w a₀ =
            (P.w a₀ * (L a₀).w o) / evidence o := by
          simp [HypercubeRamsey.normalize5, hmax, evidence, he,
            max_eq_right (hterm o a₀)]
      rw [hpost]
      field_simp
    · have heq : evidence o = 0 := le_antisymm (le_of_not_gt he) (hevidence o)
      have hzero : P.w a₀ * (L a₀).w o = 0 := by
        dsimp [evidence] at heq
        have := Finset.single_le_sum (fun a ha => hterm o a)
          (Finset.mem_univ a₀)
        nlinarith [hterm o a₀]
      simp [heq, hzero]
  calc
    ∑ o : O, evidence o *
        (HypercubeRamsey.normalize5 (fun a => P.w a * (L a).w o) fallback).w a₀ =
      ∑ o : O, P.w a₀ * (L a₀).w o := by
        apply Finset.sum_congr rfl
        intro o ho
        exact hpoint o
    _ = P.w a₀ := by
      rw [← Finset.mul_sum, (L a₀).sum_eq_one]
      ring

theorem pi_expect_prod_restrict5
    {I V α : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Fintype α]
    (k : I → V) (hk : Function.Injective k) (Q : V → FinProb α) (f : I → α → ℝ) :
    (FinProb.pi (fun v : Finset.univ.image k => Q v.1)).expect
      (fun a => ∏ i, f i (a ⟨k i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)) =
        ∏ i, (Q (k i)).expect (f i) := by
  classical
  let S : Finset V := Finset.univ.image k
  let coord : I → S := fun i => ⟨k i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hbij : Function.Bijective coord := by
    constructor
    · intro i j hij
      apply hk
      exact congrArg Subtype.val hij
    · intro v
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp v.2
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact heq
  let e : I ≃ S := Equiv.ofBijective coord hbij
  let ePi : (∀ v : S, α) ≃ (I → α) :=
    (Equiv.piCongrLeft (fun _ : S => α) e).symm
  have hPiValue (b : I → α) (v : S) : ePi.symm b v = b (e.symm v) := by
    simp [ePi, Equiv.piCongrLeft_apply]
  have hweight (b : I → α) :
      ∏ v : S, (Q v.1).w (ePi.symm b v) = ∏ i, (Q (k i)).w (b i) := by
    calc
      ∏ v : S, (Q v.1).w (ePi.symm b v) =
          ∏ v : S, (Q v.1).w (b (e.symm v)) := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [hPiValue]
      _ = ∏ i, (Q (k i)).w (b i) := by
        symm
        exact Fintype.prod_equiv e (fun i => (Q (k i)).w (b i))
          (fun v => (Q v.1).w (b (e.symm v))) (by intro i; simp [e, coord])
  rw [FinProb.expect]
  rw [← Equiv.sum_comp ePi.symm
    (fun a => (FinProb.pi (fun v : S => Q v.1)).w a *
      ∏ i, f i (a (coord i)))]
  change (∑ b : I → α,
      (FinProb.pi (fun v : S => Q v.1)).w (ePi.symm b) *
        ∏ i, f i (ePi.symm b (coord i))) = _
  have hwpi (b : I → α) :
      (FinProb.pi (fun v : S => Q v.1)).w (ePi.symm b) =
        ∏ v : S, (Q v.1).w (ePi.symm b v) := rfl
  have hfpull (b : I → α) :
      (∏ i, f i (ePi.symm b (coord i))) = ∏ i, f i (b i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hPiValue]
    simp [coord, e]
  calc
    (∑ b : I → α,
        (FinProb.pi (fun v : S => Q v.1)).w (ePi.symm b) *
          ∏ i, f i (ePi.symm b (coord i))) =
        ∑ b : I → α, (∏ i, (Q (k i)).w (b i)) * ∏ i, f i (b i) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hwpi, hweight, hfpull]
    _ = (FinProb.pi (fun i : I => Q (k i))).expect (fun b => ∏ i, f i (b i)) := rfl
    _ = ∏ i, (Q (k i)).expect (f i) := pi_expect_prod5 (fun i => Q (k i)) f

theorem pi_expect_pinned5 {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α] (P : V → FinProb α) (Λ : Finset V)
    (x₀ : V → α) (F : (V → α) → ℝ) :
    (FinProb.pi (fun v => if v ∈ Λ then P v else pinDirac5 (x₀ v))).expect F =
      (FinProb.pi (fun v : {v : V // v ∈ Λ} => P v.1)).expect
        (fun a => F (fun v => if h : v ∈ Λ then a ⟨v, h⟩ else x₀ v)) := by
  classical
  let Q : V → FinProb α := fun v => if v ∈ Λ then P v else pinDirac5 (x₀ v)
  let F' : (V → α) → ℝ := fun ω => F (fun v => if h : v ∈ Λ then ω v else x₀ v)
  have hdep : FinProb.DependsOn F' Λ := by
    intro ω ω' hagree
    apply congrArg F
    funext v
    by_cases hv : v ∈ Λ
    · simp [hv, hagree v hv]
    · simp [hv]
  have hEq : (FinProb.pi Q).expect F = (FinProb.pi Q).expect F' := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hout : ∀ v, v ∉ Λ → ω v = x₀ v
    · have hfun : (fun v => if h : v ∈ Λ then ω v else x₀ v) = ω := by
        funext v
        by_cases hv : v ∈ Λ
        · simp [hv]
        · simp [hv, hout v hv]
      have hF : F' ω = F ω := by
        dsimp [F']
        exact congrArg F hfun
      simp [hF]
    · push_neg at hout
      obtain ⟨v, hv, hne⟩ := hout
      have hzero : (FinProb.pi Q).w ω = 0 := by
        simp only [FinProb.pi]
        apply Finset.prod_eq_zero (Finset.mem_univ v)
        simp [Q, hv, hne, pinDirac5]
      simp [hzero]
  rw [hEq]
  have h := FinProb.pi_expect_depends Q Λ F' x₀ hdep
  have hfun (a : ∀ v : {v : V // v ∈ Λ}, α) :
      F' ((Equiv.piEquivPiSubtypeProd (fun v => v ∈ Λ) (fun _ => α)).symm
        (a, fun v => x₀ v.1)) = F (fun v => if hv : v ∈ Λ then a ⟨v, hv⟩ else x₀ v) := by
    dsimp [F']
    apply congrArg F
    funext v
    let split := (Equiv.piEquivPiSubtypeProd (fun v => v ∈ Λ) (fun _ => α)).symm
      (a, fun v => x₀ v.1)
    change (if hv : v ∈ Λ then split v else x₀ v) =
      (if hv : v ∈ Λ then a ⟨v, hv⟩ else x₀ v)
    by_cases hv : v ∈ Λ
    · simp [split, hv, Equiv.piEquivPiSubtypeProd_symm_apply]
    · simp [split, hv, Equiv.piEquivPiSubtypeProd_symm_apply]
  have hFunctions :
      (fun a => F' ((Equiv.piEquivPiSubtypeProd (fun v => v ∈ Λ) (fun _ => α)).symm
        (a, fun v => x₀ v.1))) =
      (fun a => F (fun v => if hv : v ∈ Λ then a ⟨v, hv⟩ else x₀ v)) := by
    funext a
    exact hfun a
  rw [hFunctions] at h
  have hQ : (fun v : {v : V // v ∈ Λ} => Q v.1) = (fun v => P v.1) := by
    funext v
    simp [Q, v.2]
  rw [hQ] at h
  exact h

end HypercubeRamsey.Lane_q_s05_h5l
