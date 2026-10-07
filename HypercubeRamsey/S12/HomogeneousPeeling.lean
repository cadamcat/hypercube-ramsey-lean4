import HypercubeRamsey.S12.ModerateMoment
import HypercubeRamsey.S12.CenteredMoment
import HypercubeRamsey.S12.HomogeneousPeeling_q_s12_peel
import HypercubeRamsey.S12.FiniteRamsey_q_s12_peel

/-!
# Section 12 homogeneous extension counts and peeling
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter
open HypercubeRamsey.Lane_q_s12_peel
open Classical
open scoped BigOperators

/-- L12.5: the homogeneous support, clique exclusion, and peeling budget. -/
structure HomogeneousInput (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (k : ℕ) (c : Colour) (C0 : ℝ) where
  S : InterSetting T k (κ.xs / 4)
  π : Law (T.S.N k)
  homogeneous : ∀ l, S.π l = π
  Sp : Finset (Fin (T.S.N k))
  Sp_nonempty : Sp.Nonempty
  Sp_subset : Sp ⊆ T.X k
  τ_supported : S.τ.SupportedIn Sp
  π_supported : π.SupportedIn (T.Y k)
  degree_gate : ∀ x ∈ Sp, DegGate (T.S.E k) c π.w C0 (bstar T k) x
  degree_positive : ∀ x ∈ Sp, 0 < deg (T.S.E k) c π.w x
  Q : ℝ
  Q_large : Real.log
      (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ) ≤ Q ∧ 1 ≤ Q
  noClique : NoClique (T.S.E k) c Sp π.w κ.θ Q
  gamma : ℝ
  gamma_eq : gamma = Real.exp (Cstar κ.u κ.ξ * Q) *
    Sp.sup' Sp_nonempty (fun x => S.τ.w x *
      Real.rpow (deg (T.S.E k) c π.w x) (-(S.d : ℝ)))
  gamma_nonneg : 0 ≤ gamma
  gamma_lt_one : gamma < 1

/-- L12.5(iii): the peeling bound for every valid homogeneous setting at the stage. -/
def HomogeneousPeelingClaim (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (c : Colour) (C0 : ℝ) : Prop :=
  ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0,
      ∑ I : Finset (Fin κ.u),
        ∑ xs : Fin κ.u → Fin (T.S.N k),
          (if ¬ Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) κ.ξ xs
           then prodW H.S.τ.w xs *
             posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0) ≤
            4 ^ (κ.u + 1) * H.gamma

/-- L12.5(i): the number of exceptional one-label extensions is bounded by Ramsey. -/
theorem homogeneous_extension_count (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ H : HomogeneousInput κ hκ T k c C0,
        ∀ i₀ : Fin κ.u, ∀ xs : Fin κ.u → Fin (T.S.N k),
          (∀ i, i ≠ i₀ → xs i ∈ H.Sp) →
          ((H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
            i₀ ∈ J ∧ 2 ≤ J.card ∧
              κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)).card : ℝ) ≤
              Real.exp (Cstar κ.u κ.ξ * H.Q) := by
  classical
  have hn : Filter.Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hbstar : Filter.Tendsto (fun k => bstar T k) atTop (nhds 0) := by
    unfold bstar
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp hn using 1
    ext k
    congr 1
    norm_num
  have hC0pos : 0 < C0 := lt_of_lt_of_le (by norm_num) hC0
  have hGateEvent : ∀ᶠ k in atTop, C0 * bstar T k ≤ 1 / 6 := by
    have hsmall := hbstar.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / (6 * C0) by positivity))
    filter_upwards [hsmall] with k hk
    have hlt : C0 * bstar T k < 1 / 6 := calc
      C0 * bstar T k < C0 * (1 / (6 * C0)) := mul_lt_mul_of_pos_left hk hC0pos
      _ = 1 / 6 := by field_simp [ne_of_gt hC0pos]
    exact hlt.le
  have hErrEvent : ∀ᶠ k in atTop,
      (2 : ℝ) ^ (κ.u + 1) * C0 * bstar T k ≤ κ.ξ / 4 := by
    have hdenpos : 0 < 8 * (2 : ℝ) ^ κ.u * C0 := by positivity
    have hthreshold : 0 < κ.ξ / (8 * (2 : ℝ) ^ κ.u * C0) :=
      div_pos hκ.ξ_rng.1 hdenpos
    have hsmall := hbstar.eventually
      (Iio_mem_nhds hthreshold)
    filter_upwards [hsmall] with k hk
    have hlt : (2 : ℝ) ^ (κ.u + 1) * C0 * bstar T k < κ.ξ / 4 := calc
      (2 : ℝ) ^ (κ.u + 1) * C0 * bstar T k <
          (2 : ℝ) ^ (κ.u + 1) * C0 *
            (κ.ξ / (8 * (2 : ℝ) ^ κ.u * C0)) :=
        mul_lt_mul_of_pos_left hk (mul_pos (by positivity) hC0pos)
      _ = κ.ξ / 4 := by
        rw [show κ.u + 1 = κ.u + 1 by rfl, pow_succ]
        field_simp [ne_of_gt hC0pos, ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) κ.u)]
        ring
    exact hlt.le
  filter_upwards [hDeep, hGateEvent, hErrEvent] with k _ hkGate hkErr
  intro H i₀ xs hxs
  let F : ℝ := (4 : ℝ) ^ (κ.u + 3)
  let t₀ : ℕ := (⌊F / κ.ξ ^ 2⌋₊).succ
  let s : ℕ := ⌈Real.exp H.Q⌉₊
  let R (y z : Fin (T.S.N k)) : Prop :=
    y ≠ z ∧ 3 * κ.θ < corr (T.S.E k) c H.π.w y z
  let badFor (J : Finset (Fin κ.u)) : Finset (Fin (T.S.N k)) :=
    H.Sp.filter (fun z => i₀ ∈ J ∧ 2 ≤ J.card ∧
      κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)
  let C := H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
    i₀ ∈ J ∧ 2 ≤ J.card ∧
      κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)
  have hξ : 0 < κ.ξ := hκ.ξ_rng.1
  have hθ : 0 < κ.θ := hκ.θ_rng.1
  have hFpos : 0 < F := by positivity
  have hθsmall : 3 * κ.θ < κ.ξ ^ 2 / F := by
    calc
      3 * κ.θ < 3 * (κ.ξ ^ 2 / (3 * F)) :=
        mul_lt_mul_of_pos_left hκ.θ_rng.2 (by norm_num)
      _ = κ.ξ ^ 2 / F := by field_simp [ne_of_gt hFpos] <;> ring
  have t₀pos : 0 < t₀ := by dsimp [t₀]; omega
  have hfloor : F / κ.ξ ^ 2 < (t₀ : ℝ) := by
    dsimp [t₀, F]
    simpa [Nat.cast_succ] using
      (Nat.lt_floor_add_one ((4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2))
  have hspos : 1 ≤ s := by
    have hceil : 0 < s := by
      dsimp [s]
      exact Nat.ceil_pos.mpr (Real.exp_pos H.Q)
    omega
  have hExpTwo : (2 : ℝ) ≤ Real.exp H.Q := by
    have hExpOne : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h ⊢
      exact h
    exact le_trans hExpOne (Real.exp_le_exp.mpr H.Q_large.2)
  have hQlog : Real.log (t₀ : ℝ) ≤ H.Q := by
    simpa [t₀, F] using H.Q_large.1
  have ht₀exp : (t₀ : ℝ) ≤ Real.exp H.Q :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.mpr t₀pos)).mp hQlog
  have hsUpper : (s : ℝ) ≤ Real.exp H.Q + 1 := by
    dsimp [s]
    exact (Nat.ceil_lt_add_one (Real.exp_nonneg H.Q)).le
  have hnRam : (s + t₀ - 2 : ℕ) ≥ 1 := by
    have hsTwo : 2 ≤ s := by
      have hsReal : (2 : ℝ) ≤ (s : ℝ) := by
        calc
          (2 : ℝ) ≤ Real.exp H.Q := hExpTwo
          _ ≤ (s : ℝ) := by
            dsimp [s]
            exact_mod_cast Nat.le_ceil (Real.exp H.Q)
      exact_mod_cast hsReal
    omega
  have hnRamBound : ((s + t₀ - 2 : ℕ) : ℝ) ≤ Real.exp (2 * H.Q) := by
    have hnat : s + t₀ - 2 ≤ s + t₀ := by omega
    have hExpQFive : (5 / 2 : ℝ) ≤ Real.exp H.Q := by
      have hExpOneFive : (5 / 2 : ℝ) < Real.exp 1 :=
        lt_trans (by norm_num) Real.exp_one_gt_d9
      exact le_trans hExpOneFive.le (Real.exp_le_exp.mpr H.Q_large.2)
    calc
      ((s + t₀ - 2 : ℕ) : ℝ) ≤ (s + t₀ : ℕ) := by exact_mod_cast hnat
      _ = (s : ℝ) + (t₀ : ℝ) := by norm_cast
      _ ≤ Real.exp H.Q + 1 + Real.exp H.Q := add_le_add hsUpper ht₀exp
      _ ≤ Real.exp (2 * H.Q) := by
        rw [show 2 * H.Q = H.Q + H.Q by ring, Real.exp_add]
        nlinarith [sq_nonneg (Real.exp H.Q - (5 / 2 : ℝ))]
  have hlogt : Real.log (t₀ : ℝ) ≤ H.Q := by simpa [t₀, F] using H.Q_large.1
  have hCstarCoeff : 2 * (t₀ : ℝ) + (κ.u : ℝ) + 1 = Cstar κ.u κ.ξ := by
    dsimp [Cstar, t₀, F]
    push_cast
    ring
  have hExpPow : (Real.exp (2 * H.Q)) ^ t₀ =
      Real.exp ((t₀ : ℝ) * (2 * H.Q)) := by rw [← Real.exp_nat_mul]
  have hRamseyReal :
      (Nat.choose (s + t₀ - 2) (s - 1) : ℝ) ≤ Real.exp (2 * H.Q * t₀) := by
    have hsymm : Nat.choose (s + t₀ - 2) (s - 1) =
        Nat.choose (s + t₀ - 2) (t₀ - 1) := by
      have hidx : (s + t₀ - 2) - (s - 1) = t₀ - 1 := by omega
      have hs := Nat.choose_symm (n := s + t₀ - 2) (k := s - 1) (by omega)
      rw [hidx] at hs
      exact hs.symm
    have hchoose : (Nat.choose (s + t₀ - 2) (t₀ - 1) : ℝ) ≤
        ((s + t₀ - 2 : ℕ) : ℝ) ^ (t₀ - 1) := by
      exact_mod_cast Nat.choose_le_pow (s + t₀ - 2) (t₀ - 1)
    have hpow : ((s + t₀ - 2 : ℕ) : ℝ) ^ (t₀ - 1) ≤
        ((s + t₀ - 2 : ℕ) : ℝ) ^ t₀ := by
      have hbase : (1 : ℝ) ≤ ((s + t₀ - 2 : ℕ) : ℝ) := by exact_mod_cast hnRam
      exact pow_le_pow_right₀ hbase (Nat.sub_le t₀ 1)
    calc
      (Nat.choose (s + t₀ - 2) (s - 1) : ℝ) =
          (Nat.choose (s + t₀ - 2) (t₀ - 1) : ℝ) := by exact_mod_cast hsymm
      _ ≤ ((s + t₀ - 2 : ℕ) : ℝ) ^ (t₀ - 1) := hchoose
      _ ≤ ((s + t₀ - 2 : ℕ) : ℝ) ^ t₀ := hpow
      _ ≤ Real.exp (2 * H.Q) ^ t₀ :=
        pow_le_pow_left₀ (by positivity) hnRamBound _
      _ = Real.exp (2 * H.Q * t₀) := by
        rw [hExpPow]
        congr 1 <;> ring
  have hExpCoeff :
      (2 * (t₀ : ℝ) + (κ.u : ℝ) + 1) * H.Q = Cstar κ.u κ.ξ * H.Q := by
    rw [← hCstarCoeff]
  have hExpTwoPow : (2 : ℝ) ^ (κ.u + 1) ≤ Real.exp (((κ.u : ℝ) + 1) * H.Q) := by
    calc
      (2 : ℝ) ^ (κ.u + 1) ≤ (Real.exp H.Q) ^ (κ.u + 1) :=
        pow_le_pow_left₀ (by norm_num) hExpTwo _
      _ = Real.exp (((κ.u : ℝ) + 1) * H.Q) := by
        rw [← Real.exp_nat_mul]
        congr 1 <;> push_cast <;> ring
  have hFinalExponent : (2 * H.Q * t₀) + ((κ.u : ℝ) + 1) * H.Q =
      Cstar κ.u κ.ξ * H.Q := by
    rw [← hCstarCoeff]
    push_cast
    ring
  have hSignCard (J : Finset (Fin κ.u)) (hJ : i₀ ∈ J) (hJcard : 2 ≤ J.card)
      (D : Finset (Fin (T.S.N k))) (hD : D ⊆ H.Sp) (g : Fin (T.S.N k) → ℝ)
      (hgNorm : (∑ y, H.π.w y * g y ^ 2) ≤ (4 : ℝ) ^ κ.u)
      (σ : ℝ) (hσ : σ ^ 2 = 1)
      (hproject : ∀ z ∈ D, κ.ξ / 4 < σ *
        (∑ y, H.π.w y * fv (T.S.E k) c z y * g y)) :
      D.card < Nat.choose (s + t₀ - 2) (s - 1) := by
    have hNoClique : ¬ ∃ D' ⊆ D, RamseyClique R s D' := by
      rintro ⟨D', hD'sub, hclique⟩
      apply H.noClique
      refine ⟨D', hD'sub.trans hD, hclique.1, ?_⟩
      intro y hy z hz hne
      exact (hclique.2 y hy z hz hne).2
    have hNoIndependent : ¬ ∃ D' ⊆ D, RamseyIndependent R t₀ D' := by
      rintro ⟨D', hD'sub, hind⟩
      have hDsize : F / κ.ξ ^ 2 < (D'.card : ℝ) := by
        rw [hind.1]
        exact hfloor
      have hDproject : ∀ z ∈ D', κ.ξ / 4 <
          σ * (∑ y, H.π.w y * fv (T.S.E k) c z y * g y) := by
        intro z hz
        exact hproject z (hD'sub hz)
      have hDpair : ∀ z ∈ D', ∀ z' ∈ D', z ≠ z' →
          corr (T.S.E k) c H.π.w z z' ≤ 3 * κ.θ := by
        intro z hz z' hz' hne
        by_contra hlarge
        have hR : R z z' := ⟨hne, lt_of_not_ge hlarge⟩
        exact hind.2 z hz z' hz' hne hR
      exact corr_sign_independent_false (T.S.E k) c H.π g D' κ.u κ.ξ κ.θ σ
        hξ hθ.le hθsmall hDsize hσ hgNorm hDproject hDpair
    by_contra hlt
    have hge : Nat.choose (s + t₀ - 2) (s - 1) ≤ D.card := by omega
    rcases finite_ramsey_exists R (by
      intro y z hr
      refine ⟨hr.1.symm, ?_⟩
      rw [← show corr (T.S.E k) c H.π.w y z = corr (T.S.E k) c H.π.w z y by
        unfold corr
        apply Finset.sum_congr rfl
        intro w hw
        ring]
      exact hr.2) s t₀ hspos (Nat.one_le_iff_ne_zero.mpr t₀pos.ne') D hge with
      hClique | hIndependent
    · exact hNoClique hClique
    · exact hNoIndependent hIndependent
  have hbadFor (J : Finset (Fin κ.u)) :
      (badFor J).card ≤ 2 * Nat.choose (s + t₀ - 2) (s - 1) := by
    by_cases hJ : i₀ ∈ J
    · by_cases hJcard : 2 ≤ J.card
      · let g (y : Fin (T.S.N k)) :=
          ∏ j ∈ J.erase i₀, acoef (T.S.E k) c H.π.w (xs j) y
        have hdeglo (z : Fin (T.S.N k)) (hz : z ∈ H.Sp) :
            (1 / 3 : ℝ) ≤ deg (T.S.E k) c H.π.w z := by
          have hg := abs_le.mp (H.degree_gate z hz)
          linarith [hkGate]
        have hcoefBound (z : Fin (T.S.N k)) (hz : z ∈ H.Sp) (y : Fin (T.S.N k)) :
            |acoef (T.S.E k) c H.π.w z y| ≤ 2 := by
          have hhit : 0 ≤ hit (T.S.E k) c z y ∧ hit (T.S.E k) c z y ≤ 1 := by
            unfold hit
            split_ifs <;> norm_num
          have hden : 0 < deg (T.S.E k) c H.π.w z := H.degree_positive z hz
          have hratio0 : 0 ≤ hit (T.S.E k) c z y / deg (T.S.E k) c H.π.w z :=
            div_nonneg hhit.1 hden.le
          have hratio3 : hit (T.S.E k) c z y / deg (T.S.E k) c H.π.w z ≤ 3 :=
            (div_le_iff₀ hden).2 (by nlinarith [hhit.2, hdeglo z hz])
          unfold acoef
          rw [abs_le]
          constructor <;> linarith
        have hgbound (y : Fin (T.S.N k)) : |g y| ≤ (2 : ℝ) ^ κ.u := by
          dsimp [g]
          rw [Finset.abs_prod]
          calc
            (∏ j ∈ J.erase i₀, |acoef (T.S.E k) c H.π.w (xs j) y|) ≤
                ∏ j ∈ J.erase i₀, (2 : ℝ) := by
              apply Finset.prod_le_prod₀
              · intro j hj
                exact abs_nonneg _
              · intro j hj
                exact hcoefBound (xs j) (hxs j ((Finset.mem_erase.mp hj).1)) y
            _ = (2 : ℝ) ^ (J.erase i₀).card := by simp
            _ ≤ (2 : ℝ) ^ κ.u := by
              apply pow_le_pow_right₀ (by norm_num)
              have hc := Finset.card_le_card (Finset.erase_subset i₀ J)
              have hcJ : J.card ≤ κ.u := by simpa using Finset.card_le_univ J
              exact hc.trans hcJ
        have hpow : ∀ y, g y ^ 2 ≤ (4 : ℝ) ^ κ.u := by
          intro y
          have hpowEq : ((2 : ℝ) ^ κ.u) ^ 2 = (4 : ℝ) ^ κ.u := by
            rw [← pow_mul]
            rw [Nat.mul_comm κ.u 2]
            rw [pow_mul]
            norm_num
          have hsquare := (sq_le_sq₀ (abs_nonneg (g y)) (by positivity)).2 (hgbound y)
          simpa [sq_abs, hpowEq] using hsquare
        have hgNorm : (∑ y, H.π.w y * g y ^ 2) ≤ (4 : ℝ) ^ κ.u := by
          calc
            (∑ y, H.π.w y * g y ^ 2) ≤ ∑ y, H.π.w y * (4 : ℝ) ^ κ.u := by
              apply Finset.sum_le_sum
              intro y hy
              exact mul_le_mul_of_nonneg_left (hpow y) (H.π.nonneg y)
            _ = (4 : ℝ) ^ κ.u := by simp [← Finset.sum_mul, H.π.sum_eq_one]
        have hprodUpdate (z y : Fin (T.S.N k)) :
            (∏ j ∈ J, acoef (T.S.E k) c H.π.w ((Function.update xs i₀ z) j) y) =
              acoef (T.S.E k) c H.π.w z y * g y := by
          calc
            (∏ j ∈ J, acoef (T.S.E k) c H.π.w ((Function.update xs i₀ z) j) y) =
                (∏ j ∈ J.erase i₀,
                  acoef (T.S.E k) c H.π.w ((Function.update xs i₀ z) j) y) *
                    acoef (T.S.E k) c H.π.w ((Function.update xs i₀ z) i₀) y :=
              (Finset.prod_erase_mul J
                (fun j => acoef (T.S.E k) c H.π.w ((Function.update xs i₀ z) j) y) hJ).symm
            _ = g y * acoef (T.S.E k) c H.π.w z y := by
              congr 1
              · apply Finset.prod_congr rfl
                intro j hj
                simp [Function.update_apply, (Finset.mem_erase.mp hj).1]
              · simp
            _ = acoef (T.S.E k) c H.π.w z y * g y := by ring
        have hinter (z : Fin (T.S.N k)) :
            inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) =
              ∑ y, H.π.w y * acoef (T.S.E k) c H.π.w z y * g y := by
          unfold inter
          apply Finset.sum_congr rfl
          intro y hy
          rw [hprodUpdate]
          ring
        have hmean (z : Fin (T.S.N k)) :
            (∑ y, H.π.w y * fv (T.S.E k) c z y) =
              2 * deg (T.S.E k) c H.π.w z - 1 := by
          calc
            (∑ y, H.π.w y * fv (T.S.E k) c z y) =
                ∑ y, (2 * (H.π.w y * hit (T.S.E k) c z y) - H.π.w y) := by
              apply Finset.sum_congr rfl
              intro y hy
              unfold fv
              ring
            _ = (∑ y, 2 * (H.π.w y * hit (T.S.E k) c z y)) -
                ∑ y, H.π.w y := by rw [Finset.sum_sub_distrib]
            _ = 2 * (∑ y, H.π.w y * hit (T.S.E k) c z y) -
                ∑ y, H.π.w y := by rw [← Finset.mul_sum]
            _ = 2 * deg (T.S.E k) c H.π.w z - 1 := by simp [deg, H.π.sum_eq_one]
        have hmeanG : |(∑ y, H.π.w y * g y)| ≤ (2 : ℝ) ^ κ.u := by
          calc
            |∑ y, H.π.w y * g y| ≤
                ∑ y, |H.π.w y * g y| :=
              Finset.abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun y => H.π.w y * g y)
            _ = ∑ y, H.π.w y * |g y| := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [abs_mul, abs_of_nonneg (H.π.nonneg y)]
            _ ≤ ∑ y, H.π.w y * (2 : ℝ) ^ κ.u := by
              apply Finset.sum_le_sum
              intro y hy
              exact mul_le_mul_of_nonneg_left (hgbound y) (H.π.nonneg y)
            _ = (2 : ℝ) ^ κ.u := by simp [← Finset.sum_mul, H.π.sum_eq_one]
        have hprojectionIdentity (z : Fin (T.S.N k)) (hzSp : z ∈ H.Sp) :
            (∑ y, H.π.w y * fv (T.S.E k) c z y * g y) =
              (∑ y, H.π.w y * fv (T.S.E k) c z y) *
                  (∑ y, H.π.w y * g y) +
                (1 + (∑ y, H.π.w y * fv (T.S.E k) c z y)) *
                  inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
          let mz : ℝ := ∑ y, H.π.w y * fv (T.S.E k) c z y
          let mg : ℝ := ∑ y, H.π.w y * g y
          have hfvAcoef : ∀ y,
              fv (T.S.E k) c z y =
                mz + (1 + mz) *
                    acoef (T.S.E k) c H.π.w z y := by
            intro y
            dsimp [mz]
            rw [hmean z]
            unfold fv acoef
            field_simp [ne_of_gt (H.degree_positive z hzSp)]
            ring
          have hlin : (∑ y, H.π.w y * fv (T.S.E k) c z y * g y) =
              (∑ y, H.π.w y * (mz * g y)) +
                (∑ y, H.π.w y * ((1 + mz) * acoef (T.S.E k) c H.π.w z y * g y)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro y hy
            rw [hfvAcoef y]
            ring
          have hfirst : (∑ y, H.π.w y * (mz * g y)) = mz * mg := by
            calc
              (∑ y, H.π.w y * (mz * g y)) = ∑ y, mz * (H.π.w y * g y) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
              _ = mz * mg := by rw [← Finset.mul_sum]
          have hsecond :
              (∑ y, H.π.w y * ((1 + mz) * acoef (T.S.E k) c H.π.w z y * g y)) =
                (1 + mz) * inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
            calc
              (∑ y, H.π.w y * ((1 + mz) * acoef (T.S.E k) c H.π.w z y * g y)) =
                  ∑ y, (1 + mz) * (H.π.w y * acoef (T.S.E k) c H.π.w z y * g y) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
              _ = (1 + mz) * (∑ y, H.π.w y * acoef (T.S.E k) c H.π.w z y * g y) := by
                rw [← Finset.mul_sum]
              _ = (1 + mz) * inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
                rw [← hinter z]
          calc
            (∑ y, H.π.w y * fv (T.S.E k) c z y * g y) =
                (∑ y, H.π.w y * (mz * g y)) +
                  (∑ y, H.π.w y * ((1 + mz) * acoef (T.S.E k) c H.π.w z y * g y)) := hlin
            _ = mz * mg + (1 + mz) * inter (T.S.E k) c H.π.w J
                (Function.update xs i₀ z) := by rw [hfirst, hsecond]
            _ = (∑ y, H.π.w y * fv (T.S.E k) c z y) *
                  (∑ y, H.π.w y * g y) +
                (1 + (∑ y, H.π.w y * fv (T.S.E k) c z y)) *
                  inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
              dsimp [mz, mg]
        let Dpos := H.Sp.filter (fun z => κ.ξ < inter (T.S.E k) c H.π.w J
          (Function.update xs i₀ z))
        let Dneg := H.Sp.filter (fun z => κ.ξ < -inter (T.S.E k) c H.π.w J
          (Function.update xs i₀ z))
        have hDposProj : ∀ z ∈ Dpos, κ.ξ / 4 <
            (∑ y, H.π.w y * fv (T.S.E k) c z y * g y) := by
          intro z hz
          have hzSp := (Finset.mem_filter.mp hz).1
          have hI := (Finset.mem_filter.mp hz).2
          have hgate := H.degree_gate z hzSp
          have hdeglo := hdeglo z hzSp
          have hmeanBound : |∑ y, H.π.w y * fv (T.S.E k) c z y| ≤
              2 * C0 * bstar T k := by
            rw [hmean z]
            have hrewrite : 2 * deg (T.S.E k) c H.π.w z - 1 =
                2 * (deg (T.S.E k) c H.π.w z - 1 / 2) := by ring
            rw [hrewrite, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            calc
              2 * |deg (T.S.E k) c H.π.w z - 1 / 2| ≤ 2 * (C0 * bstar T k) :=
                mul_le_mul_of_nonneg_left hgate (by norm_num : (0 : ℝ) ≤ 2)
              _ = 2 * C0 * bstar T k := by ring
          have hCbNonneg : 0 ≤ 2 * C0 * bstar T k :=
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0pos.le)
              (by unfold bstar; exact Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) _)
          have herror : |(∑ y, H.π.w y * fv (T.S.E k) c z y) *
              (∑ y, H.π.w y * g y)| ≤ κ.ξ / 4 := by
            rw [abs_mul]
            calc
              |∑ y, H.π.w y * fv (T.S.E k) c z y| *
                  |∑ y, H.π.w y * g y| ≤
                  (2 * C0 * bstar T k) * (2 : ℝ) ^ κ.u :=
                    calc
                      _ ≤ (2 * C0 * bstar T k) * |∑ y, H.π.w y * g y| :=
                        mul_le_mul_of_nonneg_right hmeanBound (abs_nonneg _)
                      _ ≤ (2 * C0 * bstar T k) * (2 : ℝ) ^ κ.u :=
                        mul_le_mul_of_nonneg_left hmeanG hCbNonneg
              _ = (2 : ℝ) ^ (κ.u + 1) * C0 * bstar T k := by rw [pow_succ]; ring
              _ ≤ κ.ξ / 4 := hkErr
          have h2deg : (1 / 2 : ℝ) ≤ 2 * deg (T.S.E k) c H.π.w z := by
            have hlow : -(C0 * bstar T k) ≤
                deg (T.S.E k) c H.π.w z - 1 / 2 := (abs_le.mp hgate).1
            have hdegLower : (1 / 3 : ℝ) ≤ deg (T.S.E k) c H.π.w z := by
              linarith [hkGate, hlow]
            linarith
          have hmain : κ.ξ / 2 <
              2 * deg (T.S.E k) c H.π.w z *
                inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
            calc
              κ.ξ / 2 ≤ 2 * deg (T.S.E k) c H.π.w z * κ.ξ := by nlinarith [h2deg, hξ]
              _ < 2 * deg (T.S.E k) c H.π.w z *
                inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) :=
                mul_lt_mul_of_pos_left hI
                  (mul_pos (by norm_num) (H.degree_positive z hzSp))
          have hiden := hprojectionIdentity z hzSp
          rw [hmean z] at herror
          have herrlo := (abs_le.mp herror).1
          rw [hmean z] at hiden
          have hcoef : 1 + (2 * deg (T.S.E k) c H.π.w z - 1) =
              2 * deg (T.S.E k) c H.π.w z := by ring
          have hprojEq : (∑ y, H.π.w y * fv (T.S.E k) c z y * g y) =
              (2 * deg (T.S.E k) c H.π.w z - 1) *
                  (∑ y, H.π.w y * g y) +
                2 * deg (T.S.E k) c H.π.w z *
                  inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
            simpa [hcoef] using hiden
          linarith [hprojEq, hmain]
        have hDnegProj : ∀ z ∈ Dneg, κ.ξ / 4 < -
            (∑ y, H.π.w y * fv (T.S.E k) c z y * g y) := by
          intro z hz
          have hzSp := (Finset.mem_filter.mp hz).1
          have hI := (Finset.mem_filter.mp hz).2
          have hgate := H.degree_gate z hzSp
          have hmeanBound : |∑ y, H.π.w y * fv (T.S.E k) c z y| ≤
              2 * C0 * bstar T k := by
            rw [hmean z]
            have hrewrite : 2 * deg (T.S.E k) c H.π.w z - 1 =
                2 * (deg (T.S.E k) c H.π.w z - 1 / 2) := by ring
            rw [hrewrite, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            calc
              2 * |deg (T.S.E k) c H.π.w z - 1 / 2| ≤ 2 * (C0 * bstar T k) :=
                mul_le_mul_of_nonneg_left hgate (by norm_num : (0 : ℝ) ≤ 2)
              _ = 2 * C0 * bstar T k := by ring
          have hCbNonneg : 0 ≤ 2 * C0 * bstar T k :=
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0pos.le)
              (by unfold bstar; exact Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) _)
          have herror : |(∑ y, H.π.w y * fv (T.S.E k) c z y) *
              (∑ y, H.π.w y * g y)| ≤ κ.ξ / 4 := by
            rw [abs_mul]
            calc
              |∑ y, H.π.w y * fv (T.S.E k) c z y| *
                  |∑ y, H.π.w y * g y| ≤
                  (2 * C0 * bstar T k) * (2 : ℝ) ^ κ.u :=
                    calc
                      _ ≤ (2 * C0 * bstar T k) * |∑ y, H.π.w y * g y| :=
                        mul_le_mul_of_nonneg_right hmeanBound (abs_nonneg _)
                      _ ≤ (2 * C0 * bstar T k) * (2 : ℝ) ^ κ.u :=
                        mul_le_mul_of_nonneg_left hmeanG hCbNonneg
              _ = (2 : ℝ) ^ (κ.u + 1) * C0 * bstar T k := by rw [pow_succ]; ring
              _ ≤ κ.ξ / 4 := hkErr
          have h2deg : (1 / 2 : ℝ) ≤ 2 * deg (T.S.E k) c H.π.w z := by
            have hlow : -(C0 * bstar T k) ≤
                deg (T.S.E k) c H.π.w z - 1 / 2 := (abs_le.mp hgate).1
            have hdegLower : (1 / 3 : ℝ) ≤ deg (T.S.E k) c H.π.w z := by
              linarith [hkGate, hlow]
            linarith
          have hmain : κ.ξ / 2 <
              2 * deg (T.S.E k) c H.π.w z *
                -inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
            calc
              κ.ξ / 2 ≤ 2 * deg (T.S.E k) c H.π.w z * κ.ξ := by nlinarith [h2deg, hξ]
              _ < 2 * deg (T.S.E k) c H.π.w z *
                -inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) :=
                mul_lt_mul_of_pos_left hI
                  (mul_pos (by norm_num) (H.degree_positive z hzSp))
          have hiden := hprojectionIdentity z hzSp
          rw [hmean z] at herror
          have herrhi := (abs_le.mp herror).2
          rw [hmean z] at hiden
          have hcoef : 1 + (2 * deg (T.S.E k) c H.π.w z - 1) =
              2 * deg (T.S.E k) c H.π.w z := by ring
          have hprojEq : (∑ y, H.π.w y * fv (T.S.E k) c z y * g y) =
              (2 * deg (T.S.E k) c H.π.w z - 1) *
                  (∑ y, H.π.w y * g y) +
                2 * deg (T.S.E k) c H.π.w z *
                  inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
            simpa [hcoef] using hiden
          have hnegEq : -(∑ y, H.π.w y * fv (T.S.E k) c z y * g y) =
              -((2 * deg (T.S.E k) c H.π.w z - 1) *
                  (∑ y, H.π.w y * g y)) +
                2 * deg (T.S.E k) c H.π.w z *
                  -inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
            rw [hprojEq]
            ring
          linarith [hnegEq, hmain]
        have hDposCard := hSignCard J hJ hJcard Dpos (Finset.filter_subset _ _) g hgNorm
          1 (by norm_num) (by intro z hz; simpa using hDposProj z hz)
        have hDnegCard := hSignCard J hJ hJcard Dneg (Finset.filter_subset _ _) g hgNorm
          (-1) (by norm_num) (by intro z hz; simpa using hDnegProj z hz)
        have hcover :
            (H.Sp.filter (fun z => κ.ξ < |inter (T.S.E k) c H.π.w J
              (Function.update xs i₀ z)|)) ⊆ Dpos ∪ Dneg := by
          intro z hz
          have hzSp := (Finset.mem_filter.mp hz).1
          have hAbs := (Finset.mem_filter.mp hz).2
          by_cases hnonneg : 0 ≤ inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)
          · have hI : κ.ξ < inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
              simpa [abs_of_nonneg hnonneg] using hAbs
            exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hzSp, hI⟩))
          · have hneg : inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) < 0 := lt_of_not_ge hnonneg
            have hI : κ.ξ < -inter (T.S.E k) c H.π.w J (Function.update xs i₀ z) := by
              simpa [abs_of_neg hneg] using hAbs
            exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hzSp, hI⟩))
        have hDcard :
            (H.Sp.filter (fun z => κ.ξ < |inter (T.S.E k) c H.π.w J
              (Function.update xs i₀ z)|)).card ≤
                2 * Nat.choose (s + t₀ - 2) (s - 1) := by
          calc
            _ ≤ (Dpos ∪ Dneg).card := Finset.card_le_card hcover
            _ ≤ Dpos.card + Dneg.card := Finset.card_union_le _ _
            _ ≤ Nat.choose (s + t₀ - 2) (s - 1) +
                Nat.choose (s + t₀ - 2) (s - 1) := Nat.add_le_add hDposCard.le hDnegCard.le
            _ = _ := by omega
        simpa [badFor, hJ, hJcard] using hDcard
      · simp [badFor, hJ, hJcard]
    · simp [badFor, hJ]
  have hcover : C ⊆ (Finset.univ : Finset (Finset (Fin κ.u))).biUnion badFor := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzSp, ⟨J, hJ, hJcard, hI⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨J, Finset.mem_univ J, ?_⟩
    exact Finset.mem_filter.mpr ⟨hzSp, ⟨hJ, hJcard, hI⟩⟩
  have hcardNat : C.card ≤ 2 ^ κ.u *
      (2 * Nat.choose (s + t₀ - 2) (s - 1)) := by
    calc
      C.card ≤ ((Finset.univ : Finset (Finset (Fin κ.u))).biUnion badFor).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ J ∈ (Finset.univ : Finset (Finset (Fin κ.u))), (badFor J).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ J ∈ (Finset.univ : Finset (Finset (Fin κ.u))),
          2 * Nat.choose (s + t₀ - 2) (s - 1) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact hbadFor J
      _ = 2 ^ κ.u * (2 * Nat.choose (s + t₀ - 2) (s - 1)) := by
        simp [Finset.sum_const, Fintype.card_finset]
  have hCexp : (C.card : ℝ) ≤ Real.exp (Cstar κ.u κ.ξ * H.Q) := by
    have hcardReal : (C.card : ℝ) ≤ (2 : ℝ) ^ (κ.u + 1) *
        (Nat.choose (s + t₀ - 2) (s - 1) : ℝ) := by
      calc
        (C.card : ℝ) ≤ ((2 ^ κ.u * (2 * Nat.choose (s + t₀ - 2) (s - 1)) : ℕ) : ℝ) :=
          by exact_mod_cast hcardNat
        _ = (2 : ℝ) ^ (κ.u + 1) * (Nat.choose (s + t₀ - 2) (s - 1) : ℝ) := by
          norm_cast
          rw [pow_succ]
          ring
    calc
      (C.card : ℝ) ≤ (2 : ℝ) ^ (κ.u + 1) *
          (Nat.choose (s + t₀ - 2) (s - 1) : ℝ) := hcardReal
      _ ≤ Real.exp (((κ.u : ℝ) + 1) * H.Q) * Real.exp (2 * H.Q * t₀) :=
        mul_le_mul hExpTwoPow hRamseyReal (by positivity) (by positivity)
      _ = Real.exp (Cstar κ.u κ.ξ * H.Q) := by
        rw [← Real.exp_add]
        congr 1
        calc
          ((κ.u : ℝ) + 1) * H.Q + 2 * H.Q * t₀ =
              2 * H.Q * t₀ + ((κ.u : ℝ) + 1) * H.Q := by ring
          _ = Cstar κ.u κ.ξ * H.Q := hFinalExponent
  exact hCexp

/-- L12.5(ii): every label has few large-correlation partners in the support. -/
theorem homogeneous_conflict_count (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ H : HomogeneousInput κ hκ T k c C0, ∀ x : Fin (T.S.N k),
        ((H.Sp.filter (fun z =>
          κ.ξ < |corr (T.S.E k) c H.π.w x z|)).card : ℝ) ≤
            Real.exp (Cstar κ.u κ.ξ * H.Q) := by
  classical
  filter_upwards [hDeep] with k hkDeep
  intro H x
  let F : ℝ := (4 : ℝ) ^ (κ.u + 3)
  let t₀ : ℕ := (⌊F / κ.ξ ^ 2⌋₊).succ
  let s : ℕ := ⌈Real.exp H.Q⌉₊
  let R (y z : Fin (T.S.N k)) : Prop :=
    y ≠ z ∧ 3 * κ.θ < corr (T.S.E k) c H.π.w y z
  let C := H.Sp.filter (fun z => κ.ξ < |corr (T.S.E k) c H.π.w x z|)
  let Cpos := H.Sp.filter (fun z => κ.ξ < corr (T.S.E k) c H.π.w x z)
  let Cneg := H.Sp.filter (fun z => κ.ξ < -corr (T.S.E k) c H.π.w x z)
  have hξ : 0 < κ.ξ := hκ.ξ_rng.1
  have hθ : 0 < κ.θ := hκ.θ_rng.1
  have hFpos : 0 < F := by positivity
  have hθsmall : 3 * κ.θ < κ.ξ ^ 2 / F := by
    calc
      3 * κ.θ < 3 * (κ.ξ ^ 2 / (3 * F)) :=
        mul_lt_mul_of_pos_left hκ.θ_rng.2 (by norm_num)
      _ = κ.ξ ^ 2 / F := by field_simp [ne_of_gt hFpos] <;> ring
  have t₀pos : 0 < t₀ := by dsimp [t₀]; omega
  have hfloor : F / κ.ξ ^ 2 < (t₀ : ℝ) := by
    dsimp [t₀, F]
    simpa [Nat.cast_succ] using
      (Nat.lt_floor_add_one ((4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2))
  have hQlog : Real.log (t₀ : ℝ) ≤ H.Q := by
    simpa [t₀, F] using H.Q_large.1
  have hQpos : 1 ≤ H.Q := H.Q_large.2
  have hspos : 1 ≤ s := by
    have hceil : 0 < s := by
      dsimp [s]
      exact Nat.ceil_pos.mpr (Real.exp_pos H.Q)
    omega
  have hcorrSymm : ∀ y z, corr (T.S.E k) c H.π.w y z =
      corr (T.S.E k) c H.π.w z y := by
    intro y z
    unfold corr
    apply Finset.sum_congr rfl
    intro w hw
    ring
  have hRSymm : ∀ y z, R y z → R z y := by
    intro y z hr
    refine ⟨hr.1.symm, ?_⟩
    rw [← hcorrSymm y z]
    exact hr.2
  have hSignCard (D : Finset (Fin (T.S.N k))) (hD : D ⊆ H.Sp)
      (σ : ℝ) (hσ : σ ^ 2 = 1)
      (hproject : ∀ z ∈ D, κ.ξ < σ * corr (T.S.E k) c H.π.w x z) :
      D.card < Nat.choose (s + t₀ - 2) (s - 1) := by
    have hNoClique : ¬ ∃ D' ⊆ D, RamseyClique R s D' := by
      rintro ⟨D', hD'sub, hclique⟩
      apply H.noClique
      refine ⟨D', hD'sub.trans hD, hclique.1, ?_⟩
      intro y hy z hz hne
      exact (hclique.2 y hy z hz hne).2
    have hNoIndependent : ¬ ∃ D' ⊆ D, RamseyIndependent R t₀ D' := by
      rintro ⟨D', hD'sub, hind⟩
      have hDsize : F / κ.ξ ^ 2 < (D'.card : ℝ) := by
        rw [hind.1]
        exact hfloor
      have hDproject : ∀ z ∈ D', κ.ξ < σ * corr (T.S.E k) c H.π.w x z := by
        intro z hz
        exact hproject z (hD'sub hz)
      have hfvSq : ∀ y, (fv (T.S.E k) c x y) ^ 2 = 1 := by
        intro y
        unfold fv hit
        split_ifs <;> norm_num
      have hdirNorm : (∑ y, H.π.w y * (fv (T.S.E k) c x y) ^ 2) = 1 := by
        calc
          (∑ y, H.π.w y * (fv (T.S.E k) c x y) ^ 2) =
              ∑ y, H.π.w y := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [hfvSq]
            ring
          _ = 1 := H.π.sum_eq_one
      have hdirNormBound : (∑ y, H.π.w y * (fv (T.S.E k) c x y) ^ 2) ≤
          (4 : ℝ) ^ κ.u := by
        rw [hdirNorm]
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
      have hDproject' : ∀ z ∈ D', κ.ξ / 4 < σ *
          (∑ y, H.π.w y * fv (T.S.E k) c z y * fv (T.S.E k) c x y) := by
        intro z hz
        calc
          κ.ξ / 4 < κ.ξ := by linarith
          _ < σ * corr (T.S.E k) c H.π.w x z := hDproject z hz
          _ = σ * (∑ y, H.π.w y * fv (T.S.E k) c z y * fv (T.S.E k) c x y) := by
            rw [hcorrSymm x z]
            rfl
      have hDpair : ∀ z ∈ D', ∀ z' ∈ D', z ≠ z' →
          corr (T.S.E k) c H.π.w z z' ≤ 3 * κ.θ := by
        intro z hz z' hz' hne
        by_contra hlarge
        have hR : R z z' := ⟨hne, lt_of_not_ge hlarge⟩
        exact hind.2 z hz z' hz' hne hR
      exact corr_sign_independent_false (T.S.E k) c H.π
        (fun y => fv (T.S.E k) c x y) D' κ.u κ.ξ κ.θ σ
        hξ hθ.le hθsmall hDsize hσ hdirNormBound hDproject' hDpair
    by_contra hlt
    have hge : Nat.choose (s + t₀ - 2) (s - 1) ≤ D.card := by omega
    rcases finite_ramsey_exists R hRSymm s t₀ hspos (Nat.one_le_iff_ne_zero.mpr t₀pos.ne') D hge with
      hClique | hIndependent
    · exact hNoClique hClique
    · exact hNoIndependent hIndependent
  have hCposCard := hSignCard Cpos (Finset.filter_subset _ _) 1 (by norm_num)
    (by intro z hz; simpa using (Finset.mem_filter.mp hz).2)
  have hCnegCard := hSignCard Cneg (Finset.filter_subset _ _) (-1) (by norm_num)
    (by intro z hz; simpa using (Finset.mem_filter.mp hz).2)
  have hCover : C ⊆ Cpos ∪ Cneg := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzSp, habs⟩
    by_cases hnonneg : 0 ≤ corr (T.S.E k) c H.π.w x z
    · have hcorrAbs := abs_of_nonneg hnonneg
      have hpos : κ.ξ < corr (T.S.E k) c H.π.w x z := by simpa [hcorrAbs] using habs
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hzSp, hpos⟩))
    · have hneg : corr (T.S.E k) c H.π.w x z < 0 := lt_of_not_ge hnonneg
      have hcorrAbs := abs_of_neg hneg
      have hpos : κ.ξ < -corr (T.S.E k) c H.π.w x z := by simpa [hcorrAbs] using habs
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hzSp, hpos⟩))
  have hcard : C.card ≤ 2 * Nat.choose (s + t₀ - 2) (s - 1) := by
    calc
      C.card ≤ (Cpos ∪ Cneg).card := Finset.card_le_card hCover
      _ ≤ Cpos.card + Cneg.card := Finset.card_union_le _ _
      _ ≤ Nat.choose (s + t₀ - 2) (s - 1) +
          Nat.choose (s + t₀ - 2) (s - 1) := Nat.add_le_add hCposCard.le hCnegCard.le
      _ = _ := by omega
  let nRam := s + t₀ - 2
  have hlogt : Real.log (t₀ : ℝ) ≤ H.Q := by simpa [t₀] using H.Q_large.1
  have ht₀exp : (t₀ : ℝ) ≤ Real.exp H.Q :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.mpr t₀pos)).mp hlogt
  have hExpTwo : (2 : ℝ) ≤ Real.exp H.Q := by
    have hExpOne : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h ⊢
      exact h
    exact le_trans hExpOne (Real.exp_le_exp.mpr H.Q_large.2)
  have hsUpper : (s : ℝ) ≤ Real.exp H.Q + 1 := by
    dsimp [s]
    exact (Nat.ceil_lt_add_one (Real.exp_nonneg H.Q)).le
  have hnRamPos : 1 ≤ nRam := by
    dsimp [nRam]
    have hsTwo : 2 ≤ s := by
      have hsReal : (2 : ℝ) ≤ (s : ℝ) := by
        calc
          (2 : ℝ) ≤ Real.exp H.Q := hExpTwo
          _ ≤ (s : ℝ) := by
            dsimp [s]
            exact_mod_cast Nat.le_ceil (Real.exp H.Q)
      exact_mod_cast hsReal
    omega
  have hnRamBound : (nRam : ℝ) ≤ Real.exp (2 * H.Q) := by
    have hnat : nRam ≤ s + t₀ := by dsimp [nRam]; omega
    calc
      (nRam : ℝ) ≤ (s + t₀ : ℕ) := by exact_mod_cast hnat
      _ = (s : ℝ) + (t₀ : ℝ) := by norm_cast
      _ ≤ Real.exp H.Q + 1 + Real.exp H.Q := add_le_add hsUpper ht₀exp
      _ ≤ Real.exp (2 * H.Q) := by
        have hExpQFive : (5 / 2 : ℝ) ≤ Real.exp H.Q := by
          have hExpOneFive : (5 / 2 : ℝ) < Real.exp 1 := by
            exact lt_trans (by norm_num) Real.exp_one_gt_d9
          exact le_trans hExpOneFive.le (Real.exp_le_exp.mpr H.Q_large.2)
        rw [show 2 * H.Q = H.Q + H.Q by ring, Real.exp_add]
        nlinarith [sq_nonneg (Real.exp H.Q - (5 / 2 : ℝ))]
  have hchooseSymm : Nat.choose nRam (s - 1) = Nat.choose nRam (t₀ - 1) := by
    have hidx : nRam - (s - 1) = t₀ - 1 := by dsimp [nRam]; omega
    have hsymm := Nat.choose_symm (n := nRam) (k := s - 1) (by dsimp [nRam]; omega)
    rw [hidx] at hsymm
    exact hsymm.symm
  have hchoosePow : (Nat.choose nRam (t₀ - 1) : ℝ) ≤
      (nRam : ℝ) ^ (t₀ - 1) := by
    exact_mod_cast Nat.choose_le_pow nRam (t₀ - 1)
  have hnRamPow : (nRam : ℝ) ^ (t₀ - 1) ≤ (nRam : ℝ) ^ t₀ := by
    have hnbase : (1 : ℝ) ≤ (nRam : ℝ) := by exact_mod_cast hnRamPos
    exact pow_le_pow_right₀ hnbase (Nat.sub_le t₀ 1)
  have hnRamPowBound : (nRam : ℝ) ^ t₀ ≤ Real.exp (2 * H.Q) ^ t₀ :=
    pow_le_pow_left₀ (by positivity) hnRamBound _
  have hExpPow : (Real.exp (2 * H.Q)) ^ t₀ =
      Real.exp ((t₀ : ℝ) * (2 * H.Q)) := by rw [← Real.exp_nat_mul]
  have hCstarCoeff : 2 * (t₀ : ℝ) + 1 ≤ Cstar κ.u κ.ξ := by
    have hu : (0 : ℝ) ≤ (κ.u : ℝ) := Nat.cast_nonneg κ.u
    dsimp [Cstar, t₀, F]
    push_cast
    nlinarith [hu]
  have hExpExponent : H.Q + (t₀ : ℝ) * (2 * H.Q) ≤ Cstar κ.u κ.ξ * H.Q := by
    have hmul := mul_le_mul_of_nonneg_right hCstarCoeff (by linarith [H.Q_large.2])
    nlinarith [hmul]
  have hRamseyReal :
      (Nat.choose nRam (s - 1) : ℝ) ≤ Real.exp (2 * H.Q * t₀) := by
    calc
      (Nat.choose nRam (s - 1) : ℝ) = (Nat.choose nRam (t₀ - 1) : ℝ) := by
        exact_mod_cast hchooseSymm
      _ ≤ (nRam : ℝ) ^ (t₀ - 1) := hchoosePow
      _ ≤ (nRam : ℝ) ^ t₀ := hnRamPow
      _ ≤ Real.exp (2 * H.Q) ^ t₀ := hnRamPowBound
      _ = Real.exp (2 * H.Q * t₀) := by
        rw [hExpPow]
        congr 1 <;> ring
  have hbadExp : (C.card : ℝ) ≤ Real.exp (Cstar κ.u κ.ξ * H.Q) := by
    have hcardReal : (C.card : ℝ) ≤ 2 * (Nat.choose nRam (s - 1) : ℝ) := by
      exact_mod_cast hcard
    calc
      (C.card : ℝ) ≤ 2 * (Nat.choose nRam (s - 1) : ℝ) := hcardReal
      _ ≤ 2 * Real.exp (2 * H.Q * t₀) :=
        mul_le_mul_of_nonneg_left hRamseyReal (by norm_num)
      _ ≤ Real.exp H.Q * Real.exp (2 * H.Q * t₀) :=
        mul_le_mul_of_nonneg_right hExpTwo (Real.exp_nonneg _)
      _ = Real.exp (H.Q + 2 * H.Q * t₀) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp (Cstar κ.u κ.ξ * H.Q) :=
        Real.exp_le_exp.mpr (by nlinarith [hExpExponent])
  exact hbadExp

private theorem maximal_moderate_extension_cover (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (k : ℕ) (c : Colour) (C0 : ℝ)
    (H : HomogeneousInput κ hκ T k c C0)
    (hExtension : ∀ i₀ : Fin κ.u,
      ∀ xs : Fin κ.u → Fin (T.S.N k),
        (∀ i, i ≠ i₀ → xs i ∈ H.Sp) →
        ((H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
          i₀ ∈ J ∧ 2 ≤ J.card ∧
            κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)).card : ℝ) ≤
          Real.exp (Cstar κ.u κ.ξ * H.Q)) :
    ∀ xs : Fin κ.u → Fin (T.S.N k),
      (∀ i, xs i ∈ H.Sp) →
      ¬ Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) κ.ξ xs →
      ∃ K : Finset (Fin κ.u),
        ModerateOn (T.S.E k) c H.π.w κ.ξ xs K ∧ K ≠ Finset.univ ∧
          ∀ i, i ∉ K →
            ((H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
              i ∈ J ∧ 2 ≤ J.card ∧ κ.ξ < |inter (T.S.E k) c H.π.w J
                (Function.update (fun j => if j ∈ K then xs j else H.Sp_nonempty.choose) i z)|)).card : ℝ) ≤
                Real.exp (Cstar κ.u κ.ξ * H.Q) ∧
              xs i ∈ H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
                i ∈ J ∧ 2 ≤ J.card ∧ κ.ξ < |inter (T.S.E k) c H.π.w J
                  (Function.update (fun j => if j ∈ K then xs j else H.Sp_nonempty.choose) i z)|) := by
  classical
  intro xs hxs hnotModerate
  have hnotFull : ¬ ModerateOn (T.S.E k) c H.π.w κ.ξ xs Finset.univ := by
    intro hall
    apply hnotModerate
    intro l J hJcard
    simpa [H.homogeneous l] using hall J (Finset.subset_univ _) hJcard
  obtain ⟨K, hKgood, hKmax⟩ :=
    exists_maximal_moderateOn (T.S.E k) c H.π.w κ.ξ xs
  have hKne : K ≠ Finset.univ := by
    intro hEq
    apply hnotFull
    simpa [hEq] using hKgood
  refine ⟨K, hKgood, hKne, ?_⟩
  intro i hi
  have hnotIns := moderateOn_insert_not (T.S.E k) c H.π.w κ.ξ xs K hKmax i hi
  unfold ModerateOn at hnotIns
  push_neg at hnotIns
  obtain ⟨J, hJsub, hJcard, hJlarge⟩ := hnotIns
  have hiJ : i ∈ J := by
    by_contra hni
    have hJK : J ⊆ K := by
      intro j hj
      rcases Finset.mem_insert.mp (hJsub hj) with hEq | hjK
      · subst j
        exact False.elim (hni hj)
      · exact hjK
    exact (not_lt_of_ge (hKgood J hJK hJcard)) hJlarge
  let fill : Fin κ.u → Fin (T.S.N k) :=
    fun j => if j ∈ K then xs j else H.Sp_nonempty.choose
  have hfillSupport : ∀ j, j ≠ i → fill j ∈ H.Sp := by
    intro j hji
    by_cases hjK : j ∈ K
    · simpa [fill, hjK] using hxs j
    · simp [fill, hjK, H.Sp_nonempty.choose_spec]
  have hInterEq (z : Fin (T.S.N k)) :
      inter (T.S.E k) c H.π.w J (Function.update xs i z) =
        inter (T.S.E k) c H.π.w J (Function.update fill i z) := by
    unfold inter
    apply Finset.sum_congr rfl
    intro y hy
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hji : j = i
    · subst j
      simp
    · have hjK : j ∈ K := by
        rcases Finset.mem_insert.mp (hJsub hj) with hEq | hjK
        · exact False.elim (hji hEq)
        · exact hjK
      simp [fill, hjK, hji]
  have hcard := hExtension i fill hfillSupport
  have hmem : xs i ∈ H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
      i ∈ J ∧ 2 ≤ J.card ∧ κ.ξ < |inter (T.S.E k) c H.π.w J
        (Function.update fill i z)|) := by
    apply Finset.mem_filter.mpr
    refine ⟨hxs i, ⟨J, hiJ, hJcard, ?_⟩⟩
    rw [← hInterEq (xs i)]
    simpa [Function.update_self] using hJlarge
  exact ⟨hcard, hmem⟩

private theorem moderate_positive_sum_on_subset (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (k : ℕ) (c : Colour) (C0 : ℝ)
    (H : HomogeneousInput κ hκ T k c C0)
    (hPositive : ∀ u' ≤ κ.u, ∀ I' : Finset (Fin u'),
      (∑ xs : Fin u' → Fin (T.S.N k),
        if Moderate (T.S.E k) c (fun l => (H.S.π l).w) (2 * κ.ξ) xs
        then prodW H.S.τ.w xs *
          posTerm (T.S.E k) c (fun l => (H.S.π l).w) I' xs else 0) ≤ 2)
    (K : Finset (Fin κ.u)) (I : Finset (Fin κ.u)) (hI : I ⊆ K)
    (z₀ : Fin (T.S.N k)) :
    (∑ xK : K → Fin (T.S.N k),
      if (∀ i : K, xK i ∈ H.Sp) ∧
          ModerateOn (T.S.E k) c H.π.w κ.ξ
            (fun j => if h : j ∈ K then xK ⟨j, h⟩ else z₀) K
      then (∏ i : K, H.S.τ.w (xK i)) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I
            (fun j => if h : j ∈ K then xK ⟨j, h⟩ else z₀)
      else 0) ≤ 2 := by
  classical
  let m : ℕ := K.card
  have hm : m ≤ κ.u := by
    dsimp [m]
    simpa using Finset.card_le_univ K
  let eK : Fin m ≃ K := K.orderIsoOfFin (by rfl)
  let emb : Fin m ↪ Fin κ.u := (K.orderEmbOfFin (by rfl)).toEmbedding
  let eFun : (Fin m → Fin (T.S.N k)) ≃ (K → Fin (T.S.N k)) :=
    Equiv.piCongrLeft (fun _ : K => Fin (T.S.N k)) eK
  let IFin : Finset (Fin m) := Finset.univ.filter (fun j => emb j ∈ I)
  let fill (xK : K → Fin (T.S.N k)) : Fin κ.u → Fin (T.S.N k) :=
    fun j => if h : j ∈ K then xK ⟨j, h⟩ else z₀
  let Good (xK : K → Fin (T.S.N k)) : Prop :=
    (∀ i : K, xK i ∈ H.Sp) ∧
      ModerateOn (T.S.E k) c H.π.w κ.ξ (fill xK) K
  have hIFinMap : IFin.map emb = I := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      have hiK : i ∈ K := hI hi
      let j : Fin m := eK.symm ⟨i, hiK⟩
      have heq : emb j = i := by
        have hsub : eK j = ⟨i, hiK⟩ := eK.apply_symm_apply ⟨i, hiK⟩
        calc
          emb j = (eK j).val := rfl
          _ = (⟨i, hiK⟩ : K).val := congrArg Subtype.val hsub
          _ = i := rfl
      have hmem : emb j ∈ I := by rw [heq]; exact hi
      apply Finset.mem_map.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, heq⟩
  have hfillEmb (xK : K → Fin (T.S.N k)) (j : Fin m) :
      fill xK (emb j) = eFun.symm xK j := by
    have hjK : emb j ∈ K := K.orderEmbOfFin_mem (by rfl) j
    have hsub : (⟨emb j, hjK⟩ : K) = eK j := by
      apply Subtype.ext
      rfl
    calc
      fill xK (emb j) = xK ⟨emb j, hjK⟩ := by simp [fill, hjK]
      _ = xK (eK j) := by rw [hsub]
      _ = eFun.symm xK j := by simp [eFun]
  have hmapModerate (xK : K → Fin (T.S.N k)) (hg : Good xK) :
      Moderate (T.S.E k) c (fun l => (H.S.π l).w) (2 * κ.ξ) (eFun.symm xK) := by
    intro l J hJcard
    have hJbigSub : J.map emb ⊆ K := by
      intro i hi
      rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
      exact (eK j).property
    have hJbigCard : (J.map emb).card = J.card := by simp
    have hKbound := hg.2 (J.map emb) hJbigSub (by omega)
    have hInterEq :
        inter (T.S.E k) c H.π.w (J.map emb) (fill xK) =
          inter (T.S.E k) c H.π.w J (eFun.symm xK) := by
      have h := inter_map_embedding (T.S.E k) c H.π.w emb J (fill xK)
      simpa [hfillEmb xK] using h
    change |inter (T.S.E k) c (H.S.π l).w J (eFun.symm xK)| ≤ 2 * κ.ξ
    have hLawW : (H.S.π l).w = H.π.w :=
      congrArg (fun ν : Law (T.S.N k) => ν.w) (H.homogeneous l)
    rw [hLawW, ← hInterEq]
    exact le_trans hKbound (by nlinarith [hκ.ξ_rng.1])
  have hWeightEq (xK : K → Fin (T.S.N k)) :
      prodW H.S.τ.w (eFun.symm xK) = ∏ i : K, H.S.τ.w (xK i) := by
    unfold prodW
    calc
      (∏ j : Fin m, H.S.τ.w ((eFun.symm xK) j)) =
          ∏ j : Fin m, H.S.τ.w (xK (eK j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp [eFun]
      _ = ∏ i : K, H.S.τ.w (xK i) :=
        Fintype.prod_equiv eK _ _ (by intro j; rfl)
  have hPosTermEq (xK : K → Fin (T.S.N k)) :
      posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (fill xK) =
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) IFin (eFun.symm xK) := by
    calc
      posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (fill xK) =
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (IFin.map emb) (fill xK) := by
            rw [hIFinMap]
      _ = posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) IFin
          (fun j => fill xK (emb j)) :=
            posTerm_map_embedding (T.S.E k) c H.π.w emb IFin (fill xK)
      _ = posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) IFin (eFun.symm xK) := by
            congr 1
            funext j
            exact hfillEmb xK j
  have hpoint : ∀ xK : K → Fin (T.S.N k),
      (if Good xK then (∏ i : K, H.S.τ.w (xK i)) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (fill xK) else 0) ≤
        (if Moderate (T.S.E k) c (fun l => (H.S.π l).w) (2 * κ.ξ) (eFun.symm xK)
        then prodW H.S.τ.w (eFun.symm xK) *
          posTerm (T.S.E k) c (fun l => (H.S.π l).w) IFin (eFun.symm xK) else 0) := by
    intro xK
    by_cases hg : Good xK
    · have hmod := hmapModerate xK hg
      have hw := hWeightEq xK
      have hp := hPosTermEq xK
      have hpS : posTerm (T.S.E k) c (fun l => (H.S.π l).w) I (fill xK) =
          posTerm (T.S.E k) c (fun l => (H.S.π l).w) IFin (eFun.symm xK) := by
        simpa [H.homogeneous] using hp
      simp only [if_pos hg, if_pos hmod]
      have hposLeft : posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (fill xK) =
          posTerm (T.S.E k) c (fun l => (H.S.π l).w) I (fill xK) := by
        simp [H.homogeneous]
      have hEq :
          (∏ i : K, H.S.τ.w (xK i)) *
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (fill xK) =
            prodW H.S.τ.w (eFun.symm xK) *
              posTerm (T.S.E k) c (fun l => (H.S.π l).w) IFin (eFun.symm xK) := by
        calc
          (∏ i : K, H.S.τ.w (xK i)) *
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (fill xK) =
            (∏ i : K, H.S.τ.w (xK i)) *
              posTerm (T.S.E k) c (fun l => (H.S.π l).w) I (fill xK) := by rw [hposLeft]
          _ = (∏ i : K, H.S.τ.w (xK i)) *
              posTerm (T.S.E k) c (fun l => (H.S.π l).w) IFin (eFun.symm xK) := by rw [hpS]
          _ = prodW H.S.τ.w (eFun.symm xK) *
              posTerm (T.S.E k) c (fun l => (H.S.π l).w) IFin (eFun.symm xK) := by
            exact congrArg (fun w : ℝ =>
              w * posTerm (T.S.E k) c (fun l => (H.S.π l).w) IFin (eFun.symm xK)) hw.symm
      exact hEq.le
    ·
      rw [if_neg hg]
      rcases Classical.em (Moderate (T.S.E k) c (fun l => (H.S.π l).w) (2 * κ.ξ) (eFun.symm xK)) with hmTrue | hmFalse
      · have hwpos : 0 ≤ prodW H.S.τ.w (eFun.symm xK) := by
          unfold prodW
          apply Finset.prod_nonneg
          intro i hi
          exact H.S.τ.nonneg _
        simpa [hmTrue] using mul_nonneg hwpos
          (HypercubeRamsey.Lane_q_s12_peel.posTerm_nonneg
            (T.S.E k) c H.S.π IFin (eFun.symm xK))
      · simp [hmFalse]
  have hsum :
      (∑ xK : K → Fin (T.S.N k),
        if Good xK then (∏ i : K, H.S.τ.w (xK i)) *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (fill xK) else 0) ≤ 2 := by
    calc
      _ = ∑ xFin : Fin m → Fin (T.S.N k),
          (if Good (eFun xFin) then (∏ i : K, H.S.τ.w ((eFun xFin) i)) *
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (fill (eFun xFin)) else 0) := by
        symm
        exact Fintype.sum_equiv eFun _ _ (by intro xFin; rfl)
      _ ≤ ∑ xFin : Fin m → Fin (T.S.N k),
          (if Moderate (T.S.E k) c (fun l => (H.S.π l).w) (2 * κ.ξ) xFin
          then prodW H.S.τ.w xFin *
            posTerm (T.S.E k) c (fun l => (H.S.π l).w) IFin xFin else 0) := by
        apply Finset.sum_le_sum
        intro xFin hx
        simpa [Equiv.symm_apply_apply] using hpoint (eFun xFin)
      _ ≤ 2 := hPositive m hm IFin
  exact hsum

private def peelingFill {κ : CConsts} {hκ : κ.Admissible} {T : Stage} {k : ℕ}
    {c : Colour} {C0 : ℝ} (H : HomogeneousInput κ hκ T k c C0)
    (K : Finset (Fin κ.u)) (z₀ : Fin (T.S.N k))
    (xK : K → Fin (T.S.N k)) : Fin κ.u → Fin (T.S.N k) :=
  fun j => if h : j ∈ K then xK ⟨j, h⟩ else z₀

private noncomputable def peelingExtSet {κ : CConsts} {hκ : κ.Admissible} {T : Stage} {k : ℕ}
    {c : Colour} {C0 : ℝ} (H : HomogeneousInput κ hκ T k c C0)
    (K : Finset (Fin κ.u)) (z₀ : Fin (T.S.N k))
    (xK : K → Fin (T.S.N k)) (i : Fin κ.u) : Finset (Fin (T.S.N k)) :=
  H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u), i ∈ J ∧ 2 ≤ J.card ∧
    κ.ξ < |inter (T.S.E k) c H.π.w J
      (Function.update (peelingFill H K z₀ xK) i z)|)

private def peelingFixedGood {κ : CConsts} {hκ : κ.Admissible} {T : Stage} {k : ℕ}
    {c : Colour} {C0 : ℝ} (H : HomogeneousInput κ hκ T k c C0)
    (K : Finset (Fin κ.u)) (z₀ : Fin (T.S.N k))
    (xs : Fin κ.u → Fin (T.S.N k)) : Prop :=
  (∀ i ∈ K, xs i ∈ H.Sp) ∧
    ModerateOn (T.S.E k) c H.π.w κ.ξ xs K ∧
    ∀ i, i ∉ K → xs i ∈ peelingExtSet H K z₀ (fun j => xs j) i

private theorem fixed_subset_peel_bound (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (k : ℕ) (c : Colour) (C0 : ℝ)
    (H : HomogeneousInput κ hκ T k c C0)
    (hExtension : ∀ i₀ : Fin κ.u,
      ∀ xs : Fin κ.u → Fin (T.S.N k),
        (∀ i, i ≠ i₀ → xs i ∈ H.Sp) →
        ((H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
          i₀ ∈ J ∧ 2 ≤ J.card ∧
            κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)).card : ℝ) ≤
          Real.exp (Cstar κ.u κ.ξ * H.Q))
    (hPositive : ∀ u' ≤ κ.u, ∀ I' : Finset (Fin u'),
      (∑ xs : Fin u' → Fin (T.S.N k),
        if Moderate (T.S.E k) c (fun l => (H.S.π l).w) (2 * κ.ξ) xs
        then prodW H.S.τ.w xs *
          posTerm (T.S.E k) c (fun l => (H.S.π l).w) I' xs else 0) ≤ 2)
    (K : Finset (Fin κ.u)) (hKne : K ≠ Finset.univ)
    (z₀ : Fin (T.S.N k)) (hz₀ : z₀ ∈ H.Sp) :
    ∀ I : Finset (Fin κ.u),
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if peelingFixedGood H K z₀ xs
        then prodW H.S.τ.w xs * posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs
        else 0) ≤ 2 * H.gamma := by
  classical
  intro I
  let O := {i : Fin κ.u // i ∉ K}
  let split := Equiv.piEquivPiSubtypeProd (fun i : Fin κ.u => i ∈ K)
    (fun _ => Fin (T.S.N k))
  let fill := peelingFill H K z₀
  let Ext (xK : K → Fin (T.S.N k)) (i : O) := peelingExtSet H K z₀ xK i.1
  let outWeight (xK : K → Fin (T.S.N k)) (i : O) (z : Fin (T.S.N k)) :=
    if z ∈ Ext xK i then H.S.τ.w z *
      Real.rpow (deg (T.S.E k) c H.π.w z) (-(H.S.d : ℝ)) else 0
  let goodK (xK : K → Fin (T.S.N k)) :=
    (∀ i : K, xK i ∈ H.Sp) ∧
      ModerateOn (T.S.E k) c H.π.w κ.ξ (fill xK) K
  have hdegUpper (x : Fin (T.S.N k)) : deg (T.S.E k) c H.π.w x ≤ 1 := by
    unfold deg
    calc
      (∑ y, H.π.w y * hit (T.S.E k) c x y) ≤ ∑ y, H.π.w y := by
        apply Finset.sum_le_sum
        intro y hy
        have hhit : hit (T.S.E k) c x y ≤ 1 := by
          unfold hit
          split_ifs <;> norm_num
        calc
          H.π.w y * hit (T.S.E k) c x y ≤ H.π.w y * 1 :=
            mul_le_mul_of_nonneg_left hhit (H.π.nonneg y)
          _ = H.π.w y := by ring
      _ = 1 := H.π.sum_eq_one
  have hAmaxNonneg : 0 ≤ H.Sp.sup' H.Sp_nonempty
      (fun x => H.S.τ.w x * Real.rpow (deg (T.S.E k) c H.π.w x) (-(H.S.d : ℝ))) := by
    obtain ⟨x, hx⟩ := H.Sp_nonempty
    exact le_trans (mul_nonneg (H.S.τ.nonneg x)
      (Real.rpow_nonneg (H.degree_positive x hx).le _))
      (Finset.le_sup'
        (fun x => H.S.τ.w x * Real.rpow (deg (T.S.E k) c H.π.w x) (-(H.S.d : ℝ)))
        hx)
  have hExtWeight (xK : K → Fin (T.S.N k)) (hg : goodK xK) (i : O) :
      (∑ z, outWeight xK i z) ≤ H.gamma := by
    let Eset := Ext xK i
    have hfillSupport : ∀ j, j ≠ i.1 → fill xK j ∈ H.Sp := by
      intro j hji
      by_cases hjK : j ∈ K
      · have hcoord : fill xK j = xK ⟨j, hjK⟩ := by
          simp [fill, peelingFill, hjK]
        rw [hcoord]
        exact hg.1 ⟨j, hjK⟩
      · have hcoord : fill xK j = z₀ := by
          simp [fill, peelingFill, hjK]
        rw [hcoord]
        exact hz₀
    have hcard := hExtension i.1 (fill xK) hfillSupport
    have hcardR : (Eset.card : ℝ) ≤ Real.exp (Cstar κ.u κ.ξ * H.Q) := by
      dsimp [Eset, Ext]
      simpa [peelingExtSet, fill] using hcard
    calc
      (∑ z, outWeight xK i z) =
          ∑ z ∈ Eset, H.S.τ.w z *
            Real.rpow (deg (T.S.E k) c H.π.w z) (-(H.S.d : ℝ)) := by
        simp [outWeight, Eset, Ext]
      _ ≤ ∑ z ∈ Eset, H.Sp.sup' H.Sp_nonempty
            (fun x => H.S.τ.w x *
              Real.rpow (deg (T.S.E k) c H.π.w x) (-(H.S.d : ℝ)) ) := by
        apply Finset.sum_le_sum
        intro z hz
        exact Finset.le_sup'
          (fun x => H.S.τ.w x * Real.rpow (deg (T.S.E k) c H.π.w x) (-(H.S.d : ℝ)))
          (Finset.mem_filter.mp hz).1
      _ = (Eset.card : ℝ) * H.Sp.sup' H.Sp_nonempty
            (fun x => H.S.τ.w x *
              Real.rpow (deg (T.S.E k) c H.π.w x) (-(H.S.d : ℝ))) := by
        simp
      _ ≤ Real.exp (Cstar κ.u κ.ξ * H.Q) * H.Sp.sup' H.Sp_nonempty
            (fun x => H.S.τ.w x *
              Real.rpow (deg (T.S.E k) c H.π.w x) (-(H.S.d : ℝ))) :=
        mul_le_mul_of_nonneg_right hcardR hAmaxNonneg
      _ = H.gamma := H.gamma_eq.symm
  have hOutsideSum (xK : K → Fin (T.S.N k)) (hg : goodK xK) :
      (∑ xO : O → Fin (T.S.N k), ∏ i : O, outWeight xK i (xO i)) ≤
        H.gamma ^ Fintype.card O := by
    calc
      (∑ xO : O → Fin (T.S.N k), ∏ i : O, outWeight xK i (xO i)) =
          ∏ i : O, ∑ z, outWeight xK i z := by
        exact (Fintype.prod_sum (fun i z => outWeight xK i z)).symm
      _ ≤ ∏ i : O, H.gamma := by
        apply Finset.prod_le_prod₀
        · intro i hi
          apply Finset.sum_nonneg
          intro z hz
          by_cases hzE : z ∈ Ext xK i
          · simp [outWeight, hzE]
            exact mul_nonneg (H.S.τ.nonneg z) (by
              have hdz := H.degree_positive z (Finset.mem_filter.mp hzE).1
              positivity)
          · simp [outWeight, hzE]
        · intro i hi
          exact hExtWeight xK hg i
      _ = H.gamma ^ Fintype.card O := by simp
  have hOpos : 0 < Fintype.card O := by
    have hex : ∃ i : Fin κ.u, i ∉ K := by
      by_contra h
      push_neg at h
      apply hKne
      ext i
      simp [h i]
    rcases hex with ⟨i, hi⟩
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  have hgammaPow : H.gamma ^ Fintype.card O ≤ H.gamma := by
    have he : Fintype.card O = (Fintype.card O - 1) + 1 := by omega
    rw [he, pow_add, pow_one]
    calc
      H.gamma ^ (Fintype.card O - 1) * H.gamma ≤ 1 * H.gamma := by
        apply mul_le_mul_of_nonneg_right _ H.gamma_nonneg
        exact pow_le_one₀ H.gamma_nonneg H.gamma_lt_one.le
      _ = H.gamma := by ring
  have hbase :
      (∑ xK : K → Fin (T.S.N k),
        if goodK xK then (∏ i : K, H.S.τ.w (xK i)) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK) else 0) ≤ 2 := by
    exact moderate_positive_sum_on_subset κ hκ T k c C0 H hPositive K (I ∩ K)
      (Finset.inter_subset_right) z₀
  let full (xK : K → Fin (T.S.N k)) (xO : O → Fin (T.S.N k)) :=
    split.symm (xK, xO)
  let pairGood (xK : K → Fin (T.S.N k)) (xO : O → Fin (T.S.N k)) :=
    peelingFixedGood H K z₀ (full xK xO)
  have hfullK (xK : K → Fin (T.S.N k)) (xO : O → Fin (T.S.N k)) (i : K) :
      full xK xO i.1 = xK i := by
    simp [full, split, Equiv.piEquivPiSubtypeProd]
  have hfullO (xK : K → Fin (T.S.N k)) (xO : O → Fin (T.S.N k)) (i : O) :
      full xK xO i.1 = xO i := by
    change (Equiv.piEquivPiSubtypeProd (fun j : Fin κ.u => j ∈ K)
      (fun _ => Fin (T.S.N k))).symm (xK, xO) i.1 = xO i
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [i.2]
  have hpairGood (xK : K → Fin (T.S.N k)) (xO : O → Fin (T.S.N k))
      (hp : pairGood xK xO) :
      goodK xK ∧ ∀ i : O, xO i ∈ Ext xK i := by
    dsimp [pairGood, peelingFixedGood] at hp
    rcases hp with ⟨hsp, hmod, hext⟩
    constructor
    · constructor
      · intro i
        simpa [hfullK xK xO i] using hsp i.1 i.2
      · intro J hJ hJcard
        have hsame : inter (T.S.E k) c H.π.w J (fill xK) =
            inter (T.S.E k) c H.π.w J (full xK xO) := by
          unfold inter
          apply Finset.sum_congr rfl
          intro y hy
          congr 1
          apply Finset.prod_congr rfl
          intro j hj
          have hjK : j ∈ K := hJ hj
          have hcoord : fill xK j = full xK xO j := by
            calc
              fill xK j = xK ⟨j, hjK⟩ := by simp [fill, peelingFill, hjK]
              _ = full xK xO j := (hfullK xK xO ⟨j, hjK⟩).symm
          rw [hcoord]
        have h := hmod J hJ hJcard
        rw [hsame]
        exact h
    · intro i
      have h := hext i.1 i.2
      rw [hfullO xK xO i] at h
      have hrestriction : (fun j : K => full xK xO j.1) = xK := by
        funext j
        exact hfullK xK xO j
      simpa [Ext, hrestriction] using h
  have hdegNonneg (x : Fin (T.S.N k)) : 0 ≤ deg (T.S.E k) c H.π.w x := by
    unfold deg
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg (H.π.nonneg y)
    unfold hit
    split_ifs <;> norm_num
  have houtWeightNonneg (xK : K → Fin (T.S.N k)) (i : O) (z : Fin (T.S.N k)) :
      0 ≤ outWeight xK i z := by
    by_cases hz : z ∈ Ext xK i
    · simp [outWeight, hz]
      exact mul_nonneg (H.S.τ.nonneg z) (by
        have hdz := H.degree_positive z (Finset.mem_filter.mp hz).1
        positivity)
    · simp [outWeight, hz]
  have hbaseNonneg (xK : K → Fin (T.S.N k)) :
      0 ≤ (∏ i : K, H.S.τ.w (xK i)) *
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK) := by
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i hi
      exact H.S.τ.nonneg _
    · exact posTerm_nonneg (T.S.E k) c
        (fun _ : Fin H.S.d => H.π) (I ∩ K) (fill xK)
  have htermBound (xK : K → Fin (T.S.N k)) (xO : O → Fin (T.S.N k))
      (hp : pairGood xK xO) :
      prodW H.S.τ.w (full xK xO) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (full xK xO) ≤
        (∏ i : K, H.S.τ.w (xK i)) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK) *
            ∏ i : O, outWeight xK i (xO i) := by
    obtain ⟨hg, hout⟩ := hpairGood xK xO hp
    have hfullSupport (i : Fin κ.u) : full xK xO i ∈ H.Sp := by
      by_cases hiK : i ∈ K
      · have h := hg.1 ⟨i, hiK⟩
        simpa [hfullK xK xO ⟨i, hiK⟩] using h
      · have h := hout ⟨i, hiK⟩
        have hsp := (Finset.mem_filter.mp h).1
        simpa [hfullO xK xO ⟨i, hiK⟩] using hsp
    have hdegPos (i : Fin κ.u) : 0 < deg (T.S.E k) c H.π.w (full xK xO i) :=
      H.degree_positive _ (hfullSupport i)
    have hdegUpper' (i : Fin κ.u) :
        deg (T.S.E k) c H.π.w (full xK xO i) ≤ 1 := hdegUpper _
    have hdelete := HypercubeRamsey.Lane_q_s12_peel.posTerm_delete_compl
      (d := H.S.d) (T.S.E k) c H.π (full xK xO) I K hdegPos hdegUpper'
    have hPosRestrict :
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (full xK xO) =
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK) := by
      unfold posTerm
      apply Finset.prod_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro y hy
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hjK : j ∈ K := (Finset.mem_inter.mp hj).2
      have hcoord : fill xK j = full xK xO j := by
        calc
          fill xK j = xK ⟨j, hjK⟩ := by simp [fill, peelingFill, hjK]
          _ = full xK xO j := (hfullK xK xO ⟨j, hjK⟩).symm
      rw [← hcoord]
    have hweightSplit : prodW H.S.τ.w (full xK xO) =
        (∏ i : K, H.S.τ.w (xK i)) *
          (∏ i : O, H.S.τ.w (xO i)) := by
      unfold prodW
      have hKcoord : (∏ i : K, H.S.τ.w (xK i)) =
          ∏ i : K, H.S.τ.w (full xK xO i.1) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hfullK xK xO i]
      have hKfinset : (∏ i : K, H.S.τ.w (full xK xO i.1)) =
          ∏ i ∈ K, H.S.τ.w (full xK xO i) := by
        symm
        exact Finset.prod_subtype (p := fun i : Fin κ.u => i ∈ K)
          (F := Finset.Subtype.fintype K) K (by intro i; simp)
          (fun i => H.S.τ.w (full xK xO i))
      have hOcoord : (∏ i : O, H.S.τ.w (xO i)) =
          ∏ i : O, H.S.τ.w (full xK xO i.1) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hfullO xK xO i]
      have hOutsideProduct (f : Fin κ.u → ℝ) :
          (∏ i : O, f i.1) = ∏ i ∈ Kᶜ, f i := by
        symm
        simpa [O] using
          (Finset.prod_subtype (Kᶜ) (by intro i; simp [O]) f)
      have hOfinset : (∏ i : O, H.S.τ.w (full xK xO i.1)) =
          ∏ i ∈ Kᶜ, H.S.τ.w (full xK xO i) :=
        hOutsideProduct (fun i => H.S.τ.w (full xK xO i))
      calc
        (∏ i : Fin κ.u, H.S.τ.w (full xK xO i)) =
            (∏ i ∈ K, H.S.τ.w (full xK xO i)) *
              (∏ i ∈ Kᶜ, H.S.τ.w (full xK xO i)) := by
          exact (Finset.prod_mul_prod_compl K
            (fun i => H.S.τ.w (full xK xO i))).symm
        _ = _ := by rw [← hKfinset, ← hKcoord, ← hOfinset, ← hOcoord]
    let D (i : Fin κ.u) := Real.rpow
      (deg (T.S.E k) c H.π.w (full xK xO i)) (-(H.S.d : ℝ))
    have hDsubtype : (∏ i : O, D i.1) = ∏ i ∈ Kᶜ, D i := by
      symm
      simpa [O] using
        (Finset.prod_subtype (Kᶜ) (by intro i; simp [O]) (fun i => D i))
    have hWeightO : 0 ≤ ∏ i : O, H.S.τ.w (xO i) := by
      apply Finset.prod_nonneg
      intro i hi
      exact H.S.τ.nonneg _
    have hBase : 0 ≤ (∏ i : K, H.S.τ.w (xK i)) *
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK) :=
      hbaseNonneg xK
    have hFullWNonneg : 0 ≤ prodW H.S.τ.w (full xK xO) := by
      unfold prodW
      apply Finset.prod_nonneg
      intro i hi
      exact H.S.τ.nonneg _
    have hOutTerm :
        (∏ i : O, H.S.τ.w (xO i) * D i.1) =
          ∏ i : O, outWeight xK i (xO i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hmember : xO i ∈ Ext xK i := hout i
      simp [outWeight, hmember, D, hfullO xK xO i]
    have hmulOut :
        (∏ i : O, H.S.τ.w (xO i) * D i.1) =
          (∏ i : O, H.S.τ.w (xO i)) * (∏ i : O, D i.1) := by
      exact Finset.prod_mul_distrib
    have hdelete' :
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (full xK xO) ≤
          (∏ i ∈ Kᶜ, D i) *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK) := by
      simpa [D, hPosRestrict] using hdelete
    calc
      prodW H.S.τ.w (full xK xO) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (full xK xO) ≤
          prodW H.S.τ.w (full xK xO) *
            ((∏ i ∈ Kᶜ, D i) *
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK)) :=
        mul_le_mul_of_nonneg_left hdelete' hFullWNonneg
      _ = ((∏ i : K, H.S.τ.w (xK i)) *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK)) *
          ((∏ i : O, H.S.τ.w (xO i)) * (∏ i : O, D i.1)) := by
        rw [hweightSplit, ← hDsubtype]
        ring
      _ = ((∏ i : K, H.S.τ.w (xK i)) *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK)) *
          (∏ i : O, H.S.τ.w (xO i) * D i.1) := by
        rw [← hmulOut]
      _ = (∏ i : K, H.S.τ.w (xK i)) *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK) *
          ∏ i : O, outWeight xK i (xO i) := by rw [hOutTerm]
  let baseK (xK : K → Fin (T.S.N k)) :=
    (∏ i : K, H.S.τ.w (xK i)) *
      posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (I ∩ K) (fill xK)
  let outsideProd (xK : K → Fin (T.S.N k)) (xO : O → Fin (T.S.N k)) :=
    ∏ i : O, outWeight xK i (xO i)
  have hbaseNonneg' (xK : K → Fin (T.S.N k)) : 0 ≤ baseK xK := hbaseNonneg xK
  have houtsideProdNonneg (xK : K → Fin (T.S.N k)) (xO : O → Fin (T.S.N k)) :
      0 ≤ outsideProd xK xO := by
    apply Finset.prod_nonneg
    intro i hi
    exact houtWeightNonneg xK i (xO i)
  have hreindex :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if peelingFixedGood H K z₀ xs
        then prodW H.S.τ.w xs *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0) =
      ∑ xK : K → Fin (T.S.N k), ∑ xO : O → Fin (T.S.N k),
        if pairGood xK xO
        then prodW H.S.τ.w (full xK xO) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (full xK xO) else 0 := by
    calc
      _ = ∑ p : (K → Fin (T.S.N k)) × (O → Fin (T.S.N k)),
          if peelingFixedGood H K z₀ (split.symm p)
          then prodW H.S.τ.w (split.symm p) *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (split.symm p) else 0 := by
        exact Fintype.sum_equiv split
          (fun xs => if peelingFixedGood H K z₀ xs
            then prodW H.S.τ.w xs *
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0)
          (fun p => if peelingFixedGood H K z₀ (split.symm p)
            then prodW H.S.τ.w (split.symm p) *
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (split.symm p) else 0)
          (by intro xs; simp)
      _ = _ := by simp only [Fintype.sum_prod_type, pairGood, full]
  have hinner (xK : K → Fin (T.S.N k)) :
      (∑ xO : O → Fin (T.S.N k),
        if pairGood xK xO
        then prodW H.S.τ.w (full xK xO) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (full xK xO) else 0) ≤
        if goodK xK then baseK xK * (∑ xO : O → Fin (T.S.N k), outsideProd xK xO) else 0 := by
    by_cases hg : goodK xK
    · calc
        _ ≤ ∑ xO : O → Fin (T.S.N k), baseK xK * outsideProd xK xO := by
          apply Finset.sum_le_sum
          intro xO hxO
          by_cases hp : pairGood xK xO
          · simpa [hp, baseK, outsideProd, pairGood, full] using htermBound xK xO hp
          · simp [hp]
            exact mul_nonneg (hbaseNonneg' xK) (houtsideProdNonneg xK xO)
        _ = baseK xK * (∑ xO : O → Fin (T.S.N k), outsideProd xK xO) := by
          rw [← Finset.mul_sum]
        _ = if goodK xK then baseK xK * (∑ xO : O → Fin (T.S.N k), outsideProd xK xO) else 0 := by
          simp [hg]
    · have hpairFalse : ∀ xO : O → Fin (T.S.N k), ¬ pairGood xK xO := by
        intro xO hp
        exact hg (hpairGood xK xO hp).1
      simp only [if_neg hg]
      apply le_of_eq
      rw [Finset.sum_eq_zero]
      intro xO hxO
      simp [hpairFalse xO]
  have hdoubleBound :
      (∑ xK : K → Fin (T.S.N k), ∑ xO : O → Fin (T.S.N k),
        if pairGood xK xO
        then prodW H.S.τ.w (full xK xO) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I (full xK xO) else 0) ≤
      ∑ xK : K → Fin (T.S.N k),
        if goodK xK then baseK xK * (∑ xO : O → Fin (T.S.N k), outsideProd xK xO) else 0 := by
    apply Finset.sum_le_sum
    intro xK hxK
    exact hinner xK
  have houterBound :
      (∑ xK : K → Fin (T.S.N k),
        if goodK xK then baseK xK * (∑ xO : O → Fin (T.S.N k), outsideProd xK xO) else 0) ≤
      ∑ xK : K → Fin (T.S.N k), if goodK xK then baseK xK * H.gamma else 0 := by
    apply Finset.sum_le_sum
    intro xK hxK
    by_cases hg : goodK xK
    · simp only [if_pos hg]
      exact mul_le_mul_of_nonneg_left
        (le_trans (hOutsideSum xK hg) hgammaPow) (hbaseNonneg' xK)
    · simp [hg]
  have hbaseSum :
      (∑ xK : K → Fin (T.S.N k), if goodK xK then baseK xK else 0) ≤ 2 := by
    simpa [baseK] using hbase
  calc
    (∑ xs : Fin κ.u → Fin (T.S.N k),
      if peelingFixedGood H K z₀ xs
      then prodW H.S.τ.w xs *
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0) ≤
        ∑ xK : K → Fin (T.S.N k),
          if goodK xK then baseK xK * H.gamma else 0 := by
      rw [hreindex]
      exact le_trans hdoubleBound houterBound
    _ = H.gamma * (∑ xK : K → Fin (T.S.N k),
          if goodK xK then baseK xK else 0) := by
      calc
        _ = ∑ xK : K → Fin (T.S.N k),
              H.gamma * (if goodK xK then baseK xK else 0) := by
          apply Finset.sum_congr rfl
          intro xK hxK
          by_cases hg : goodK xK <;> simp [hg, mul_comm]
        _ = _ := by rw [← Finset.mul_sum]
    _ ≤ H.gamma * 2 := mul_le_mul_of_nonneg_left hbaseSum H.gamma_nonneg
    _ = 2 * H.gamma := by ring

/-- L12.5(iii): large-interaction tuples have bounded total positive-term mass. -/
theorem homogeneous_peeling (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hModerate : ModerateMomentClaim κ T c C0) :
    HomogeneousPeelingClaim κ hκ T c C0 := by
  classical
  unfold HomogeneousPeelingClaim
  filter_upwards [hModerate,
    homogeneous_extension_count κ hκ T hDeep c C0 hC0] with k hModerateK hExtension
  intro H
  have hdegOK : H.S.DegOK c C0 := by
    intro l x hx
    have hxSp : x ∈ H.Sp := by
      by_contra hxSp
      have hzero := H.τ_supported x hxSp
      rw [hzero] at hx
      norm_num at hx
    have hgate := H.degree_gate x hxSp
    simpa [H.homogeneous l] using hgate
  obtain ⟨_, hPositive⟩ := hModerateK H.S hdegOK
  let z₀ : Fin (T.S.N k) := H.Sp_nonempty.choose
  have hz₀ : z₀ ∈ H.Sp := H.Sp_nonempty.choose_spec
  have hExtensionH := hExtension H
  have hCover := maximal_moderate_extension_cover κ hκ T k c C0 H hExtensionH
  let badTerm (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :=
    if ¬ Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) κ.ξ xs
    then prodW H.S.τ.w xs *
      posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0
  let fixedTerm (K : Finset (Fin κ.u)) (I : Finset (Fin κ.u))
      (xs : Fin κ.u → Fin (T.S.N k)) :=
    if K ≠ Finset.univ then
      if peelingFixedGood H K z₀ xs then prodW H.S.τ.w xs *
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0
    else 0
  have hprodWNonneg (xs : Fin κ.u → Fin (T.S.N k)) :
      0 ≤ prodW H.S.τ.w xs := by
    unfold prodW
    apply Finset.prod_nonneg
    intro i hi
    exact H.S.τ.nonneg (xs i)
  have hposTermNonneg (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
      0 ≤ posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs :=
    HypercubeRamsey.Lane_q_s12_peel.posTerm_nonneg (T.S.E k) c
      (fun _ : Fin H.S.d => H.π) I xs
  have htermNonneg (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
      0 ≤ prodW H.S.τ.w xs *
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs :=
    mul_nonneg (hprodWNonneg xs) (hposTermNonneg I xs)
  have hfixedTermNonneg (K I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
      0 ≤ fixedTerm K I xs := by
    by_cases hK : K ≠ Finset.univ
    · by_cases hG : peelingFixedGood H K z₀ xs
      · simp [fixedTerm, hK, hG, htermNonneg]
      · simp [fixedTerm, hK, hG]
    · have hEq : K = Finset.univ := by
        by_contra hNe
        exact hK hNe
      simp [fixedTerm, hEq]
  have hfixedSumBound (K I : Finset (Fin κ.u)) :
      (∑ xs : Fin κ.u → Fin (T.S.N k), fixedTerm K I xs) ≤
        if K ≠ Finset.univ then 2 * H.gamma else 0 := by
    by_cases hK : K ≠ Finset.univ
    · simp only [fixedTerm, if_pos hK]
      exact fixed_subset_peel_bound κ hκ T k c C0 H hExtensionH hPositive
        K hK z₀ hz₀ I
    · have hEq : K = Finset.univ := by
        by_contra hNe
        exact hK hNe
      simp [fixedTerm, hEq]
  have hpoint (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
      badTerm I xs ≤ ∑ K : Finset (Fin κ.u), fixedTerm K I xs := by
    by_cases hmod : Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) κ.ξ xs
    · simp [badTerm, hmod]
      exact Finset.sum_nonneg (fun K hK => hfixedTermNonneg K I xs)
    · by_cases hsupport : ∀ i, xs i ∈ H.Sp
      · obtain ⟨K, hmodOn, hK, hext⟩ := hCover xs hsupport hmod
        have hgood : peelingFixedGood H K z₀ xs := by
          refine ⟨?_, hmodOn, ?_⟩
          · intro i hi
            exact hsupport i
          · intro i hi
            have hmem := (hext i hi).2
            have hfillEq : peelingFill H K z₀ (fun j : K => xs j.1) =
                (fun j => if j ∈ K then xs j else H.Sp_nonempty.choose) := by
              funext j
              by_cases hj : j ∈ K
              · simp [peelingFill, hj]
              · simp [peelingFill, z₀, hj]
            simpa [peelingExtSet, hfillEq] using hmem
        have htermEq : fixedTerm K I xs =
            prodW H.S.τ.w xs *
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs := by
          simp [fixedTerm, hK, hgood]
        calc
          badTerm I xs = fixedTerm K I xs := by
            simp [badTerm, hmod, htermEq]
          _ ≤ ∑ K' : Finset (Fin κ.u), fixedTerm K' I xs :=
            Finset.single_le_sum (fun K' hK' => hfixedTermNonneg K' I xs)
              (Finset.mem_univ K)
      · obtain ⟨i, hi⟩ := not_forall.mp hsupport
        have hτzero : H.S.τ.w (xs i) = 0 := H.τ_supported (xs i) hi
        have hweightZero : prodW H.S.τ.w xs = 0 := by
          unfold prodW
          exact Finset.prod_eq_zero (Finset.mem_univ i) hτzero
        simp [badTerm, hmod, hweightZero]
        exact Finset.sum_nonneg (fun K hK => hfixedTermNonneg K I xs)
  have hIbound (I : Finset (Fin κ.u)) :
      (∑ xs : Fin κ.u → Fin (T.S.N k), badTerm I xs) ≤
        (2 : ℝ) ^ κ.u * (2 * H.gamma) := by
    calc
      _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
            ∑ K : Finset (Fin κ.u), fixedTerm K I xs := by
        apply Finset.sum_le_sum
        intro xs hxs
        exact hpoint I xs
      _ = ∑ K : Finset (Fin κ.u),
            ∑ xs : Fin κ.u → Fin (T.S.N k), fixedTerm K I xs := by
        rw [Finset.sum_comm]
      _ ≤ ∑ K : Finset (Fin κ.u),
            (if K ≠ Finset.univ then 2 * H.gamma else 0) := by
        apply Finset.sum_le_sum
        intro K hK
        exact hfixedSumBound K I
      _ ≤ ∑ K : Finset (Fin κ.u), (2 * H.gamma) := by
        apply Finset.sum_le_sum
        intro K hK
        by_cases hKne : K ≠ Finset.univ
        · simp [hKne]
        · rw [if_neg hKne]
          exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) H.gamma_nonneg
      _ = (Fintype.card (Finset (Fin κ.u)) : ℝ) * (2 * H.gamma) := by simp
      _ = (2 : ℝ) ^ κ.u * (2 * H.gamma) := by
        simp [Fintype.card_finset]
  have hgammaNonneg : 0 ≤ H.gamma := H.gamma_nonneg
  have hpow2 : (2 : ℝ) ^ κ.u * (2 : ℝ) ^ κ.u = (4 : ℝ) ^ κ.u := by
    rw [← mul_pow]
    norm_num
  calc
    (∑ I : Finset (Fin κ.u),
      ∑ xs : Fin κ.u → Fin (T.S.N k), badTerm I xs) ≤
        ∑ I : Finset (Fin κ.u), (2 : ℝ) ^ κ.u * (2 * H.gamma) := by
      apply Finset.sum_le_sum
      intro I hI
      exact hIbound I
    _ = (Fintype.card (Finset (Fin κ.u)) : ℝ) *
          ((2 : ℝ) ^ κ.u * (2 * H.gamma)) := by simp
    _ = (2 : ℝ) ^ κ.u * ((2 : ℝ) ^ κ.u * (2 * H.gamma)) := by
      simp [Fintype.card_finset]
    _ ≤ (4 : ℝ) ^ (κ.u + 1) * H.gamma := by
      calc
        (2 : ℝ) ^ κ.u * ((2 : ℝ) ^ κ.u * (2 * H.gamma)) =
            (2 * (4 : ℝ) ^ κ.u) * H.gamma := by
          calc
            _ = ((2 : ℝ) ^ κ.u * (2 : ℝ) ^ κ.u) * (2 * H.gamma) := by ring
            _ = (4 : ℝ) ^ κ.u * (2 * H.gamma) := by rw [hpow2]
            _ = (2 * (4 : ℝ) ^ κ.u) * H.gamma := by ring
        _ ≤ (4 : ℝ) ^ (κ.u + 1) * H.gamma := by
          apply mul_le_mul_of_nonneg_right _ hgammaNonneg
          rw [pow_succ]
          have hp : 0 ≤ (4 : ℝ) ^ κ.u := pow_nonneg (by norm_num) _
          nlinarith

/-- L12.5(iv): even-moment and peeling bounds give the homogeneous lower-tail estimate. -/
theorem homogeneous_lower_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hModerate : ModerateMomentClaim κ T c C0)
    (hPeeling : HomogeneousPeelingClaim κ hκ T c C0) :
    ∀ᶠ k in atTop,
      ∀ H : HomogeneousInput κ hκ T k c C0, ∀ t : ℝ, 0 ≤ t → t < 1 →
        (∑ ys : Fin H.S.d → Fin (T.S.N k),
          if Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys < t
          then ∏ l, H.π.w (ys l) else 0) ≤
            (1 - t) ^ (-(κ.u : ℝ)) *
              ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
              4 ^ (κ.u + 1) * H.gamma) := by
  classical
  filter_upwards [hModerate, hPeeling] with k hModerateK hPeelingK
  intro H t ht0 ht1
  have hdegOK : H.S.DegOK c C0 := by
    intro l x hx
    have hxSp : x ∈ H.Sp := by
      by_contra hxSp
      have hzero := H.τ_supported x hxSp
      rw [hzero] at hx
      norm_num at hx
    have hgate := H.degree_gate x hxSp
    simpa [H.homogeneous l] using hgate
  obtain ⟨hmoderateSigned, hmoderatePositive⟩ := hModerateK H.S hdegOK
  have hpeel := hPeelingK H
  have hcenter := centered_moment_identity
    (N := T.S.N k) (d := H.S.d) (u := κ.u) H.S.τ.w H.S.τ.sum_eq_one
    (fun _ : Fin H.S.d => H.π.w) (fun _ => H.π.sum_eq_one)
    (fun _ x y => 1 + acoef (T.S.E k) c H.π.w x y)
  have hcenterEq :
      (∑ ys : Fin H.S.d → Fin (T.S.N k),
        (∏ l, H.π.w (ys l)) *
          (Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys - 1) ^ κ.u) =
      ∑ xs : Fin κ.u → Fin (T.S.N k),
        prodW H.S.τ.w xs * Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs := by
    simpa [Zmass, prodW, Phi, posTerm] using hcenter
  have hhitNonneg : ∀ x y, 0 ≤ hit (T.S.E k) c x y := by
    intro x y
    unfold hit
    split_ifs <;> norm_num
  have hdegreeNonneg : ∀ x, 0 ≤ deg (T.S.E k) c H.π.w x := by
    intro x
    unfold deg
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (H.π.nonneg y) (hhitNonneg x y)
  have hfactorNonneg : ∀ x y, 0 ≤ 1 + acoef (T.S.E k) c H.π.w x y := by
    intro x y
    have hEq : 1 + acoef (T.S.E k) c H.π.w x y =
        hit (T.S.E k) c x y / deg (T.S.E k) c H.π.w x := by
      unfold acoef
      ring
    rw [hEq]
    exact div_nonneg (hhitNonneg x y) (hdegreeNonneg x)
  have hposTermNonneg : ∀ (I : Finset (Fin κ.u))
      (xs : Fin κ.u → Fin (T.S.N k)),
      0 ≤ posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs := by
    intro I xs
    unfold posTerm
    apply Finset.prod_nonneg
    intro l hl
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg (H.π.nonneg y)
    apply Finset.prod_nonneg
    intro i hi
    exact hfactorNonneg (xs i) y
  have hprodWNonneg : ∀ xs : Fin κ.u → Fin (T.S.N k),
      0 ≤ prodW H.S.τ.w xs := by
    intro xs
    unfold prodW
    apply Finset.prod_nonneg
    intro i hi
    exact H.S.τ.nonneg (xs i)
  have hPhiBound (xs : Fin κ.u → Fin (T.S.N k)) :
      |Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs| ≤
        ∑ I : Finset (Fin κ.u),
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs := by
    unfold Phi
    calc
      |∑ I : Finset (Fin κ.u), (-1 : ℝ) ^ (κ.u - I.card) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs| ≤
        ∑ I : Finset (Fin κ.u),
          |(-1 : ℝ) ^ (κ.u - I.card) *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I : Finset (Fin κ.u),
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [abs_mul, abs_of_nonneg (hposTermNonneg I xs)]
        simp
  let M2 (xs : Fin κ.u → Fin (T.S.N k)) :=
    Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (2 * κ.ξ) xs
  let M1 (xs : Fin κ.u → Fin (T.S.N k)) :=
    Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) κ.ξ xs
  let modSum := ∑ xs : Fin κ.u → Fin (T.S.N k),
    if M2 xs then prodW H.S.τ.w xs *
      Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0
  let tailSum := ∑ xs : Fin κ.u → Fin (T.S.N k),
    if ¬ M2 xs then prodW H.S.τ.w xs *
      Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0
  have htermNonneg (xs : Fin κ.u → Fin (T.S.N k)) (I : Finset (Fin κ.u)) :
      0 ≤ prodW H.S.τ.w xs *
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs :=
    mul_nonneg (hprodWNonneg xs) (hposTermNonneg I xs)
  have htupleAbs (xs : Fin κ.u → Fin (T.S.N k)) :
      |(if ¬ M2 xs then prodW H.S.τ.w xs *
          Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0)| ≤
        ∑ I : Finset (Fin κ.u),
          if ¬ M1 xs then prodW H.S.τ.w xs *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0 := by
    by_cases hM2 : M2 xs
    · by_cases hM1 : M1 xs
      · simp [hM2, hM1]
      · simp [hM2, hM1]
        apply Finset.sum_nonneg
        intro I hI
        exact htermNonneg xs I
    · have hnotM1 : ¬ M1 xs := by
        intro hM1
        apply hM2
        intro l J hJ
        exact le_trans (hM1 l J hJ) (by nlinarith [hκ.ξ_rng.1])
      rw [if_pos hM2]
      calc
        |prodW H.S.τ.w xs * Phi (T.S.E k) c
            (fun _ : Fin H.S.d => H.π.w) xs| =
          prodW H.S.τ.w xs *
            |Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs| := by
              rw [abs_mul, abs_of_nonneg (hprodWNonneg xs)]
        _ ≤ prodW H.S.τ.w xs *
            (∑ I : Finset (Fin κ.u),
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs) :=
          mul_le_mul_of_nonneg_left (hPhiBound xs) (hprodWNonneg xs)
        _ = ∑ I : Finset (Fin κ.u),
              prodW H.S.τ.w xs *
                posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs := by
          rw [Finset.mul_sum]
        _ = ∑ I : Finset (Fin κ.u),
              if ¬ M1 xs then prodW H.S.τ.w xs *
                posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0 := by
          simp [hnotM1]
  have hnonmodAbs : |tailSum| ≤ 4 ^ (κ.u + 1) * H.gamma := by
    calc
      |tailSum| ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
          |if ¬ M2 xs then prodW H.S.τ.w xs *
            Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
          ∑ I : Finset (Fin κ.u),
            if ¬ M1 xs then prodW H.S.τ.w xs *
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0 := by
        apply Finset.sum_le_sum
        intro xs hxs
        exact htupleAbs xs
      _ = ∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ M1 xs then prodW H.S.τ.w xs *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0 := by
        rw [Finset.sum_comm]
      _ ≤ 4 ^ (κ.u + 1) * H.gamma := by
        simpa [M1] using hpeel
  have hsplit :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        prodW H.S.τ.w xs * Phi (T.S.E k) c
          (fun _ : Fin H.S.d => H.π.w) xs) = modSum + tailSum := by
    calc
      _ = ∑ xs : Fin κ.u → Fin (T.S.N k),
          ((if M2 xs then prodW H.S.τ.w xs *
            Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0) +
          (if ¬ M2 xs then prodW H.S.τ.w xs *
            Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0)) := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hM2 : M2 xs <;> simp [hM2]
      _ = modSum + tailSum := by
        simp [modSum, tailSum, Finset.sum_add_distrib]
  have htotalAbs :
      |∑ xs : Fin κ.u → Fin (T.S.N k),
        prodW H.S.τ.w xs * Phi (T.S.E k) c
          (fun _ : Fin H.S.d => H.π.w) xs| ≤
        (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
          4 ^ (κ.u + 1) * H.gamma := by
    rw [hsplit]
    calc
      |modSum + tailSum| ≤ |modSum| + |tailSum| := abs_add_le _ _
      _ ≤ (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
          4 ^ (κ.u + 1) * H.gamma := by
        exact add_le_add (by simpa [modSum, M2, H.homogeneous] using hmoderateSigned) hnonmodAbs
  have hmomentUpper :
      (∑ ys : Fin H.S.d → Fin (T.S.N k),
        (∏ l, H.π.w (ys l)) *
          (Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys - 1) ^ κ.u) ≤
        (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
          4 ^ (κ.u + 1) * H.gamma := by
    rw [hcenterEq]
    exact le_trans (le_abs_self _) htotalAbs
  let z (ys : Fin H.S.d → Fin (T.S.N k)) :=
    Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys
  let badProb := ∑ ys : Fin H.S.d → Fin (T.S.N k),
    if z ys < t then ∏ l, H.π.w (ys l) else 0
  let wp : ℝ := (1 - t) ^ κ.u
  have hwp : 0 < wp := pow_pos (by linarith) _
  have hpiProdNonneg (ys : Fin H.S.d → Fin (T.S.N k)) :
      0 ≤ ∏ l, H.π.w (ys l) := by
    apply Finset.prod_nonneg
    intro l hl
    exact H.π.nonneg (ys l)
  have hEvenPowNonneg (ys : Fin H.S.d → Fin (T.S.N k)) :
      0 ≤ (z ys - 1) ^ κ.u := hκ.u_rng.1.pow_nonneg _
  have hval (ys : Fin H.S.d → Fin (T.S.N k)) (hz : z ys < t) :
      wp ≤ |z ys - 1| ^ κ.u := by
    have hbase : 1 - t ≤ |z ys - 1| := by
      have hZlt1 : z ys < 1 := lt_trans hz ht1
      have hneg : z ys - 1 < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
    dsimp [wp]
    exact pow_le_pow_left₀ (by linarith [ht1]) hbase κ.u
  have hmomentLower : wp * badProb ≤
      (∑ ys : Fin H.S.d → Fin (T.S.N k),
        (∏ l, H.π.w (ys l)) * (z ys - 1) ^ κ.u) := by
    calc
      wp * badProb = ∑ ys : Fin H.S.d → Fin (T.S.N k),
          (if z ys < t then wp * ∏ l, H.π.w (ys l) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ys hys
        by_cases hz : z ys < t <;> simp [badProb, hz] <;> ring
      _ ≤ ∑ ys : Fin H.S.d → Fin (T.S.N k),
          (∏ l, H.π.w (ys l)) * (z ys - 1) ^ κ.u := by
        apply Finset.sum_le_sum
        intro ys hys
        by_cases hz : z ys < t
        · simp [hz]
          have hval' : wp ≤ (z ys - 1) ^ κ.u := by
            calc
              wp ≤ |z ys - 1| ^ κ.u := hval ys hz
              _ = (z ys - 1) ^ κ.u := hκ.u_rng.1.pow_abs _
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left hval' (hpiProdNonneg ys))
        · simp [hz]
          exact mul_nonneg (hpiProdNonneg ys) (hEvenPowNonneg ys)
  have hmassBound : wp * badProb ≤
      (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma := by
    exact le_trans hmomentLower (by simpa [z] using hmomentUpper)
  have hprobBound : badProb ≤ wp⁻¹ *
      ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma) := by
    calc
      badProb = wp⁻¹ * (wp * badProb) := by field_simp [ne_of_gt hwp] <;> ring
      _ ≤ wp⁻¹ *
          ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma) :=
        mul_le_mul_of_nonneg_left hmassBound (inv_nonneg.mpr hwp.le)
  have hwpInv : (1 - t) ^ (-(κ.u : ℝ)) = wp⁻¹ := by
    dsimp [wp]
    rw [Real.rpow_neg (by linarith [ht1]), Real.rpow_natCast]
  simpa [badProb, z, hwpInv] using hprobBound

/-- L12.5: package the extension, conflict, peeling, and lower-tail nodes. -/
structure HomogeneousPeelingResults (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) : Prop where
  extension_count : ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0,
      ∀ i₀ : Fin κ.u, ∀ xs : Fin κ.u → Fin (T.S.N k),
        (∀ i, i ≠ i₀ → xs i ∈ H.Sp) →
        ((H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
          i₀ ∈ J ∧ 2 ≤ J.card ∧
            κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)).card : ℝ) ≤
            Real.exp (Cstar κ.u κ.ξ * H.Q)
  conflict_count : ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0, ∀ x : Fin (T.S.N k),
      ((H.Sp.filter (fun z => κ.ξ < |corr (T.S.E k) c H.π.w x z|)).card : ℝ) ≤
        Real.exp (Cstar κ.u κ.ξ * H.Q)
  peeling : HomogeneousPeelingClaim κ hκ T c C0
  lower_tail : ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0, ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∑ ys : Fin H.S.d → Fin (T.S.N k),
        if Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys < t
        then ∏ l, H.π.w (ys l) else 0) ≤
          (1 - t) ^ (-(κ.u : ℝ)) *
            ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
              4 ^ (κ.u + 1) * H.gamma)

/-- L12.5: the public package assembled from its four theorem nodes. -/
theorem homogeneous_peeling_export (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    HomogeneousPeelingResults κ hκ T hDeep c C0 hC0 := by
  have hm := moderate_moment κ hκ T hDeep c C0 hC0
  have hp := homogeneous_peeling κ hκ T hDeep c C0 hC0 hm
  exact ⟨homogeneous_extension_count κ hκ T hDeep c C0 hC0,
    homogeneous_conflict_count κ hκ T hDeep c C0 hC0, hp,
    homogeneous_lower_tail κ hκ T hDeep c C0 hC0 hm hp⟩

end HypercubeRamsey.S12
