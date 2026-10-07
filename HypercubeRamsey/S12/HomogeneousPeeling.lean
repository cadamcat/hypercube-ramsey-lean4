import HypercubeRamsey.S12.ModerateMoment
import HypercubeRamsey.S12.CenteredMoment
import HypercubeRamsey.S12.HomogeneousPeeling_q_s12_peel
import HypercubeRamsey.S12.FiniteRamsey_q_s12_peel

/-!
# Section 12 homogeneous extension counts and peeling
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter
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

/-- L12.5(iii): large-interaction tuples have bounded total positive-term mass. -/
theorem homogeneous_peeling (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hModerate : ModerateMomentClaim κ T c C0) :
    HomogeneousPeelingClaim κ hκ T c C0 := by
  sorry

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
