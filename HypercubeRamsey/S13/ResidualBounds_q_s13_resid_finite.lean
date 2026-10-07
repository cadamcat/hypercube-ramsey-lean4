import HypercubeRamsey.S13.ResidualBounds_q_s13_resid

namespace HypercubeRamsey.Lane_q_s13_resid_finite

open HypercubeRamsey
open Filter
open Classical
open scoped BigOperators

/-- The finite-grid hypothesis, duplicated so this lane helper has no import cycle. -/
def ClusterAbsenceInputAux (κ : CConsts) (T : Stage) : Prop :=
  ∀ (ζ δ : ℚ), 0 < ζ → 0 < δ →
    (δ : ℝ) < min κ.η0 (min (ζ : ℝ) 1) / 2000 →
    ∀ (c : Colour) (o : Bool),
      ∀ᶠ k in atTop, ¬ ClusterWitnessAt (T.orient o) k c ζ δ

private theorem cluster_b_le_two_n (κ : CConsts) (S : Stage) (k : ℕ)
    (RX RY : Finset (Fin (S.S.N k))) (b : ℕ) (o : Bool)
    (hClu : CluScaleWitness κ S k RX RY b o) :
    (b : ℝ) ≤ 2 * (S.S.n k : ℝ) := by
  rcases hClu with ⟨U, hU, m, B, hUs, hBs, hdisj, hBins, hUcard, hVcard, hcorr⟩
  let V := Finset.univ.biUnion B
  have hNpos : (0 : ℝ) < S.S.N k := by exact_mod_cast S.S.N_pos k
  have hVpos : 0 < (V.card : ℝ) := by
    apply lt_of_lt_of_le (mul_pos hNpos (Real.exp_pos _))
    simpa [V] using hVcard
  have hVne : V.Nonempty := by
    exact Finset.card_pos.mp (by exact_mod_cast hVpos)
  obtain ⟨y, hy⟩ := hVne
  have hy' : y ∈ Finset.univ.biUnion B := by simpa [V] using hy
  rcases Finset.mem_biUnion.mp hy' with ⟨j, hj, hyj⟩
  have hBcard : (B j).card ≤ S.S.N k := by
    simpa using Finset.card_le_card (Finset.subset_univ (B j))
  have hexp : Real.exp (b : ℝ) ≤ (S.S.N k : ℝ) :=
    le_trans (hBins j) (by exact_mod_cast hBcard)
  have hlog : (b : ℝ) ≤ Real.log (S.S.N k : ℝ) := by
    calc
      (b : ℝ) = Real.log (Real.exp (b : ℝ)) := by rw [Real.log_exp]
      _ ≤ Real.log (S.S.N k : ℝ) := Real.log_le_log (Real.exp_pos _) hexp
  have hNupper : (S.S.N k : ℝ) ≤
      (S.S.n k : ℝ) * (2 : ℝ) ^ (S.S.n k) := by
    exact_mod_cast S.S.N_le k
  have hlogupper : Real.log (S.S.N k : ℝ) ≤ 2 * (S.S.n k : ℝ) := by
    have hlogN := Real.log_le_log hNpos hNupper
    have hnpos : (0 : ℝ) < S.S.n k := by
      have hnNat : 0 < S.S.n k := by
        by_contra hnot
        have heq : S.S.n k = 0 := Nat.eq_zero_of_not_pos hnot
        have hbound := S.S.N_le k
        rw [heq] at hbound
        simp at hbound
        have hpos := S.S.N_pos k
        omega
      exact_mod_cast hnNat
    rw [Real.log_mul (ne_of_gt hnpos)
      (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), Real.log_pow] at hlogN
    have hlogn : Real.log (S.S.n k : ℝ) ≤ (S.S.n k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hnpos
    have hlog2 : Real.log 2 ≤ 1 := by nlinarith [Real.log_two_lt_d9]
    nlinarith
  exact hlog.trans hlogupper

theorem initial_scale_bound (κ : CConsts) (T : Stage) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
        CluScaleWitness κ T k RX RY b o →
          (b : ℝ) < (T.S.n k : ℝ) ^ (2 : ℝ) := by
  have hn3 : ∀ᶠ k in atTop, 3 ≤ (T.S.n k : ℝ) := by
    have htend : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        T.S.n_tendsto
    exact htend.eventually (eventually_ge_atTop (3 : ℝ))
  filter_upwards [hn3] with k hn
  intro RX RY hRX hRY b o hb hClu
  have hscale := cluster_b_le_two_n κ T k RX RY b o hClu
  have hpower : (T.S.n k : ℝ) ^ (2 : ℝ) = (T.S.n k : ℝ) ^ (2 : ℕ) := by
    exact Real.rpow_natCast (T.S.n k : ℝ) 2
  have hquad : 2 * (T.S.n k : ℝ) < (T.S.n k : ℝ) ^ (2 : ℕ) := by
    nlinarith [hn]
  rw [hpower]
  linarith

def gridExponent : ℕ → ℚ
  | 0 => 2
  | j + 1 => gridExponent j / 10

theorem gridExponent_succ (j : ℕ) : gridExponent (j + 1) = gridExponent j / 10 := rfl

theorem gridExponent_range (j : ℕ) : 0 < gridExponent j ∧ gridExponent j ≤ 2 := by
  induction j with
  | zero => norm_num [gridExponent]
  | succ j ih =>
      constructor
      · simpa [gridExponent] using div_pos ih.1 (by norm_num : (0 : ℚ) < 10)
      · have hdiv : gridExponent j / 10 ≤ gridExponent j := by
          have hpos := ih.1
          nlinarith
        exact le_trans hdiv ih.2

theorem gridExponent_cast (j : ℕ) :
    (gridExponent j : ℝ) = 2 * (1 / 10 : ℝ) ^ j := by
  induction j with
  | zero => norm_num [gridExponent]
  | succ j ih =>
      simp [gridExponent, ih, pow_succ]
      ring

end HypercubeRamsey.Lane_q_s13_resid_finite
