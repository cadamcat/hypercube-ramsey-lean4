import HypercubeRamsey.S08.L81.HiddenNodes
import HypercubeRamsey.S08.L81.SelectionNodes_q_s08_sel

/-!
# Lemma 8.1, Step 5: hidden-history conditioning and local selection

Source: `sections/08-…tex`, lines 178–225 (L8.1f).
-/

noncomputable section

namespace HypercubeRamsey.S08

open HypercubeRamsey.Lane_q_s08_sel
open Classical OAI.HypercubeRamsey
open scoped BigOperators
set_option maxHeartbeats 1000000

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1f(ii) (08:179–189): the hidden event at `g` reads the tuples in `B_grid(g, 2)` (gates at `g` and its
neighbours, the centre and anchor laws there, the references); two events meet only within grid distance four, at
most `(2s+1)^4` of them; by the gate tail and Markov on `E_{Θ_g} q_{g,k} ≤ ε₀` (independence of `Θ_g`),
`q_H ≤ e^{-n^{c'}} + (T+1)ε₀^{1/2} ≤ e^{-n^{c_H}}`, and `x_H = 2q_H` satisfies `q_H ≤ x_H(1-x_H)^{(2s+1)^4}`. -/
theorem hidden_lll (c' : ℝ) (hc' : 0 < c') (hη₀ : 0 < η₀) (hh : 1 ≤ h) :
    ∃ cH > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n →
      D.GateTail c' → D.DenTail → D.HiddenLLL (2 * Real.exp (-(D.n : ℝ) ^ cH)) := by
  sorry

/-- L8.1f(iii) (08:196–199): on incident ball counts at most `2λ`, the internal IDs of a candidate list are chosen
from at most `(n+1)(H+1) 2λ ≤ n^{13}` IDs (`≤ T` of them) and each of the `≤ 2s` cross IDs from at most `(H+1)2λ`,
so there are at most `exp(25(s+T) log n)` candidate lists; the constant does not depend on `h`. -/
theorem list_count (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.ListCount := by
  sorry

/-- L8.1f(iv) (08:208–212): a family has fewer than `n` lists of at most `T + 2s` IDs; an even site has at most
`(n - m + 1) + 2s` incident odd cells; so at most `n(n+1+2s)(T+2s) = o(λ)` IDs are forbidden at a site-level, and
at least `λ/2 - o(λ) ≥ λ/3` present IDs remain eligible. -/
theorem legal_of_counts (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.LegalOfCounts := by
  sorry

/-- L8.1f(v) (08:130–131, 212–214): on selection success, good heights select at every site (`¬ Bad` at the
selected level gives an active eligible ID); the ordinary neighbours of an odd cell lie within distance `D = 2`, so
their heights take at most two values and the crowd bound at one site per level gives at most `2n^b ≤ T` distinct
internal IDs; the realized list is a candidate list all of whose IDs are eligible where they are used, so it is
not bad (otherwise it meets a family list, whose IDs are forbidden there); legality follows from
`LegalOfCounts`. -/
theorem sel_conseq (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.LegalOfCounts → D.SelConseq := by
  sorry

/-- L8.1f(vi) (08:216–225): the selection at `(t, b)` consults eligibility in slice `t` at sites within `4H`
(the long rule), whose forbidden IDs come from the families at incident odd cells (keys within one of `t`), whose
lists read positions and tags of IDs within `r + 2` of those sites in slices within one of those keys, and `q_L`
reads hidden tuples within two of those keys; activations and ties are read only in slice `t`. -/
theorem sel_local (D : Ctx η₀ β p h) : D.SelLocal := by
  intro q q' e hΘ hLoc hAT
  let E := D.elig q.1.1 q.1.2 q.2.1.1 e.1
  let E' := D.elig q'.1.1 q'.1.2 q'.2.1.1 e.1
  unfold Ctx.sel
  apply selection_eq_of_local_data (hdP η₀ D.n) Finset.univ
    (q.1.2 e.1) (q'.1.2 e.1) (q.2.1.2 e.1) (q'.2.1.2 e.1)
    E E' (q.2.2 e.1) (q'.2.2 e.1) e.2 (Finset.mem_univ _)
  · intro v hv hdist
    have hsite : _root_.hammingDist v e.2 ≤ 4 * HH η₀ D.n := by
      simpa [HDParams.Rlong, hdP] using hdist
    have hp : ∀ k ∈ keyBall e.1 2, ∀ ℓ : D.Loc,
        _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
          q.1.2 k ℓ = q'.1.2 k ℓ := by
      intro k hk ℓ hℓ
      exact (hLoc k hk ℓ hℓ).1
    have ht : ∀ k ∈ keyBall e.1 2, ∀ ℓ : D.Loc,
        _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
          q.2.1.1 k ℓ = q'.2.1.1 k ℓ := by
      intro k hk ℓ hℓ
      exact (hLoc k hk ℓ hℓ).2
    have hE := elig_eq_of_local_inputs D q.1.1 q'.1.1 q.1.2 q'.1.2
      q.2.1.1 q'.2.1.1 e.1 v e.2 hsite hΘ hp ht
    funext j
    exact hE j
  · intro v hv j ℓ hℓ
    change ℓ ∈ D.elig q.1.1 q.1.2 q.2.1.1 e.1 v j at hℓ
    simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    rcases hℓ with ⟨_, _, hdist, _⟩
    exact hdist
  · intro ℓ hℓ
    have hkey : e.1 ∈ keyBall e.1 2 := by
      simp only [keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [keyDist]
    have hbound : _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
      have hbound' : _root_.hammingDist ℓ.1 e.2 ≤ 4 * HH η₀ D.n + rH D.n + 2 := by
        simpa [HDParams.Rlong, hdP] using hℓ
      omega
    exact (hLoc e.1 hkey ℓ hbound).1
  · intro ℓ hℓ
    have hbound : _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
      have hbound' : _root_.hammingDist ℓ.1 e.2 ≤ 4 * HH η₀ D.n + rH D.n + 2 := by
        simpa [HDParams.Rlong, hdP] using hℓ
      omega
    exact (hAT ℓ hbound).1
  · intro j
    exact (hAT (e.2, j) (by simp)).2

/-- L8.1f(vii) (08:211): prospective ball counts lie in `[λ/2, 2λ]` everywhere except with probability at most
`(ℓ+1)^s · 2 · 2^{n-m} (H+1) e^{-λ/12} ≤ e^{-n}` (`height_position_counts` in every slice). -/
theorem pos_tail (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n →
      D.preLaw.pr (fun q => ¬ D.PosOK q.1.2) ≤ Real.exp (-(D.n : ℝ)) := by
  obtain ⟨hσpos, hσζ, hζ1, _, _⟩ := (hd_admissible η₀ hη₀).hsz
  have hζpos : 0 < zetaH η₀ := lt_trans hσpos hσζ
  have hσ1 : sigmaH η₀ < 1 := lt_trans hσζ hζ1
  let a : ℝ := 1 - zetaH η₀
  have ha : 0 < a := by dsimp [a]; linarith
  let cVol : ℝ := (6 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ)
  have hpowTendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (10 : ℝ))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 10)).comp
      tendsto_natCast_atTop_atTop
  have hVolEventually : ∀ᶠ n : ℕ in Filter.atTop, cVol ≤ (n : ℝ) ^ (10 : ℝ) :=
    hpowTendsto.eventually (Filter.eventually_ge_atTop cVol)
  obtain ⟨nVol, hVol⟩ := Filter.eventually_atTop.1 hVolEventually
  let cLog : ℝ := ((4 / a) ^ 2)
  have hlogTendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (a / 2))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : (0 : ℝ) < a / 2)).comp
      tendsto_natCast_atTop_atTop
  have hLogEventually : ∀ᶠ n : ℕ in Filter.atTop, cLog ≤ (n : ℝ) ^ (a / 2) :=
    hlogTendsto.eventually (Filter.eventually_ge_atTop cLog)
  obtain ⟨nLog, hLog⟩ := Filter.eventually_atTop.1 hLogEventually
  refine ⟨max 8000 (max nVol nLog), ?_⟩
  intro D hn hGF
  have hn8000 : 8000 ≤ D.n := by omega
  have hnVol : nVol ≤ D.n := by omega
  have hnLog : nLog ≤ D.n := by omega
  have hn1 : 1 ≤ D.n := le_trans (by decide : 1 ≤ 8000) hn8000
  have hn2 : 2 ≤ D.n := by omega
  have hnR : (1 : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast hn1
  have hnR2 : (2 : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast hn2
  have hpowD : cVol ≤ (D.n : ℝ) ^ (10 : ℝ) := hVol D.n hnVol
  have hlogPow : cLog ≤ (D.n : ℝ) ^ (a / 2) := hLog D.n hnLog
  have hlogNonneg : 0 ≤ Real.log (D.n : ℝ) := Real.log_nonneg hnR
  have hlogBound : Real.log (D.n : ℝ) ≤
      ((D.n : ℝ) ^ (a / 4)) / (a / 4) :=
    Real.log_natCast_le_rpow_div D.n (by linarith)
  have hlogSq : (Real.log (D.n : ℝ)) ^ 2 ≤ (D.n : ℝ) ^ a := by
    have hsq : (Real.log (D.n : ℝ)) ^ 2 ≤
        (((D.n : ℝ) ^ (a / 4)) / (a / 4)) ^ 2 :=
          (sq_le_sq₀ hlogNonneg (by positivity)).2 hlogBound
    calc
      (Real.log (D.n : ℝ)) ^ 2 ≤
          (((D.n : ℝ) ^ (a / 4)) / (a / 4)) ^ 2 := hsq
      _ = cLog * (D.n : ℝ) ^ (a / 2) := by
        dsimp [cLog]
        calc
          (((D.n : ℝ) ^ (a / 4)) / (a / 4)) ^ 2 =
              ((D.n : ℝ) ^ (a / 4)) ^ 2 / (a / 4) ^ 2 := by rw [div_pow]
          _ = ((4 / a) ^ 2) * (D.n : ℝ) ^ (a / 2) := by
            have hpow : ((D.n : ℝ) ^ (a / 4)) ^ 2 = (D.n : ℝ) ^ (a / 2) := by
              calc
                ((D.n : ℝ) ^ (a / 4)) ^ 2 =
                    ((D.n : ℝ) ^ (a / 4)) ^ (2 : ℝ) :=
                      (Real.rpow_natCast ((D.n : ℝ) ^ (a / 4)) 2).symm
                _ = (D.n : ℝ) ^ ((a / 4) * 2) :=
                      (Real.rpow_mul (x := (D.n : ℝ)) (by positivity) (a / 4) 2).symm
                _ = (D.n : ℝ) ^ (a / 2) := by congr 1 <;> ring
            rw [hpow]
            have heps : (a / 4) ≠ 0 := ne_of_gt (by linarith)
            field_simp [heps]
      _ ≤ (D.n : ℝ) ^ (a / 2) * (D.n : ℝ) ^ (a / 2) :=
        mul_le_mul_of_nonneg_right hlogPow (Real.rpow_nonneg (by positivity) _)
      _ = (D.n : ℝ) ^ a := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < (D.n : ℝ))]
        congr 1 <;> ring
  have hceilLog :
      ⌈Real.log (D.n : ℝ) ^ 2⌉₊ ≤ ⌈(D.n : ℝ) ^ a⌉₊ :=
    Nat.ceil_le.mpr (hlogSq.trans (Nat.le_ceil ((D.n : ℝ) ^ a)))
  have hpowOne : (1 : ℝ) ≤ (D.n : ℝ) ^ a :=
    Real.one_le_rpow hnR (by linarith)
  have hceilOne : 1 ≤ ⌈(D.n : ℝ) ^ a⌉₊ := by
    exact_mod_cast (le_trans hpowOne (Nat.le_ceil ((D.n : ℝ) ^ a)))
  have hR0 : max 1 ⌈Real.log (D.n : ℝ) ^ 2⌉₊ ≤ ⌈(D.n : ℝ) ^ a⌉₊ :=
    max_le hceilOne hceilLog
  have htop := topScale_le_mul_target (D.n) (sigmaH η₀) (zetaH η₀)
    (by simpa [a] using hR0)
  have hpowσ : (D.n : ℝ) ^ sigmaH η₀ ≤ (D.n : ℝ) :=
    by simpa using Real.rpow_le_rpow_of_exponent_le hnR hσ1.le
  have hpowTarget : (D.n : ℝ) ^ a ≤ (D.n : ℝ) :=
    calc
      (D.n : ℝ) ^ a ≤ (D.n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by dsimp [a]; linarith [hζpos])
      _ = (D.n : ℝ) := Real.rpow_one _
  have hceilσ : ⌈(D.n : ℝ) ^ sigmaH η₀⌉₊ ≤ D.n := Nat.ceil_le.mpr hpowσ
  have hceilTarget : ⌈(D.n : ℝ) ^ a⌉₊ ≤ D.n := Nat.ceil_le.mpr hpowTarget
  have hM : max 2 ⌈(D.n : ℝ) ^ sigmaH η₀⌉₊ ≤ D.n := max_le (by omega) hceilσ
  have hHH : HH η₀ D.n ≤ D.n ^ 2 := by
    dsimp [HH]
    calc
      topScale D.n (sigmaH η₀) (zetaH η₀) ≤
          (max 2 ⌈(D.n : ℝ) ^ sigmaH η₀⌉₊) * ⌈(D.n : ℝ) ^ a⌉₊ := by
            simpa [a] using htop
      _ ≤ D.n * D.n := Nat.mul_le_mul hM hceilTarget
      _ = D.n ^ 2 := by ring
  have hHplus : (HH η₀ D.n + 1 : ℝ) ≤ 2 * (D.n : ℝ) ^ 2 := by
    have hNat : HH η₀ D.n + 1 ≤ 2 * D.n ^ 2 := by
      have hH' : HH η₀ D.n + 1 ≤ D.n ^ 2 + 1 := Nat.add_le_add_right hHH 1
      have hsq : 1 ≤ D.n ^ 2 := Nat.one_le_pow 2 D.n hn1
      omega
    exact_mod_cast hNat
  let pH := hdP η₀ D.n
  have hdimLow : (1 / 2 : ℝ) * (D.n : ℝ) ≤ (dC η₀ D.n : ℝ) := hGF.hd_ok.2.1
  have hdimHigh : (dC η₀ D.n : ℝ) ≤ (1 : ℝ) * D.n := hGF.hd_ok.2.2
  have hsplit := hGF.split
  have hmle : mC η₀ D.n ≤ D.n := by omega
  have hnR8000 : (8000 : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast hn8000
  have hd40 : 40 ≤ dC η₀ D.n := by
    have hr : (40 : ℝ) ≤ (dC η₀ D.n : ℝ) := by nlinarith [hdimLow, hnR8000]
    exact_mod_cast hr
  have hlinear : (1 / 200 : ℝ) * (dC η₀ D.n : ℝ) ≤ (rH D.n : ℝ) := by
    simpa [hdRegime, HDRegime.ok] using hGF.hd_ok.1.1
  have hr20 : 20 ≤ rH D.n := by
    have hr : (20 : ℝ) ≤ (rH D.n : ℝ) := by nlinarith [hlinear, hdimLow, hnR8000]
    exact_mod_cast hr
  have hchoose := choose20_lower hd40
  have hchooseLower :
      ((D.n : ℝ) / 6) ^ 20 / (Nat.factorial 20 : ℝ) ≤
        (Nat.choose (dC η₀ D.n) 20 : ℝ) := by
    have hbase : (D.n : ℝ) / 6 ≤ (dC η₀ D.n : ℝ) / 3 := by nlinarith [hdimLow]
    calc
      ((D.n : ℝ) / 6) ^ 20 / (Nat.factorial 20 : ℝ) ≤
          ((dC η₀ D.n : ℝ) / 3) ^ 20 / (Nat.factorial 20 : ℝ) := by
            exact div_le_div_of_nonneg_right
              (pow_le_pow_left₀ (by positivity) hbase 20) (by positivity)
      _ ≤ (Nat.choose (dC η₀ D.n) 20 : ℝ) := by
        convert hchoose using 1 <;> field_simp <;> ring
  have hpowLower : (D.n : ℝ) ^ (10 : ℝ) ≤
      ((D.n : ℝ) / 6) ^ 20 / (Nat.factorial 20 : ℝ) := by
    have hmul : (D.n : ℝ) ^ (10 : ℝ) * cVol ≤ (D.n : ℝ) ^ (20 : ℝ) := by
      calc
        (D.n : ℝ) ^ (10 : ℝ) * cVol ≤
            (D.n : ℝ) ^ (10 : ℝ) * (D.n : ℝ) ^ (10 : ℝ) :=
              mul_le_mul_of_nonneg_left hpowD (Real.rpow_nonneg (by positivity) _)
        _ = (D.n : ℝ) ^ (20 : ℝ) := by
              rw [← Real.rpow_add (by positivity : (0 : ℝ) < (D.n : ℝ))]
              congr 1 <;> ring
    have heq : ((D.n : ℝ) / 6) ^ 20 / (Nat.factorial 20 : ℝ) =
        (D.n : ℝ) ^ (20 : ℝ) / cVol := by
      dsimp [cVol]
      rw [div_pow]
      field_simp
      exact (Real.rpow_natCast (D.n : ℝ) 20).symm
    rw [heq]
    exact (le_div_iff₀ (by positivity : 0 < cVol)).2 (by simpa [mul_comm] using hmul)
  have hVlower : (D.n : ℝ) ^ (10 : ℝ) ≤ (pH.V : ℝ) := by
    have hsum : (Nat.choose (dC η₀ D.n) 20 : ℝ) ≤
        ∑ j ∈ Finset.range (rH D.n + 1), (Nat.choose (dC η₀ D.n) j : ℝ) := by
      calc
        (Nat.choose (dC η₀ D.n) 20 : ℝ) =
            ∑ j ∈ ({20} : Finset ℕ), (Nat.choose (dC η₀ D.n) j : ℝ) := by simp
        _ ≤ ∑ j ∈ Finset.range (rH D.n + 1),
            (Nat.choose (dC η₀ D.n) j : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.singleton_subset_iff.mpr
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hr20)))
            (by intro j hj hnot; positivity)
    calc
      _ ≤ (Nat.choose (dC η₀ D.n) 20 : ℝ) := hpowLower.trans hchooseLower
      _ ≤ _ := hsum
      _ = (pH.V : ℝ) := by simp [pH, HDParams.V, hdP]
  have hVNat : 0 < pH.V := by
    have hnpositive : (0 : ℝ) < (D.n : ℝ) ^ (10 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < D.n)) _
    exact_mod_cast lt_of_lt_of_le hnpositive hVlower
  have hVReal : (0 : ℝ) < (pH.V : ℝ) := by exact_mod_cast hVNat
  have hlam : 0 < pH.lam := by simp [pH, hdP]; positivity
  have hprob : pH.lam / (pH.V : ℝ) ≤ 1 := by
    apply (div_le_one hVReal).2
    simpa [pH, hdP] using hVlower
  have hr : pH.r ≤ pH.d := by
    have hr4 : 4 * rH D.n ≤ dC η₀ D.n := by
      simpa [hdRegime, HDRegime.ok] using hGF.hd_ok.1.2
    dsimp [pH, hdP]
    omega
  let SliceBad : (pH.Loc → Bool) → Prop := fun P =>
    ∃ b : CubeVertex pH.d, ∃ j : Fin (pH.H + 1),
      let count := (Finset.univ.filter fun u : CubeVertex pH.d =>
        P (u, j) = true ∧ _root_.hammingDist u b ≤ pH.r).card
      (count : ℝ) < pH.lam / 2 ∨ 2 * pH.lam < (count : ℝ)
  have hSliceTail : pH.posLaw.pr SliceBad ≤
      2 * ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) *
        ((pH.H + 1 : ℕ) : ℝ) * Real.exp (-pH.lam / 12) := by
    have hcounts := _root_.HypercubeRamsey.height_position_counts pH
      (Finset.univ : Finset (CubeVertex pH.d)) hlam hVNat hr hprob
    simpa [SliceBad] using hcounts
  have hMarg (g : D.KeyT) :
      D.posLaw.pr (fun P => SliceBad (P g)) = pH.posLaw.pr SliceBad := by
    calc
      D.posLaw.pr (fun P => SliceBad (P g)) =
          D.posLaw.expect (prIndicator (fun P => SliceBad (P g))) :=
            pr_eq_expect_indicator D.posLaw (fun P => SliceBad (P g))
      _ = pH.posLaw.expect (prIndicator SliceBad) := by
            calc
              D.posLaw.expect (prIndicator (fun P => SliceBad (P g))) =
                  D.posLaw.expect (fun P => prIndicator SliceBad (P g)) := by
                    congr 1
              _ = pH.posLaw.expect (prIndicator SliceBad) := by
                    simpa [Ctx.posLaw, pH] using
                      pi_expect_coordinate pH.posLaw g (prIndicator SliceBad)
      _ = pH.posLaw.pr SliceBad := (pr_eq_expect_indicator pH.posLaw SliceBad).symm
  have hEvent (P : D.Pos) : ¬ D.PosOK P ↔ ∃ g, SliceBad (P g) := by
    unfold Ctx.PosOK
    constructor
    · intro h
      push_neg at h
      rcases h with ⟨g, b, j, hfail⟩
      refine ⟨g, b, j, ?_⟩
      dsimp [SliceBad]
      by_cases hlow : pH.lam / 2 ≤ (D.ballCount P g b j : ℝ)
      · right
        simpa [Ctx.ballCount, pH] using hfail hlow
      · left
        simpa [Ctx.ballCount, pH] using (lt_of_not_ge hlow)
    · rintro ⟨g, b, j, hfail⟩ hOK
      have hAt := hOK g b j
      dsimp [SliceBad] at hfail
      rcases hfail with hlow | hhigh
      · have hlow' : (D.ballCount P g b j : ℝ) < pH.lam / 2 := by
          simpa [Ctx.ballCount, pH] using hlow
        exact (not_lt_of_ge hAt.1) hlow'
      · have hhigh' : 2 * pH.lam < (D.ballCount P g b j : ℝ) := by
          simpa [Ctx.ballCount, pH] using hhigh
        exact (not_lt_of_ge hAt.2) hhigh'
  have hUnion : D.posLaw.pr (fun P => ¬ D.PosOK P) ≤
      (Fintype.card D.KeyT : ℝ) *
        (2 * ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) *
          ((pH.H + 1 : ℕ) : ℝ) * Real.exp (-pH.lam / 12)) := by
    have heq : (fun P => ¬ D.PosOK P) = (fun P => ∃ g, SliceBad (P g)) := by
      funext P
      exact propext (hEvent P)
    rw [heq]
    calc
      _ ≤ ∑ g : D.KeyT, D.posLaw.pr (fun P => SliceBad (P g)) :=
        pr_exists_le_sum D.posLaw (fun g P => SliceBad (P g))
      _ ≤ ∑ _g : D.KeyT,
          2 * ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) *
            ((pH.H + 1 : ℕ) : ℝ) * Real.exp (-pH.lam / 12) :=
            Finset.sum_le_sum fun g hg => by
              calc
                D.posLaw.pr (fun P => SliceBad (P g)) = pH.posLaw.pr SliceBad := hMarg g
                _ ≤ _ := hSliceTail
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hPrePos : D.preLaw.pr (fun q => ¬ D.PosOK q.1.2) =
      D.posLaw.pr (fun P => ¬ D.PosOK P) := by
    calc
      _ = D.preLaw.expect (fun q => prIndicator (fun q => ¬ D.PosOK q.1.2) q) :=
        pr_eq_expect_indicator D.preLaw (fun q => ¬ D.PosOK q.1.2)
      _ = D.posLaw.expect (prIndicator (fun P => ¬ D.PosOK P)) :=
        preLaw_expect_pos D (prIndicator (fun P => ¬ D.PosOK P))
      _ = _ := (pr_eq_expect_indicator D.posLaw (fun P => ¬ D.PosOK P)).symm
  have hKeyCard : (Fintype.card D.KeyT : ℝ) ≤ (2 : ℝ) ^ D.n := by
    have hCard : Fintype.card D.KeyT = (lC D.n + 1) ^ sC η₀ D.n := by
      simp [Ctx.KeyT, Key]
    have hl : lC D.n + 1 ≤ 2 ^ lC D.n := by
      simpa using Nat.choose_succ_le_two_pow (lC D.n) 1
    have hNat : Fintype.card D.KeyT ≤ 2 ^ D.n := by
      rw [hCard]
      calc
        (lC D.n + 1) ^ sC η₀ D.n ≤ (2 ^ lC D.n) ^ sC η₀ D.n :=
          Nat.pow_le_pow_left hl _
        _ = 2 ^ (lC D.n * sC η₀ D.n) := by rw [Nat.pow_mul]
        _ = 2 ^ mC η₀ D.n := by simp [mC, Nat.mul_comm]
        _ ≤ 2 ^ D.n := Nat.pow_le_pow_right (by decide) hmle
    exact_mod_cast hNat
  have hSiteCard :
      ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) ≤ (2 : ℝ) ^ D.n := by
    have hdimNat : dC η₀ D.n ≤ D.n := by
      unfold dC
      omega
    have hcard : Fintype.card (CubeVertex pH.d) = 2 ^ pH.d := by
      simp [CubeVertex, Fintype.card_fun]
    have hNat : Fintype.card (CubeVertex pH.d) ≤ 2 ^ D.n := by
      rw [hcard]
      exact Nat.pow_le_pow_right (by decide) (by simpa [pH, hdP] using hdimNat)
    exact_mod_cast (by simpa using hNat)
  have hHplus : ((pH.H + 1 : ℕ) : ℝ) ≤ 2 * (D.n : ℝ) ^ 2 := by
    have hNat : pH.H + 1 ≤ 2 * D.n ^ 2 := by
      change HH η₀ D.n + 1 ≤ 2 * D.n ^ 2
      have hH' : HH η₀ D.n + 1 ≤ D.n ^ 2 + 1 := Nat.add_le_add_right hHH 1
      have hsq : 1 ≤ D.n ^ 2 := Nat.one_le_pow 2 D.n hn1
      omega
    exact_mod_cast hNat
  have hExpoPref :
      (Fintype.card D.KeyT : ℝ) *
        (2 * ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) *
          ((pH.H + 1 : ℕ) : ℝ) * Real.exp (-pH.lam / 12)) ≤
        4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 * Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) := by
    have hLam : pH.lam = (D.n : ℝ) ^ (10 : ℝ) := by rfl
    have hpow4 : (2 : ℝ) ^ D.n * (2 : ℝ) ^ D.n = (4 : ℝ) ^ D.n := by
      calc
        (2 : ℝ) ^ D.n * (2 : ℝ) ^ D.n = ((2 : ℝ) * 2) ^ D.n := by rw [← mul_pow]
        _ = (4 : ℝ) ^ D.n := by norm_num
    rw [hLam]
    calc
      _ ≤ (2 : ℝ) ^ D.n *
          (2 * (2 : ℝ) ^ D.n * (2 * (D.n : ℝ) ^ 2) *
            Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12)) := by
              gcongr <;> positivity
      _ = _ := by
        calc
          (2 : ℝ) ^ D.n *
              (2 * (2 : ℝ) ^ D.n * (2 * (D.n : ℝ) ^ 2) *
                Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12)) =
              4 * ((2 : ℝ) ^ D.n * (2 : ℝ) ^ D.n) * (D.n : ℝ) ^ 2 *
                Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) := by ring
          _ = 4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 *
                Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) := by rw [hpow4]
  have hExpOne : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hExpTwo : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) hExpOne 2
      _ = Real.exp 1 * Real.exp 1 := by ring
      _ = Real.exp (1 + 1) := (Real.exp_add 1 1).symm
      _ = Real.exp 2 := by congr 1; norm_num
  have hExpNat : ∀ (x : ℝ) (k : ℕ), Real.exp x ^ k = Real.exp ((k : ℝ) * x) := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          Real.exp x ^ (k + 1) = Real.exp x ^ k * Real.exp x := by rw [pow_succ]
          _ = Real.exp ((k : ℝ) * x) * Real.exp x := by rw [ih]
          _ = Real.exp ((k : ℝ) * x + x) := (Real.exp_add _ _).symm
          _ = Real.exp (((k + 1 : ℕ) : ℝ) * x) := by
            congr 1
            norm_num [Nat.cast_succ]
            ring
  have hFourPow : (4 : ℝ) ^ D.n ≤ Real.exp (2 * D.n) := by
    calc
      (4 : ℝ) ^ D.n ≤ (Real.exp 2) ^ D.n := pow_le_pow_left₀ (by norm_num) hExpTwo _
      _ = Real.exp (2 * (D.n : ℝ)) := by simpa [mul_comm] using hExpNat 2 D.n
  have hNExp : (D.n : ℝ) ^ 2 ≤ Real.exp (2 * D.n) := by
    have hNle : (D.n : ℝ) ≤ Real.exp (D.n : ℝ) := by
      have h := Real.add_one_le_exp (D.n : ℝ)
      linarith
    calc
      (D.n : ℝ) ^ 2 ≤ (Real.exp (D.n : ℝ)) ^ 2 := by gcongr
      _ = Real.exp (2 * (D.n : ℝ)) := by
        calc
          (Real.exp (D.n : ℝ)) ^ 2 = Real.exp (D.n : ℝ) * Real.exp (D.n : ℝ) := by ring
          _ = Real.exp ((D.n : ℝ) + D.n) := (Real.exp_add _ _).symm
          _ = Real.exp (2 * (D.n : ℝ)) := by congr 1 <;> ring
  have hPrefExp : 4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 ≤ Real.exp (4 * D.n + 2) := by
    calc
      4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 ≤
          Real.exp 2 * Real.exp (2 * D.n) * Real.exp (2 * D.n) := by
            gcongr
      _ = (Real.exp 2 * Real.exp (2 * D.n)) * Real.exp (2 * D.n) := by ring
      _ = Real.exp (2 + 2 * D.n) * Real.exp (2 * D.n) := by
        rw [(Real.exp_add 2 (2 * D.n)).symm]
      _ = Real.exp ((2 + 2 * D.n) + 2 * D.n) := (Real.exp_add _ _).symm
      _ = Real.exp (4 * D.n + 2) := by congr 1 <;> ring
  have hn10 : 5 * (D.n : ℝ) + 2 ≤ (D.n : ℝ) ^ (10 : ℝ) / 12 := by
    have hnNat : 10 ≤ D.n := by omega
    have hpowNat : (10 : ℕ) ^ 9 ≤ D.n ^ 9 := Nat.pow_le_pow_left hnNat _
    have hpow9 : (72 : ℝ) ≤ (D.n : ℝ) ^ (9 : ℕ) := by
      have hcast : (10 : ℝ) ^ (9 : ℕ) ≤ (D.n : ℝ) ^ (9 : ℕ) := by exact_mod_cast hpowNat
      have hten : (72 : ℝ) ≤ (10 : ℝ) ^ (9 : ℕ) := by norm_num
      exact hten.trans hcast
    have hnreal : (0 : ℝ) ≤ (D.n : ℝ) := by positivity
    have hpow10 : 72 * (D.n : ℝ) ≤ (D.n : ℝ) ^ (10 : ℝ) := by
      have hpow10Nat : 72 * (D.n : ℝ) ≤ (D.n : ℝ) ^ (10 : ℕ) := by
        calc
          72 * (D.n : ℝ) ≤ (D.n : ℝ) ^ (9 : ℕ) * (D.n : ℝ) :=
            mul_le_mul_of_nonneg_right hpow9 hnreal
          _ = (D.n : ℝ) ^ (10 : ℕ) := by
            rw [show (10 : ℕ) = 9 + 1 by norm_num]
            exact (pow_succ (D.n : ℝ) 9).symm
      calc
        72 * (D.n : ℝ) ≤ (D.n : ℝ) ^ (10 : ℕ) := hpow10Nat
        _ = (D.n : ℝ) ^ (10 : ℝ) := (Real.rpow_natCast (D.n : ℝ) 10).symm
    have hmul : 12 * (5 * (D.n : ℝ) + 2) ≤ 72 * (D.n : ℝ) := by nlinarith [hnR2]
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 12)).2
      (by simpa [mul_comm] using hmul.trans hpow10)
  have hExpAbsorb : 4 * D.n + 2 - (D.n : ℝ) ^ (10 : ℝ) / 12 ≤ -(D.n : ℝ) := by
    linarith [hn10]
  have hFinal :
      4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 *
          Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) ≤ Real.exp (-(D.n : ℝ)) := by
    calc
      _ ≤ Real.exp (4 * D.n + 2) *
          Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) :=
            mul_le_mul_of_nonneg_right hPrefExp (Real.exp_nonneg _)
      _ = Real.exp (4 * D.n + 2 - (D.n : ℝ) ^ (10 : ℝ) / 12) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      _ ≤ Real.exp (-(D.n : ℝ)) := Real.exp_le_exp.mpr hExpAbsorb
  exact hPrePos ▸ hUnion.trans (hExpoPref.trans hFinal)

/-- L8.1f(viii) (08:191–195): the tags of a candidate list's distinct IDs are independent with laws `S_g`
(internal) and `S_u` (cross), so `E_t q_L = q_{g,k}` with `k ≤ T` internal IDs (`Mden` does not depend on how the
internal observations are indexed); at a hidden history avoiding the hidden events `q_{g,k} ≤ ε₀^{1/2}`, and
Markov gives `Pr(q_L > ε₀^{1/4}) ≤ ε₀^{1/4}`. -/
theorem bad_list_prob (D : Ctx η₀ β p h) : D.BadListProb := by
  sorry

/-- L8.1f(ix) (08:200–206): lists with disjoint ID sets have independent tags, so `n` disjoint bad lists at a cell
have probability at most `L_n^n ε₀^{n/4} = exp(n[25(s+T) - δhs/4] log n)` (`BadListProb`, `ListCount`), which for
`h ≥ 10⁸` beats the `exp(O(n + s log n))` cells. -/
theorem few_bad_tail (hη₀ : 0 < η₀) (hh : 10 ^ 8 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.ListCount → D.BadListProb →
      0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g) →
      D.preLaw.pr (fun q => D.PosOK q.1.2 ∧ ¬ D.FewBad q.1.1 q.1.2 q.2.1.1) ≤ Real.exp (-(D.n : ℝ)) := by
  sorry

/-- L8.1f(x) (08:214): eligibility in slice `g` is a function of the positions and of auxiliary randomness
independent of the activations of slice `g` (other slices' positions, tags); on legality (from `PosOK ∧ FewBad`)
Lemma 3.8 (`height_selection_global`, with `hd_admissible` and the linear regime) bounds the failure of good
heights in a slice by `e^{-n^{1+c}}`; a union over the `exp(O(s log n))` slices gives `e^{-n}`. -/
theorem height_tail (hη₀ : 0 < η₀)
    (hadm : HDAdmissible 10 (b0H η₀) (bH η₀) (sigmaH η₀) (zetaH η₀) (thetaH η₀) (aH η₀) (1 / 2) 1 2) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.LegalOfCounts →
      D.preLaw.pr (fun q => D.PosOK q.1.2 ∧ D.FewBad q.1.1 q.1.2 q.2.1.1 ∧
        ¬ D.GoodH q.1.1 q.1.2 q.2.1.1 q.2.1.2) ≤ Real.exp (-(D.n : ℝ)) := by
  sorry

end Nodes

end HypercubeRamsey.S08
