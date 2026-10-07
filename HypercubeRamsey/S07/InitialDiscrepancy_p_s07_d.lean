import HypercubeRamsey.S07.SmallGridPurity
import HypercubeRamsey.S07.Needs
import HypercubeRamsey.S03.Mixtures

namespace HypercubeRamsey.S07

open Filter

/-- Restrict a pure pair to the labels on which its majority colour has high degree. -/
theorem purity_to_grid_purity_p_s07_d (β h : ℝ) (hβ : 0 < β) (hh : 0 < h) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ κ : ℝ, 0 < κ → ∀ N : ℕ,
      ∀ E : Fin N → Fin N → Prop, ∀ X Y : Finset (Fin N),
        AvailableAt κ (PPure β β h).toPatch n N E X Y →
        ∃ G : Colour, AvailableAt (κ / 2) (PGridPure G (4 * β) (h / 2)).toPatch n N E X Y := by
  classical
  let low : Colour → PairProp := fun G n N E μ ν =>
    μ.WidthLE (2 * (n : ℝ) ^ β) ∧ ν.WidthLE (2 * (n : ℝ) ^ β) ∧
      dens E (!G) μ ν ≤ Real.exp (-((n : ℝ) ^ h))
  have hUnion : (PPure β β h).toPatch =
      fun n N E => (low false).toPatch n N E ∪ (low true).toPatch n N E := by
    funext n N E
    ext AB
    change
      (∃ μ ν : Law N, μ.SupportedIn AB.1 ∧ ν.SupportedIn AB.2 ∧
        PPure β β h n N E μ ν) ↔
      ((∃ μ ν : Law N, μ.SupportedIn AB.1 ∧ ν.SupportedIn AB.2 ∧
          low false n N E μ ν) ∨
        ∃ μ ν : Law N, μ.SupportedIn AB.1 ∧ ν.SupportedIn AB.2 ∧
          low true n N E μ ν)
    constructor
    · rintro ⟨μ, ν, hμA, hνB, hPure⟩
      rcases hPure with ⟨hμw, hνw, c, hdefect⟩
      cases c
      · exact Or.inl ⟨μ, ν, hμA, hνB, hμw, hνw, by simpa using hdefect⟩
      · exact Or.inr ⟨μ, ν, hμA, hνB, hμw, hνw, by simpa using hdefect⟩
    · rintro (⟨μ, ν, hμA, hνB, hμw, hνw, hdefect⟩ |
        ⟨μ, ν, hμA, hνB, hμw, hνw, hdefect⟩)
      · exact ⟨μ, ν, hμA, hνB, ⟨hμw, hνw, false, by simpa using hdefect⟩⟩
      · exact ⟨μ, ν, hμA, hνB, ⟨hμw, hνw, true, by simpa using hdefect⟩⟩
  have hhalf : 0 < h / 2 := by positivity
  have hbetaGap : 0 < β := hβ
  have hgridBeta : (4 * β) / 2 = 2 * β := by ring
  have htend (a : ℝ) (ha : 0 < a) :
      Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hbetaEvent : ∀ᶠ n : ℕ in atTop, 4 ≤ (n : ℝ) ^ β :=
    (htend β hbetaGap).eventually (eventually_ge_atTop (4 : ℝ))
  have hhalfEvent : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (h / 2) :=
    (htend (h / 2) hhalf).eventually (eventually_ge_atTop (2 : ℝ))
  have hnEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact_mod_cast hn
  have hLargeN : ∀ᶠ n : ℕ in atTop,
      1 ≤ (n : ℝ) ∧ 4 ≤ (n : ℝ) ^ β ∧ 2 ≤ (n : ℝ) ^ (h / 2) := by
    filter_upwards [hnEvent, hbetaEvent, hhalfEvent] with n hn hβn hhn
    exact ⟨hn, hβn, hhn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hLargeN
  refine ⟨n₀, ?_⟩
  have hTrimColor : ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
      n₀ ≤ n → ∀ G : Colour,
        AvailableAt (κ / 2) (low G).toPatch n N E X Y →
        AvailableAt (κ / 2) (PGridPure G (4 * β) (h / 2)).toPatch n N E X Y := by
    intro n N E X Y hn G hAvail RX RY hRX hRY
    have hLarge := hn₀ n hn
    have hnR : 1 ≤ (n : ℝ) := hLarge.1
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
    have hnβ : 1 ≤ (n : ℝ) ^ β := Real.one_le_rpow hnR hβ.le
    have hβpow : (n : ℝ) ^ (2 * β) = (n : ℝ) ^ β * (n : ℝ) ^ β := by
      calc
        (n : ℝ) ^ (2 * β) = (n : ℝ) ^ (β + β) := by congr 1 <;> ring
        _ = (n : ℝ) ^ β * (n : ℝ) ^ β := Real.rpow_add hnpos _ _
    have hβsquare : 4 * (n : ℝ) ^ β ≤ (n : ℝ) ^ (2 * β) := by
      rw [hβpow]
      exact mul_le_mul_of_nonneg_left (hLarge.2.1) (Real.rpow_nonneg (le_of_lt hnpos) β)
    have hβexp : 2 * (n : ℝ) ^ β + Real.log 2 ≤ (n : ℝ) ^ (2 * β) := by
      have hlog : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9
        linarith
      linarith [hβsquare, hnβ]
    let δ : ℝ := Real.exp (-((n : ℝ) ^ (h / 2)))
    have hδpos : 0 < δ := by positivity
    obtain ⟨A, B, hAB, hAX, hBY⟩ := hAvail RX RY hRX hRY
    rcases hAB with ⟨μ, ν, hμA, hνB, hLow⟩
    rcases hLow with ⟨hμwidth, hνwidth, hdefect⟩
    have hNpos : 0 < N := by
      by_contra hN
      have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      have hsum := μ.sum_eq_one
      norm_num at hsum
    let bad : Finset (Fin N) := Finset.univ.filter
      (fun y => colDeg E G μ y < 1 - δ)
    let good : Finset (Fin N) := Finset.univ \ bad
    have hdensCol (c : Colour) :
        dens E c μ ν = ∑ y, ν.w y * colDeg E c μ y := by
      unfold dens colDeg
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    have hcolComplement (y : Fin N) :
        colDeg E G μ y + colDeg E (!G) μ y = 1 := by
      unfold colDeg
      rw [← Finset.sum_add_distrib]
      calc
        (∑ x, (μ.w x * (if Hits E G x y then 1 else 0) +
            μ.w x * (if Hits E (!G) x y then 1 else 0))) = ∑ x, μ.w x := by
          apply Finset.sum_congr rfl
          intro x hx
          cases G <;> by_cases hE : E x y <;> simp [Hits, hE]
        _ = 1 := μ.sum_eq_one
    have hcolNonneg (c : Colour) (y : Fin N) : 0 ≤ colDeg E c μ y := by
      unfold colDeg
      apply Finset.sum_nonneg
      intro x hx
      split_ifs <;> exact mul_nonneg (μ.nonneg x) (by positivity)
    have hbadDegree (y : Fin N) (hy : y ∈ bad) :
        δ ≤ colDeg E (!G) μ y := by
      have hy' := (Finset.mem_filter.mp hy).2
      have hdegree := hcolComplement y
      linarith
    have hbadMarkov : δ * (∑ y ∈ bad, ν.w y) ≤ Real.exp (-((n : ℝ) ^ h)) := by
      calc
        δ * (∑ y ∈ bad, ν.w y) = ∑ y ∈ bad, ν.w y * δ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ ≤ ∑ y ∈ bad, ν.w y * colDeg E (!G) μ y := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (hbadDegree y hy) (ν.nonneg y)
        _ ≤ ∑ y, ν.w y * colDeg E (!G) μ y := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bad)
            (by intro y hy hnot; exact mul_nonneg (ν.nonneg y) (hcolNonneg (!G) y))
        _ = dens E (!G) μ ν := (hdensCol (!G)).symm
        _ ≤ Real.exp (-((n : ℝ) ^ h)) := hdefect
    let t : ℝ := (n : ℝ) ^ (h / 2)
    have ht : 2 ≤ t := hLarge.2.2
    have hpower : (n : ℝ) ^ h = t * t := by
      dsimp [t]
      calc
        (n : ℝ) ^ h = (n : ℝ) ^ (h / 2 + h / 2) := by congr 1 <;> ring
        _ = (n : ℝ) ^ (h / 2) * (n : ℝ) ^ (h / 2) := Real.rpow_add hnpos _ _
    have hgapExp : 2 ≤ (n : ℝ) ^ h - t := by
      rw [hpower]
      have hprod : 0 ≤ (t - 2) * (t + 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hExpHalf : Real.exp (-2 : ℝ) < 1 / 2 := by
      have hExpTwo : 2 < Real.exp (2 : ℝ) := by
        have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
        linarith
      rw [Real.exp_neg]
      exact (inv_lt_iff_one_lt_mul₀' (Real.exp_pos (2 : ℝ))).2 (by nlinarith)
    have hratio : Real.exp (-((n : ℝ) ^ h)) / δ = Real.exp (-((n : ℝ) ^ h) + t) := by
      dsimp [δ, t]
      rw [← Real.exp_sub]
      congr 1
      ring
    have hbadMass : (∑ y ∈ bad, ν.w y) ≤ 1 / 2 := by
      have hdiv : (∑ y ∈ bad, ν.w y) ≤ Real.exp (-((n : ℝ) ^ h)) / δ :=
        (le_div_iff₀ hδpos).2 (by simpa [mul_comm] using hbadMarkov)
      calc
        (∑ y ∈ bad, ν.w y) ≤ Real.exp (-((n : ℝ) ^ h)) / δ := hdiv
        _ = Real.exp (-((n : ℝ) ^ h) + t) := hratio
        _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 1 / 2 := hExpHalf.le
    have hdisj : Disjoint good bad := disjoint_sdiff_self_left
    have hunion : good ∪ bad = Finset.univ := by simp [good]
    let mass : ℝ := ∑ y ∈ good, ν.w y
    have hmassEq : mass + (∑ y ∈ bad, ν.w y) = 1 := by
      dsimp [mass]
      rw [← Finset.sum_union hdisj, hunion]
      exact ν.sum_eq_one
    have hmassHalf : 1 / 2 ≤ mass := by linarith [hmassEq, hbadMass]
    have hmassPos : 0 < mass := lt_of_lt_of_le (by norm_num) hmassHalf
    let ν' : Law N := Law.restrict ν good hmassPos
    have hweight (y : Fin N) : ν'.w y ≤ 2 * ν.w y := by
      by_cases hy : y ∈ good
      · dsimp [ν', Law.restrict]
        rw [if_pos hy]
        rw [div_le_iff₀ hmassPos]
        have hfactor : 1 ≤ 2 * mass := by linarith
        calc
          ν.w y = ν.w y * 1 := by ring
          _ ≤ ν.w y * (2 * mass) := mul_le_mul_of_nonneg_left hfactor (ν.nonneg y)
          _ = 2 * ν.w y * mass := by ring
      · simp only [ν', Law.restrict, if_neg hy]
        exact mul_nonneg (by norm_num) (ν.nonneg y)
    have hExpWidth : 2 * Real.exp (2 * (n : ℝ) ^ β) ≤ Real.exp ((n : ℝ) ^ (2 * β)) := by
      have htwo : 2 = Real.exp (Real.log 2) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
      calc
        2 * Real.exp (2 * (n : ℝ) ^ β) =
            Real.exp (Real.log 2) * Real.exp (2 * (n : ℝ) ^ β) := by rw [← htwo]
        _ = Real.exp (Real.log 2 + 2 * (n : ℝ) ^ β) := by rw [← Real.exp_add]
        _ ≤ Real.exp ((n : ℝ) ^ (2 * β)) := Real.exp_le_exp.mpr hβexp
    have hNcast : 0 < (N : ℝ) := by exact_mod_cast hNpos
    have hνdiv :
        (2 * Real.exp (2 * (n : ℝ) ^ β)) / N ≤ Real.exp ((n : ℝ) ^ (2 * β)) / N :=
      div_le_div_of_nonneg_right hExpWidth hNcast.le
    have hμdiv : Real.exp (2 * (n : ℝ) ^ β) / N ≤
        Real.exp ((n : ℝ) ^ (2 * β)) / N := by
      apply div_le_div_of_nonneg_right _ hNcast.le
      exact Real.exp_le_exp.mpr (by linarith [hβsquare])
    have hν'width : ν'.WidthLE ((n : ℝ) ^ (2 * β)) := by
      intro y
      calc
        ν'.w y ≤ 2 * ν.w y := hweight y
        _ ≤ 2 * (Real.exp (2 * (n : ℝ) ^ β) / N) :=
          mul_le_mul_of_nonneg_left (hνwidth y) (by norm_num)
        _ = (2 * Real.exp (2 * (n : ℝ) ^ β)) / N := by ring
        _ ≤ Real.exp ((n : ℝ) ^ (2 * β)) / N := hνdiv
    have hμ'width : μ.WidthLE ((n : ℝ) ^ (2 * β)) := by
      intro x
      exact (hμwidth x).trans hμdiv
    have hν'support : ν'.SupportedIn B := by
      intro y hyB
      by_cases hy : y ∈ good
      · simp [ν', Law.restrict, hy, hνB y hyB]
      · simp [ν', Law.restrict, hy]
    refine ⟨A, B, ?_, hAX, hBY⟩
    refine ⟨μ, ν', hμA, hν'support, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hgridBeta] using hμ'width
    · simpa only [hgridBeta] using hν'width
    intro y hyweight
    have hygood : y ∈ good := by
      by_contra hynot
      have : ν'.w y = 0 := by simp [ν', Law.restrict, hynot]
      linarith
    have hynotbad : y ∉ bad := (Finset.mem_sdiff.mp hygood).2
    have hydegree : ¬ colDeg E G μ y < 1 - δ := by
      intro hlt
      exact hynotbad (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hlt⟩)
    have hydegree' : 1 - δ ≤ colDeg E G μ y := le_of_not_gt hydegree
    simpa [δ] using hydegree'
  intro n hn κ hκ N E X Y hAvail
  have hAvail' : AvailableAt κ
      (fun n N E => (low false).toPatch n N E ∪ (low true).toPatch n N E)
      n N E X Y := by simpa [hUnion] using hAvail
  rcases AvailableAt.union hAvail' with hFalse | hTrue
  · exact ⟨false, hTrimColor n N E X Y hn false hFalse⟩
  · exact ⟨true, hTrimColor n N E X Y hn true hTrue⟩

/-- E7.1 in one-shot form, with the universal L6 exponent supplied by the caller. -/
theorem sparse_rect_not_available_of_L6_p_s07_d
    (Dstar D₀ c : ℝ) (hDstar : 0 < Dstar) (hD₀ : 0 < D₀)
    (hD₀star : D₀ < Dstar / 2) (hc : 0 < c)
    (hL6 : Needs.BroadSideProperty Dstar) :
    ∀ T : Stage, ¬ Available T (PViol D₀ c).toPatch := by
  classical
  let low : Colour → PairProp := fun G n N E σ τ =>
    σ.CapLE ((n : ℝ) ^ D₀) ∧ τ.WidthLE ((n : ℝ) ^ ((1 : ℝ) / 4)) ∧
      dens E (!G) σ τ ≤ (n : ℝ) ^ (-c)
  have hUnion : (PViol D₀ c).toPatch =
      fun n N E => (low false).toPatch n N E ∪ (low true).toPatch n N E := by
    funext n N E
    ext AB
    change
      (∃ σ τ : Law N, σ.SupportedIn AB.1 ∧ τ.SupportedIn AB.2 ∧
        PViol D₀ c n N E σ τ) ↔
      ((∃ σ τ : Law N, σ.SupportedIn AB.1 ∧ τ.SupportedIn AB.2 ∧
          low false n N E σ τ) ∨
        ∃ σ τ : Law N, σ.SupportedIn AB.1 ∧ τ.SupportedIn AB.2 ∧
          low true n N E σ τ)
    constructor
    · rintro ⟨σ, τ, hσA, hτB, hViol⟩
      rcases hViol with ⟨hσcap, hτwidth, col, hden⟩
      cases col
      · exact Or.inr ⟨σ, τ, hσA, hτB, hσcap, hτwidth, by simpa [low] using hden⟩
      · exact Or.inl ⟨σ, τ, hσA, hτB, hσcap, hτwidth, by simpa [low] using hden⟩
    · rintro (⟨σ, τ, hσA, hτB, hσcap, hτwidth, hden⟩ |
        ⟨σ, τ, hσA, hτB, hσcap, hτwidth, hden⟩)
      · exact ⟨σ, τ, hσA, hτB, hσcap, hτwidth, false, by simpa [low] using hden⟩
      · exact ⟨σ, τ, hσA, hτB, hσcap, hτwidth, true, by simpa [low] using hden⟩
  have hshot : ∀ κ > (0 : ℝ), ∃ n₀ C₀,
      ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
        LargeAt n₀ C₀ n N → True →
        AvailableAt κ (PViol D₀ c).toPatch n N E X Y → CubeAt n N E := by
    intro κ hκ
    have hκhalf : 0 < κ / 2 := by positivity
    have hDgap : 0 < Dstar - D₀ := by linarith
    obtain ⟨nL6, C₀, hL6shot⟩ :=
      hL6 (1 / 4) (c / 2) (8 / κ) (by norm_num) (by norm_num)
        (by positivity) (by positivity)
    have htend (a : ℝ) (ha : 0 < a) :
        Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
      (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
    have hDgapEvent : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (Dstar - D₀) :=
      (htend (Dstar - D₀) hDgap).eventually (eventually_ge_atTop (2 : ℝ))
    have hcEvent : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (c / 2) :=
      (htend (c / 2) (by positivity)).eventually (eventually_ge_atTop (2 : ℝ))
    have hnEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact_mod_cast hn
    have hLargeN : ∀ᶠ n : ℕ in atTop,
        1 ≤ (n : ℝ) ∧ 2 ≤ (n : ℝ) ^ (Dstar - D₀) ∧
          2 ≤ (n : ℝ) ^ (c / 2) := by
      filter_upwards [hnEvent, hDgapEvent, hcEvent] with n hn hD hc
      exact ⟨hn, hD, hc⟩
    obtain ⟨nTrim, hnTrim⟩ := Filter.eventually_atTop.1 hLargeN
    refine ⟨max nL6 nTrim, C₀, ?_⟩
    intro n N E X Y hLarge _hside hAvail
    have hnLarge : nTrim ≤ n := le_trans (Nat.le_max_right nL6 nTrim) hLarge.1
    have hcut := hnTrim n hnLarge
    have hnR : 1 ≤ (n : ℝ) := hcut.1
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
    have hpowD : (n : ℝ) ^ Dstar =
        (n : ℝ) ^ D₀ * (n : ℝ) ^ (Dstar - D₀) := by
      calc
        (n : ℝ) ^ Dstar = (n : ℝ) ^ (D₀ + (Dstar - D₀)) := by congr 1 <;> ring
        _ = (n : ℝ) ^ D₀ * (n : ℝ) ^ (Dstar - D₀) := Real.rpow_add hnpos _ _
    have hcapFactor : 2 * (n : ℝ) ^ D₀ ≤ (n : ℝ) ^ Dstar := by
      rw [hpowD]
      exact mul_le_mul_of_nonneg_left hcut.2.1
        (Real.rpow_nonneg hnR.le D₀)
    have δ : ℝ := (n : ℝ) ^ (-(c / 2))
    have hδpos : 0 < δ := Real.rpow_pos_of_pos hnpos _
    have hδsquare : (n : ℝ) ^ (-c) = δ * δ := by
      dsimp [δ]
      calc
        (n : ℝ) ^ (-c) = (n : ℝ) ^ (-(c / 2) + -(c / 2)) := by congr 1 <;> ring
        _ = (n : ℝ) ^ (-(c / 2)) * (n : ℝ) ^ (-(c / 2)) := Real.rpow_add hnpos _ _
    have hδtimes : δ * (n : ℝ) ^ (c / 2) = 1 := by
      dsimp [δ]
      calc
        (n : ℝ) ^ (-(c / 2)) * (n : ℝ) ^ (c / 2) =
            (n : ℝ) ^ (-(c / 2) + c / 2) := (Real.rpow_add hnpos _ _).symm
        _ = 1 := by simp
    have hδsmall : δ ≤ 1 / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hcut.2.2 (le_of_lt hδpos)
      rw [hδtimes] at hmul
      linarith
    have hColorShot : ∀ G : Colour, AvailableAt (κ / 2) (low G).toPatch n N E X Y →
        CubeAt n N E := by
      intro G hLowAvail
      have hNpos : 0 < N := by
        by_contra hN
        have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
        subst N
        obtain ⟨A, B, hAB, hAX, hBY⟩ := hLowAvail ∅ ∅
          (by simp; positivity) (by simp; positivity)
        rcases hAB with ⟨σ, τ, hσA, hτB, hproperty⟩
        have hsum := σ.sum_eq_one
        norm_num at hsum
      let I : Type := {AB : Finset (Fin N) × Finset (Fin N) //
        ∃ σ τ : Law N, σ.SupportedIn AB.1 ∧ τ.SupportedIn AB.2 ∧ low G n N E σ τ}
      let σMenu : I → Law N := fun i => Classical.choose i.2
      let τMenu : I → Law N := fun i => Classical.choose (Classical.choose_spec i.2)
      have hmenuSpec (i : I) : (σMenu i).SupportedIn i.val.1 ∧
          (τMenu i).SupportedIn i.val.2 ∧ low G n N E (σMenu i) (τMenu i) :=
        Classical.choose_spec (Classical.choose_spec i.2)
      have hmenuWidth (i : I) : (τMenu i).WidthLE ((n : ℝ) ^ ((1 : ℝ) / 4)) := by
        rcases (hmenuSpec i).2.2 with ⟨hσcap, hτwidth, hdefect⟩
        exact hτwidth
      let bad : I → Finset (Fin N) := fun i => Finset.univ.filter
        (fun x => rowDeg E G x (τMenu i) < 1 - δ)
      let good : I → Finset (Fin N) := fun i => Finset.univ \ bad i
      let mass : I → ℝ := fun i => ∑ x ∈ good i, (σMenu i).w x
      have hdensRow (i : I) (col : Colour) :
          dens E col (σMenu i) (τMenu i) =
            ∑ x, (σMenu i).w x * rowDeg E col x (τMenu i) := by
        unfold dens rowDeg
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      have hrowComplement (i : I) (x : Fin N) :
          rowDeg E G x (τMenu i) + rowDeg E (!G) x (τMenu i) = 1 := by
        unfold rowDeg
        rw [← Finset.sum_add_distrib]
        calc
          (∑ y, ((τMenu i).w y * (if Hits E G x y then 1 else 0) +
              (τMenu i).w y * (if Hits E (!G) x y then 1 else 0))) =
              ∑ y, (τMenu i).w y := by
            apply Finset.sum_congr rfl
            intro y hy
            cases G <;> by_cases hE : E x y <;> simp [Hits, hE]
          _ = 1 := (τMenu i).sum_eq_one
      have hrowNonneg (i : I) (col : Colour) (x : Fin N) :
          0 ≤ rowDeg E col x (τMenu i) := by
        unfold rowDeg
        apply Finset.sum_nonneg
        intro y hy
        split_ifs <;> exact mul_nonneg ((τMenu i).nonneg y) (by positivity)
      have hbadDegree (i : I) (x : Fin N) (hx : x ∈ bad i) :
          δ ≤ rowDeg E (!G) x (τMenu i) := by
        have hx' := (Finset.mem_filter.mp hx).2
        have hdegree := hrowComplement i x
        linarith
      have hbadMarkov (i : I) :
          δ * (∑ x ∈ bad i, (σMenu i).w x) ≤ (n : ℝ) ^ (-c) := by
        have hproperty := (hmenuSpec i).2.2
        rcases hproperty with ⟨hσcap, hτwidth, hdefect⟩
        calc
          δ * (∑ x ∈ bad i, (σMenu i).w x) =
              ∑ x ∈ bad i, (σMenu i).w x * δ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ ≤ ∑ x ∈ bad i,
              (σMenu i).w x * rowDeg E (!G) x (τMenu i) := by
            apply Finset.sum_le_sum
            intro x hx
            exact mul_le_mul_of_nonneg_left (hbadDegree i x hx) ((σMenu i).nonneg x)
          _ ≤ ∑ x, (σMenu i).w x * rowDeg E (!G) x (τMenu i) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (bad i))
              (by intro x hx hnot; exact mul_nonneg ((σMenu i).nonneg x) (hrowNonneg i (!G) x))
          _ = dens E (!G) (σMenu i) (τMenu i) := (hdensRow i (!G)).symm
          _ ≤ (n : ℝ) ^ (-c) := hdefect
      have hbadMass (i : I) : (∑ x ∈ bad i, (σMenu i).w x) ≤ δ := by
        have hbadMarkov' : δ * (∑ x ∈ bad i, (σMenu i).w x) ≤ δ * δ := by
          rw [hδsquare] at hbadMarkov
          exact hbadMarkov i
        have hdiv : (∑ x ∈ bad i, (σMenu i).w x) ≤ (δ * δ) / δ :=
          (le_div_iff₀ hδpos).2 (by simpa [mul_comm] using hbadMarkov')
        have hcancel : (δ * δ) / δ = δ := by field_simp [ne_of_gt hδpos]
        simpa [hcancel] using hdiv
      have hdisj (i : I) : Disjoint (good i) (bad i) := disjoint_sdiff_self_left
      have hunion (i : I) : good i ∪ bad i = Finset.univ := by simp [good]
      have hmassEq (i : I) : mass i + (∑ x ∈ bad i, (σMenu i).w x) = 1 := by
        dsimp [mass]
        rw [← Finset.sum_union (hdisj i), hunion i]
        exact (σMenu i).sum_eq_one
      have hmassHalf (i : I) : 1 / 2 ≤ mass i := by
        have := hmassEq i
        have := hbadMass i
        linarith
      have hmassPos (i : I) : 0 < mass i :=
        lt_of_lt_of_le (by norm_num) (hmassHalf i)
      let σTrim : I → Law N := fun i => Law.restrict (σMenu i) (good i) (hmassPos i)
      have htrimWeight (i : I) (x : Fin N) : (σTrim i).w x ≤ 2 * (σMenu i).w x := by
        by_cases hx : x ∈ good i
        · dsimp [σTrim, Law.restrict]
          rw [if_pos hx]
          rw [div_le_iff₀ (hmassPos i)]
          have hfactor : 1 ≤ 2 * mass i := by linarith [hmassHalf i]
          calc
            (σMenu i).w x = (σMenu i).w x * 1 := by ring
            _ ≤ (σMenu i).w x * (2 * mass i) :=
              mul_le_mul_of_nonneg_left hfactor ((σMenu i).nonneg x)
            _ = 2 * (σMenu i).w x * mass i := by ring
        · simp only [σTrim, Law.restrict, if_neg hx]
          exact mul_nonneg (by norm_num) ((σMenu i).nonneg x)
      have htrimCap (i : I) : (σTrim i).CapLE ((n : ℝ) ^ Dstar) := by
        intro x
        have hproperty := (hmenuSpec i).2.2
        rcases hproperty with ⟨hσcap, hτwidth, hdefect⟩
        calc
          (N : ℝ) * (σTrim i).w x ≤ (N : ℝ) * (2 * (σMenu i).w x) :=
            mul_le_mul_of_nonneg_left (htrimWeight i x) (by positivity)
          _ = 2 * ((N : ℝ) * (σMenu i).w x) := by ring
          _ ≤ 2 * (n : ℝ) ^ D₀ := mul_le_mul_of_nonneg_left (hσcap x) (by norm_num)
          _ ≤ (n : ℝ) ^ Dstar := hcapFactor
      have htrimDegree (i : I) (x : Fin N) (hx : 0 < (σTrim i).w x) :
          1 - δ ≤ rowDeg E G x (τMenu i) := by
        have hxgood : x ∈ good i := by
          by_contra hxnot
          have hzero : (σTrim i).w x = 0 := by simp [σTrim, Law.restrict, hxnot]
          linarith
        have hxnotbad : x ∉ bad i := (Finset.mem_sdiff.mp (by simpa [good] using hxgood)).2
        exact le_of_not_gt (fun hlt => hxnotbad
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hlt⟩))
      have hσTrimSupport (i : I) : (σTrim i).SupportedIn i.val.1 := by
        intro x hxA
        by_cases hx : x ∈ good i
        · simp [σTrim, Law.restrict, hx, (hmenuSpec i).1 x hxA]
        · simp [σTrim, Law.restrict, hx]
      have havailMenu : ∀ RX RY : Finset (Fin N),
          (RX.card : ℝ) ≤ (κ / 2) * N → (RY.card : ℝ) ≤ (κ / 2) * N →
          ∃ i : I, (∀ x ∈ RX, (σTrim i).w x = 0) ∧
            (∀ y ∈ RY, (τMenu i).w y = 0) := by
        intro RX RY hRX hRY
        obtain ⟨A, B, hAB, hAX, hBY⟩ := hLowAvail RX RY hRX hRY
        rcases hAB with ⟨σ, τ, hσA, hτB, hproperty⟩
        let i : I := ⟨(A, B), ⟨σ, τ, hσA, hτB, hproperty⟩⟩
        refine ⟨i, ?_, ?_⟩
        · intro x hxRX
          have hxnotA : x ∉ i.val.1 := by
            intro hxA
            exact (Finset.mem_sdiff.mp (hAX hxA)).2 hxRX
          exact hσTrimSupport i x hxnotA
        · intro y hyRY
          have hynotB : y ∉ i.val.2 := by
            intro hyB
            exact (Finset.mem_sdiff.mp (hBY hyB)).2 hyRY
          exact (hmenuSpec i).2.1 y hynotB
      obtain ⟨t, ht0, htsum, htσ, htτ⟩ :=
        balanced_mixture hNpos σTrim τMenu (κ / 2) hκhalf havailMenu
      let M : TagMix N where
        ι := I
        fin := inferInstance
        Λ := t
        Λ_nonneg := ht0
        Λ_sum := htsum
        μ := τMenu
        ν := σTrim
      have hNcast : 0 < (N : ℝ) := by exact_mod_cast hNpos
      have hbalance : M.Balanced (8 / κ) := by
        constructor
        · intro x
          change (N : ℝ) * ∑ i, t i * (τMenu i).w x ≤ 8 / κ
          calc
            (N : ℝ) * ∑ i, t i * (τMenu i).w x ≤
                (N : ℝ) * (4 / ((κ / 2) * N)) :=
              mul_le_mul_of_nonneg_left (htτ x) (by positivity)
            _ = 8 / κ := by field_simp [ne_of_gt hκ, ne_of_gt hNcast]; ring
        · intro y
          change (N : ℝ) * ∑ i, t i * (σTrim i).w y ≤ 8 / κ
          calc
            (N : ℝ) * ∑ i, t i * (σTrim i).w y ≤
                (N : ℝ) * (4 / ((κ / 2) * N)) :=
              mul_le_mul_of_nonneg_left (htσ y) (by positivity)
            _ = 8 / κ := by field_simp [ne_of_gt hκ, ne_of_gt hNcast]; ring
      have hL6cube := hL6shot n N (transposeRel E) G M
        (by
          obtain ⟨hn, hlow, hhigh⟩ := hLarge
          exact ⟨le_trans (Nat.le_max_left nL6 nTrim) hn, hlow, hhigh⟩)
        hbalance
        (by
          intro i hi
          exact hmenuWidth i)
        (by
          intro i hi
          exact htrimCap i)
        (by
          intro i y hi hy
          rw [colDeg_transpose]
          have hdeg := htrimDegree i y hy
          simpa [δ] using hdeg)
      exact CubeAt.of_transpose hL6cube
    have hAvail' : AvailableAt κ
        (fun n N E => (low false).toPatch n N E ∪ (low true).toPatch n N E)
        n N E X Y := by simpa [hUnion] using hAvail
    rcases AvailableAt.union hAvail' with hLowFalse | hLowTrue
    · exact hColorShot false hLowFalse
    · exact hColorShot true hLowTrue
  exact not_available_of_oneShot' (T := T) (P := (PViol D₀ c).toPatch)
    (side := fun _ _ _ _ _ => True) (by simp) hshot

end HypercubeRamsey.S07
