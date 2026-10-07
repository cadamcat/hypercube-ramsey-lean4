import HypercubeRamsey.S08.AsymmetricPurity
import HypercubeRamsey.S08.Needs

/-!
# Section 8: asymmetric discrepancy

C8.2 is assembled from the one-dimension trimming node, the L8.1 one-shot result, L3.3a, stabilization, and
the consumed L4.1 implication. Only the large trimming statement remains a skeleton node.
-/

namespace HypercubeRamsey

open Filter

private theorem tau8_quarter_lt_one (η₀ : ℝ) (_hη₀ : 0 < η₀) : tau8 η₀ / 4 < 1 := by
  unfold tau8
  have hm : min (η₀ / 2) (4 / 100 : ℝ) ≤ 4 / 100 := min_le_right _ _
  nlinarith

/-- Asymmetric witness pair: the narrow first-side law has high degree into the broad second-side law. -/
def AsymmetricWitness (G : Colour) (β γ δ : ℝ) : PairProp := fun n _N E μ ν =>
  μ.WidthLE ((n : ℝ) ^ β) ∧ ν.WidthLE ((n : ℝ) ^ γ) ∧
    ∀ x, 0 < μ.w x → 1 - Real.exp (-((n : ℝ) ^ δ)) ≤ rowDeg E G x ν

/-- C8.2a (08:457–463): trim an available pure pair to an asymmetric degree witness.

The first law is the narrow side. Restricting it discards rows with poor degree and increases its width by an
O(1) term, absorbed by `β⁺`; the broad-side budget is absorbed by `γ⁺`.
-/
theorem asymmetric_witness_of_pure_available
    (η₀ β γ h βplus γplus κ : ℝ)
    (hη₀ : 0 < η₀) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hβτ : β < tau8 η₀ / 4) (hγ : γ < 1) (hh : 0 < h)
    (hβplus : β < βplus) (hβplusτ : βplus < tau8 η₀ / 4)
    (hγplus : γ < γplus) (hγplus1 : γplus < 1) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
      ∀ X Y : Finset (Fin N), n₀ ≤ n →
        AvailableAt κ (PPure β γ h).toPatch n N E X Y →
        ∃ G : Colour,
          AvailableAt (κ / 2) (AsymmetricWitness G βplus γplus (h / 2)).toPatch n N E X Y := by
  sorry

private theorem pure_mem_FamB (β γ h : ℚ) :
    (PPure (β : ℝ) (γ : ℝ) (h : ℝ)).toPatch ∈ FamB := by
  unfold FamB
  simp only [Set.mem_union, Set.mem_setOf_eq]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨β, γ, h, Or.inl rfl⟩)))

private theorem bias_mem_FamB (β γ h : ℚ) :
    (PBias (pw (β : ℝ)) (pw (γ : ℝ)) (h : ℝ)).toPatch ∈ FamB := by
  unfold FamB
  simp only [Set.mem_union, Set.mem_setOf_eq]
  exact Or.inl (Or.inl (Or.inr ⟨β, γ, h, Or.inl rfl⟩))

/-- C8.2b (08:463–464): the initial discrepancy excludes availability of an asymmetric pure pair. -/
theorem asymmetric_pure_not_available
    (η₀ : ℝ) (hη₀ : 0 < η₀) (T : Stage)
    (hD : DiscAt T (pw η₀) (pw η₀) (fun n => n ^ (-η₀)))
    (β γ h : ℚ) (hβ : 0 < β) (hβτ : (β : ℝ) < tau8 η₀ / 4)
    (hβγ : (β : ℝ) ≤ γ) (hγ : (γ : ℝ) < 1) (hh : 0 < h) :
    ¬ Available T (PPure (β : ℝ) (γ : ℝ) (h : ℝ)).toPatch := by
  have hside : ∀ᶠ k in atTop,
      DiscOne (T.S.E k) (T.X k) (T.Y k)
        ((T.S.n k : ℝ) ^ η₀) ((T.S.n k : ℝ) ^ η₀) ((T.S.n k : ℝ) ^ (-η₀)) :=
    (discAt_iff_eventually_discOne T (pw η₀) (pw η₀) (fun n => n ^ (-η₀))).mp hD
  have hshot : ∀ κ > (0 : ℝ), ∃ n₀ C₀,
      ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
        ∀ X Y : Finset (Fin N),
          LargeAt n₀ C₀ n N →
          DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
          AvailableAt κ (PPure (β : ℝ) (γ : ℝ) (h : ℝ)).toPatch n N E X Y →
          CubeAt n N E := by
    intro κ hκ
    let βplus : ℝ := ((β : ℝ) + tau8 η₀ / 4) / 2
    let γplus : ℝ := ((γ : ℝ) + 1) / 2
    have hγposR : 0 < (γ : ℝ) :=
      lt_of_lt_of_le (by exact_mod_cast hβ) hβγ
    have hτpos : 0 < tau8 η₀ := by
      unfold tau8
      positivity
    have hτlt : tau8 η₀ / 4 < 1 := tau8_quarter_lt_one η₀ hη₀
    obtain ⟨nTrim, hTrim⟩ := asymmetric_witness_of_pure_available
      η₀ (β : ℝ) (γ : ℝ) (h : ℝ) βplus γplus κ
      hη₀ (by exact_mod_cast hβ) hβγ hβτ hγ (by exact_mod_cast hh)
      (by dsimp [βplus]; linarith) (by dsimp [βplus]; linarith)
      (by dsimp [γplus]; linarith) (by dsimp [γplus]; linarith) hκ
    let p : ℝ := (h : ℝ) / 2
    let K : ℝ := 4 / (κ / 2)
    have hK : 0 < K := by dsimp [K]; positivity
    obtain ⟨nPure, C₀, hPure⟩ := asymmetric_purity_reversed
      η₀ γplus βplus p K hη₀
      (by dsimp [γplus]; linarith [hγposR])
      (by dsimp [γplus]; linarith)
      (by
        dsimp [βplus]
        have hb : 0 < (β : ℝ) := by exact_mod_cast hβ
        linarith [hτpos, hb])
      (by dsimp [βplus]; linarith [hτlt])
      (by dsimp [p]; positivity) hK
    refine ⟨max nTrim nPure, C₀, ?_⟩
    intro n N E X Y hLarge hDisc hAvail
    have hTrimN : nTrim ≤ n := le_trans (le_max_left _ _) hLarge.1
    obtain ⟨G, hWit⟩ := hTrim n N E X Y hTrimN hAvail
    have hκhalf : 0 < κ / 2 := by positivity
    obtain ⟨M, hBal, hWitness⟩ := L3_3a_consumed
      (κ / 2) n N E X Y (AsymmetricWitness G βplus γplus p) hκhalf hWit
    have hLargePure : LargeAt nPure C₀ n N := by
      rcases hLarge with ⟨hn, hNlo, hNhi⟩
      exact ⟨le_trans (le_max_right _ _) hn, hNlo, hNhi⟩
    have hRows : ∀ i, 0 < M.Λ i →
        (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
        (M.μ i).WidthLE ((n : ℝ) ^ βplus) ∧ (M.ν i).WidthLE ((n : ℝ) ^ γplus) ∧
        (∀ x, 0 < (M.μ i).w x →
          1 - Real.exp (-((n : ℝ) ^ p)) ≤ rowDeg E G x (M.ν i)) := by
      intro i hi
      rcases hWitness i hi with ⟨hμsupp, hνsupp, hQ⟩
      exact ⟨hμsupp, hνsupp, hQ.1, hQ.2.1, hQ.2.2⟩
    have hKbal : M.Balanced K := by
      change M.Balanced (4 / (κ / 2))
      exact hBal
    exact hPure n N E X Y G M hLargePure hDisc hKbal hRows
  exact not_available_of_oneShot' (T := T)
    (P := (PPure (β : ℝ) (γ : ℝ) (h : ℝ)).toPatch)
    (side := fun n N E X Y =>
      DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)))
    hside hshot

private theorem discAt_of_bias_absent
    (T : Stage) (β γ h : ℝ)
    (hAbsent : EventuallyAbsent T (PBias (pw β) (pw γ) h).toPatch) :
    DiscAt T (pw β) (pw γ) (fun n => n ^ (-h)) := by
  rw [discAt_iff_eventually_discOne]
  filter_upwards [hAbsent] with k hk
  intro μ ν hμ hν hμw hνw c
  let n : ℕ := T.S.n k
  have hTrue : |dens (T.S.E k) true μ ν - 1 / 2| < (n : ℝ) ^ (-h) := by
    by_contra hnot
    have hlarge : (n : ℝ) ^ (-h) ≤ |dens (T.S.E k) true μ ν - 1 / 2| := le_of_not_gt hnot
    have hmem : (T.X k, T.Y k) ∈
        (PBias (pw β) (pw γ) h).toPatch (T.S.n k) (T.S.N k) (T.S.E k) := by
      exact ⟨μ, ν, hμ, hν, hμw, hνw, hlarge⟩
    exact hk (T.X k) (T.Y k) hmem ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩
  have hAbs : |dens (T.S.E k) c μ ν - 1 / 2| =
      |dens (T.S.E k) true μ ν - 1 / 2| := by
    cases c with
    | true => rfl
    | false =>
        rw [dens_false]
        have hneg : 1 - dens (T.S.E k) true μ ν - 1 / 2 =
            -(dens (T.S.E k) true μ ν - 1 / 2) := by ring
        rw [hneg, abs_neg]
  change |dens (T.S.E k) c μ ν - 1 / 2| ≤ ((n : ℝ) ^ (-h))
  rw [hAbs]
  exact le_of_lt hTrue

private theorem pure_mem_FamB' (β γ h : ℚ) :
    (PPure (β : ℝ) (γ : ℝ) (h : ℝ)).toPatch ∈ FamB := pure_mem_FamB β γ h

private theorem bias_mem_FamB' (β γ h : ℚ) :
    (PBias (pw (β : ℝ)) (pw (γ : ℝ)) (h : ℝ)).toPatch ∈ FamB := bias_mem_FamB β γ h

/-- C8.2 (08:457–468): asymmetric power discrepancy, in both orientations. -/
theorem asymmetric_discrepancy
    (η₀ : ℝ) (hη₀ : 0 < η₀) (T : Stage)
    (hT : StabilizedOn T FamB)
    (hD : DiscAt T (pw η₀) (pw η₀) (fun n => n ^ (-η₀))) :
    ∀ β γ : ℚ, 0 < β → (β : ℝ) < tau8 η₀ / 4 → 0 < γ → γ < 1 →
      ∃ h > (0 : ℝ),
        DiscAt T (pw (β : ℝ)) (pw (γ : ℝ)) (fun n => n ^ (-h)) ∧
        DiscAt T.swap (pw (β : ℝ)) (pw (γ : ℝ)) (fun n => n ^ (-h)) := by
  intro β γ hβ hβτ hγ hγlt
  let γ₀ : ℚ := max β γ
  have hτlt : tau8 η₀ / 4 < 1 := tau8_quarter_lt_one η₀ hη₀
  have hβlt1 : (β : ℝ) < 1 := lt_trans hβτ hτlt
  have hγ₀cast : (γ₀ : ℝ) = max (β : ℝ) (γ : ℝ) := by simp [γ₀]
  have hβleγ₀ : (β : ℝ) ≤ (γ₀ : ℝ) := by
    rw [hγ₀cast]
    exact le_max_left _ _
  have hγleγ₀ : (γ : ℝ) ≤ (γ₀ : ℝ) := by
    rw [hγ₀cast]
    exact le_max_right _ _
  have hγ₀lt1 : (γ₀ : ℝ) < 1 := by
    rw [hγ₀cast]
    exact max_lt_iff.mpr ⟨hβlt1, by exact_mod_cast hγlt⟩
  obtain ⟨H, hH, hL4⟩ := L4_1_consumed
    (β : ℝ) (γ₀ : ℝ) (by exact_mod_cast hβ) hβleγ₀ hγ₀lt1
  obtain ⟨q, hq0, hqH⟩ := exists_rat_btwn hH
  have hq0Q : 0 < q := by exact_mod_cast hq0
  have hq0R : 0 < (q : ℝ) := by exact_mod_cast hq0
  have hqHR : (q : ℝ) ≤ H := le_of_lt hqH
  have hβleγ₀Q : β ≤ γ₀ := le_max_left β γ
  have hβγ₀ : (β : ℝ) ≤ (γ₀ : ℝ) := hβleγ₀
  have hPureAbsent : EventuallyAbsent T
      (PPure (β : ℝ) (γ₀ : ℝ) (q : ℝ)).toPatch := by
    have hNoAvail := asymmetric_pure_not_available η₀ hη₀ T hD
      β γ₀ q hβ hβτ hβγ₀ hγ₀lt1 hq0Q
    rcases hT _ (pure_mem_FamB' β γ₀ q) with hav | habs
    · exact (hNoAvail hav).elim
    · exact habs
  have hBiasAbsent : EventuallyAbsent T
      (PBias (pw (β : ℝ)) (pw (γ₀ : ℝ)) (q : ℝ)).toPatch := by
    have hNoAvail : ¬ Available T
        (PBias (pw (β : ℝ)) (pw (γ₀ : ℝ)) (q : ℝ)).toPatch := by
      intro hav
      exact hL4 (q : ℝ) hq0R hqHR T hav hPureAbsent
    rcases hT _ (bias_mem_FamB' β γ₀ q) with hav | habs
    · exact (hNoAvail hav).elim
    · exact habs
  have hBig : DiscAt T (pw (β : ℝ)) (pw (γ₀ : ℝ))
      (fun n => n ^ (-(q : ℝ))) :=
    discAt_of_bias_absent T (β : ℝ) (γ₀ : ℝ) (q : ℝ) hBiasAbsent
  have hTswap : StabilizedOn T.swap FamB := StabilizedOn.swap hT FamB_swap
  have hDswap : DiscAt T.swap (pw η₀) (pw η₀) (fun n => n ^ (-η₀)) :=
    (DiscAt.swap_iff T (pw η₀) (pw η₀) (fun n => n ^ (-η₀))).2 hD
  have hPureAbsentSwap : EventuallyAbsent T.swap
      (PPure (β : ℝ) (γ₀ : ℝ) (q : ℝ)).toPatch := by
    have hNoAvail := asymmetric_pure_not_available η₀ hη₀ T.swap hDswap
      β γ₀ q hβ hβτ hβγ₀ hγ₀lt1 hq0Q
    rcases hTswap _ (pure_mem_FamB' β γ₀ q) with hav | habs
    · exact (hNoAvail hav).elim
    · exact habs
  have hBiasAbsentSwap : EventuallyAbsent T.swap
      (PBias (pw (β : ℝ)) (pw (γ₀ : ℝ)) (q : ℝ)).toPatch := by
    have hNoAvail : ¬ Available T.swap
        (PBias (pw (β : ℝ)) (pw (γ₀ : ℝ)) (q : ℝ)).toPatch := by
      intro hav
      exact hL4 (q : ℝ) hq0R hqHR T.swap hav hPureAbsentSwap
    rcases hTswap _ (bias_mem_FamB' β γ₀ q) with hav | habs
    · exact (hNoAvail hav).elim
    · exact habs
  have hBigSwap : DiscAt T.swap (pw (β : ℝ)) (pw (γ₀ : ℝ))
      (fun n => n ^ (-(q : ℝ))) :=
    discAt_of_bias_absent T.swap (β : ℝ) (γ₀ : ℝ) (q : ℝ) hBiasAbsentSwap
  have hSecondBudget : ∀ᶠ x : ℝ in atTop,
      x ^ (γ : ℝ) ≤ x ^ (γ₀ : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact Real.rpow_le_rpow_of_exponent_le hx hγleγ₀
  have hFirstBudget : ∀ᶠ x : ℝ in atTop,
      x ^ (β : ℝ) ≤ x ^ (β : ℝ) := Filter.Eventually.of_forall (fun _ => le_rfl)
  have hError : ∀ᶠ x : ℝ in atTop,
      x ^ (-(q : ℝ)) ≤ x ^ (-(q : ℝ)) := Filter.Eventually.of_forall (fun _ => le_rfl)
  refine ⟨(q : ℝ), hq0R, ?_, ?_⟩
  · exact DiscAt.mono hBig hFirstBudget hSecondBudget hError
  · exact DiscAt.mono hBigSwap hFirstBudget hSecondBudget hError

end HypercubeRamsey
