import HypercubeRamsey.S04.CoreLemmas
import HypercubeRamsey.S04.GadgetNodes_q_s04_gadget
import HypercubeRamsey.S04.GadgetNodes_sol_s04_gadget

/-!
# L4.1c, L4.1d: the key gadget and the patch tags

Source: `sections/04-…tex`, lines 100–162; blueprint L4.1c, D4.3/L4.1d.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- L4.1c(1) (04:118–127, 134–138): all one-bit changes of an input change at most one gadget, and within a
gadget produce at most `1 + 2 log₂ S` outputs (the first changed comparison on the search path and the direction of
the move determine the new multiset; the moving chunk stays on the same side of every elementary midpoint).  Hence
`|Z_u| ≤ 1 + G_n (2 log₂ S + 1) ≤ n^{γ - 0.9ω}` for large `n`. -/
theorem key_nbr_card (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyNbrCard β γ n := by
  obtain ⟨nNumeric, hnNumeric⟩ :=
    HypercubeRamsey.Lane_sol_s04_gadget.key_neighbor_numeric_bound hβ hβγ hγ
  obtain ⟨nGrowth, hnGrowth⟩ :=
    HypercubeRamsey.Lane_q_s04_gadget.keyFiber_growth_thresholds hβ hβγ hγ
  refine ⟨max 1 (max nNumeric nGrowth), ?_⟩
  intro n hn u
  have hnNumeric' : nNumeric ≤ n :=
    (le_max_left nNumeric nGrowth).trans ((le_max_right 1 _).trans hn)
  have hnGrowth' : nGrowth ≤ n :=
    (le_max_right nNumeric nGrowth).trans ((le_max_right 1 _).trans hn)
  have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn
  have hSreal : (4 : ℝ) ≤ (gadgetPower β γ n : ℝ) :=
    (by norm_num : (4 : ℝ) ≤ 128).trans
      ((hnGrowth n hnGrowth').1.trans
        (HypercubeRamsey.Lane_q_s04_gadget.gadgetPower_ge_scale n
          (omega4_pos hβ hγ) hn1))
  have hS : 4 ≤ gadgetPower β γ n := by exact_mod_cast hSreal
  have hcard : ((Zset β γ u).card : ℝ) ≤
      ((1 + gadgetNum β γ n * (Nat.log2 (gadgetPower β γ n) * 2) : ℕ) : ℝ) := by
    exact_mod_cast HypercubeRamsey.Lane_q_s04_gadget.keyNbr_card_le_path u hS
  exact hcard.trans (hnNumeric n hnNumeric')

/-- L4.1c(3) (04:134–136, 393–394): the key depends only on the `m = G_n s' ℓ ≤ 128 n^{γ+13ω}` special
coordinates, so at most `n^{γ+14ω}` coordinate flips of a vertex change its key (for large `n`). -/
theorem key_local (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyLocal β γ n := by
  obtain ⟨n₀, hn₀⟩ := HypercubeRamsey.Lane_q_s04_gadget.specialNum_eventually_bound hβ hβγ hγ
  refine ⟨n₀, ?_⟩
  intro n hn v
  exact (HypercubeRamsey.Lane_q_s04_gadget.keyLocal_le_specialNum n v).trans (hn₀ n hn)

/-- L4.1c(2) (04:128–143): for a fixed output each chunk lies on a prescribed side of a fixed midpoint, which has
probability at most `2/3` (each clipped endpoint has probability at least `1/3`: the counts are symmetric and the
central interval has `Binomial(ℓ, 1/2)`-mass `O(S² s'^{-3})`); chunks are independent and a parity class induces
the uniform law on the `m < n` special coordinates.  So each key has parity-class fraction at most
`(2/3)^{s' G_n} ≤ exp(-n^{γ+ω}/10)` for large `n`. -/
theorem key_fiber (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyFiber β γ n := by
  classical
  let ω := HypercubeRamsey.omega4 β γ
  have hω : 0 < ω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have hωltγ : ω < γ := by
    dsimp [ω, HypercubeRamsey.omega4]
    have hmin : min β (1 - γ) ≤ β := min_le_left _ _
    have hdiv : β / 1000 < β := by nlinarith
    linarith
  have hωcap : ω ≤ (1 - γ) / 1000 := by
    dsimp [ω, HypercubeRamsey.omega4]
    gcongr
    exact min_le_right _ _
  have hgammaOmega : 0 < γ + ω := by linarith [hβ, hβγ, hω]
  have hexp : γ + 14 * ω < 1 := by nlinarith [hωcap, hγ]
  obtain ⟨nGrowth, hnGrowth⟩ :=
    HypercubeRamsey.Lane_q_s04_gadget.keyFiber_growth_thresholds hβ hβγ hγ
  obtain ⟨nM, hnM⟩ :=
    HypercubeRamsey.Lane_q_s04_gadget.specialNum_eventually_bound hβ hβγ hγ
  let nTail := max nGrowth nM
  let n₀ := max 2 nTail
  refine ⟨n₀, ?_⟩
  intro n hn κ
  have htail : nTail ≤ n := (le_max_right 2 nTail).trans hn
  have hn2 : 2 ≤ n := (le_max_left 2 nTail).trans hn
  have hnGrowth' : nGrowth ≤ n :=
    (le_max_left nGrowth nM).trans (le_max_right 2 nTail) |>.trans hn
  have hnM' : nM ≤ n :=
    (le_max_right nGrowth nM).trans (le_max_right 2 nTail) |>.trans hn
  have hGrowth := hnGrowth n hnGrowth'
  have hpowSlarge : (128 : ℝ) ≤ (n : ℝ) ^ (2 * ω) := by simpa [ω] using hGrowth.1
  have hpowGlarge : (10 : ℝ) ≤ (n : ℝ) ^ (γ - ω) := by simpa [ω] using hGrowth.2
  have hspecialBound : (HypercubeRamsey.S04.specialNum β γ n : ℝ) ≤
      (n : ℝ) ^ (γ + 14 * ω) := hnM n hnM'
  have hnreal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hnrealPos : 0 < (n : ℝ) := by positivity
  have hpowStrict : (n : ℝ) ^ (γ + 14 * ω) < (n : ℝ) := by
    simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hnreal hexp
  have hmStrictReal :
      (HypercubeRamsey.S04.specialNum β γ n : ℝ) < (n : ℝ) :=
    hspecialBound.trans_lt hpowStrict
  have hmStrict : HypercubeRamsey.S04.specialNum β γ n < n := by
    exact_mod_cast hmStrictReal
  have hmnNat : HypercubeRamsey.S04.specialNum β γ n ≤ n := hmStrict.le
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let S := HypercubeRamsey.S04.gadgetPower β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  let m := G * s * ℓ
  have hSdef : S = HypercubeRamsey.S04.gadgetPower β γ n := rfl
  have hsdef : s = S - 1 := rfl
  have hmdef : m = HypercubeRamsey.S04.specialNum β γ n := rfl
  have hmprod : HypercubeRamsey.S04.specialNum β γ n = m := rfl
  have hmLt : m < n := by simpa [hmdef] using hmStrict
  have hmLe : m ≤ n := hmLt.le
  have hmnBlocks : G * s * ℓ ≤ n := by
    change m ≤ n
    exact hmLe
  have hSlarge : 128 ≤ S := by
    have hscale := HypercubeRamsey.Lane_q_s04_gadget.gadgetPower_ge_scale n hω (by omega)
    exact_mod_cast hpowSlarge.trans hscale
  have hS100 : 100 ≤ S := le_trans (by norm_num) hSlarge
  have hSeven : Even S := HypercubeRamsey.Lane_q_s04_gadget.gadgetPower_even n
  have hsCast : (s : ℝ) = (S : ℝ) - 1 := by
    rw [hsdef, Nat.cast_sub (by omega : 1 ≤ S)]
    norm_num
  have hlogS := HypercubeRamsey.Lane_q_s04_gadget.log_power_le_chunk S s hSlarge hsdef
  have hGfloor : (n : ℝ) ^ (γ - ω) < (G : ℝ) + 1 := by
    simpa [G, HypercubeRamsey.S04.gadgetNum] using
      (Nat.lt_floor_add_one ((n : ℝ) ^ (γ - ω)))
  have hGlow : (9 / 10 : ℝ) * (n : ℝ) ^ (γ - ω) ≤ (G : ℝ) := by
    nlinarith [hGfloor, hpowGlarge]
  have hSscale : (n : ℝ) ^ (2 * ω) ≤ (S : ℝ) := by
    simpa [S] using HypercubeRamsey.Lane_q_s04_gadget.gadgetPower_ge_scale n hω (by omega)
  have hsLow : (9 / 10 : ℝ) * (n : ℝ) ^ (2 * ω) ≤ (s : ℝ) := by
    rw [hsCast]
    nlinarith [hpowSlarge, hSscale]
  have hpowProduct :
      (n : ℝ) ^ (γ - ω) * (n : ℝ) ^ (2 * ω) = (n : ℝ) ^ (γ + ω) := by
    rw [← Real.rpow_add hnrealPos]
    congr 1
    ring
  have hchunks : (81 / 100 : ℝ) * (n : ℝ) ^ (γ + ω) ≤
      (G : ℝ) * (s : ℝ) := by
    calc
      (81 / 100 : ℝ) * (n : ℝ) ^ (γ + ω) =
          ((9 / 10 : ℝ) * (n : ℝ) ^ (γ - ω)) *
            ((9 / 10 : ℝ) * (n : ℝ) ^ (2 * ω)) := by
              calc
                (81 / 100 : ℝ) * (n : ℝ) ^ (γ + ω) =
                    (9 / 10 : ℝ) * (9 / 10 : ℝ) *
                      ((n : ℝ) ^ (γ - ω) * (n : ℝ) ^ (2 * ω)) := by rw [hpowProduct]; ring
                _ = ((9 / 10 : ℝ) * (n : ℝ) ^ (γ - ω)) *
                    ((9 / 10 : ℝ) * (n : ℝ) ^ (2 * ω)) := by ring
      _ ≤ (G : ℝ) * (s : ℝ) :=
        mul_le_mul hGlow hsLow (by positivity) (by positivity)
  have hlog32 : (1 / 3 : ℝ) ≤ Real.log ((3 : ℝ) / 2) := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ) / 3)
    have hinv : Real.log ((2 : ℝ) / 3) = -Real.log ((3 : ℝ) / 2) := by
      have heq : (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ := by norm_num
      rw [heq, Real.log_inv]
    nlinarith
  let x := (n : ℝ) ^ (γ + ω)
  have hx : 0 ≤ x := by positivity
  have hSpos : 0 < (S : ℝ) := by
    exact_mod_cast HypercubeRamsey.S04.gadgetPower_pos β γ n
  have hleafTail := HypercubeRamsey.Lane_q_s04_gadget.leaf_choice_tail
    S G s x hSpos hlogS hlog32 hx (by simpa [x, Nat.cast_mul] using hchunks)
  let coords : Finset (Fin n) :=
    HypercubeRamsey.Lane_q_s04_gadget.firstCoordinates n m
  have hcoordsCard : coords.card = m := by
    calc
      coords.card = Fintype.card {i : Fin n // i ∈ coords} := (Fintype.card_coe coords).symm
      _ = Fintype.card (Fin m) := Fintype.card_congr
        (HypercubeRamsey.Lane_q_s04_gadget.firstCoordinatesEquiv hmLe).symm
      _ = m := Fintype.card_fin _
  have hcoordsLt : coords.card < n := by simpa [hcoordsCard] using hmLt
  let A : Finset (∀ i : {q : Fin n // q ∈ coords}, Bool) :=
    Finset.univ.filter fun z => ∃ a : Fin G → Fin S, ∀ b : Fin G × Fin s,
      if b.2 ∈ (κ b.1).2 then
        (a b.1).val * S + S / 2 <
          HypercubeRamsey.Lane_q_s04_gadget.clippedBlockWeight S ℓ
            ((HypercubeRamsey.Lane_q_s04_gadget.gadgetFirstBlocksEquiv hmnBlocks z) b)
      else
        HypercubeRamsey.Lane_q_s04_gadget.clippedBlockWeight S ℓ
          ((HypercubeRamsey.Lane_q_s04_gadget.gadgetFirstBlocksEquiv hmnBlocks z) b) ≤
          (a b.1).val * S + S / 2
  have hAcount := HypercubeRamsey.Lane_q_s04_gadget.keyFiber_all_leaf_constraints_card_le
    κ hmnNat S hSdef hS100 hSeven
  have hAcard : (A.card : ℝ) ≤ Real.exp (-x / 10) * (2 : ℝ) ^ m := by
    calc
      (A.card : ℝ) ≤ (S : ℝ) ^ G * ((2 : ℝ) / 3) ^ (G * s) * (2 : ℝ) ^ m := by
        simpa [A, G, s, ℓ, m, coords, hmprod, Finset.mem_filter, Finset.mem_univ,
          mul_assoc] using hAcount
      _ ≤ Real.exp (-x / 10) * (2 : ℝ) ^ m := by
        have hmul := mul_le_mul_of_nonneg_right hleafTail (by positivity :
          0 ≤ (2 : ℝ) ^ m)
        simpa [mul_assoc] using hmul
  have hEventEven := HypercubeRamsey.Lane_q_s04_gadget.evenProjection_event_card
    coords hcoordsLt A
  have hEventOdd := HypercubeRamsey.Lane_q_s04_gadget.oddProjection_event_card
    coords hcoordsLt A
  let E := (HypercubeRamsey.evenRoleSet n).filter fun v : CubeVertex n =>
    (fun i : {q : Fin n // q ∈ coords} => v i.1) ∈ A
  let O := (Finset.univ \ HypercubeRamsey.evenRoleSet n).filter
    fun v : CubeVertex n => (fun i : {q : Fin n // q ∈ coords} => v i.1) ∈ A
  have hsubE :
      ((HypercubeRamsey.evenRoleSet n).filter fun v : CubeVertex n =>
        key β γ n v = κ) ⊆ E := by
    intro v hv
    have hw := HypercubeRamsey.Lane_q_s04_gadget.keyFiber_key_satisfies_leaf_constraints
      κ hmnNat S hSdef v ((Finset.mem_filter.mp hv).2)
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hv).1, ?_⟩
    · change (fun i : {q : Fin n // q ∈ coords} => v i.1) ∈ A
      simpa [A, G, s, ℓ, coords, hmnBlocks, Finset.mem_filter, Finset.mem_univ] using hw
  have hsubO :
      ((Finset.univ \ HypercubeRamsey.evenRoleSet n).filter fun v : CubeVertex n =>
        key β γ n v = κ) ⊆ O := by
    intro v hv
    have hw := HypercubeRamsey.Lane_q_s04_gadget.keyFiber_key_satisfies_leaf_constraints
      κ hmnNat S hSdef v ((Finset.mem_filter.mp hv).2)
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hv).1, ?_⟩
    · change (fun i : {q : Fin n // q ∈ coords} => v i.1) ∈ A
      simpa [A, G, s, ℓ, coords, hmnBlocks, Finset.mem_filter, Finset.mem_univ] using hw
  have hmPos : 0 < n := by omega
  have hRoleCardEven : (Fintype.card (EvenRole n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
    have hp := HypercubeRamsey.parity_class_card hmPos
    have heq : Fintype.card (EvenRole n) = (HypercubeRamsey.evenRoleSet n).card := by
      simpa [EvenRole, HypercubeRamsey.evenRoleSet] using
        (Fintype.card_coe (HypercubeRamsey.evenRoleSet n))
    rw [heq]
    exact_mod_cast hp.1
  have hRoleCardOdd : (Fintype.card (OddRole n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
    have hp := HypercubeRamsey.parity_class_card hmPos
    have heq : Fintype.card (OddRole n) =
        (Finset.univ \ HypercubeRamsey.evenRoleSet n).card := by
      simpa [OddRole, HypercubeRamsey.evenRoleSet] using
        (Fintype.card_coe (Finset.univ \ HypercubeRamsey.evenRoleSet n))
    rw [heq]
    exact_mod_cast hp.2
  have hEventEvenReal : (E.card : ℝ) =
      (A.card : ℝ) * (2 : ℝ) ^ (n - m - 1) := by
    have h := hEventEven
    rw [hcoordsCard] at h
    exact_mod_cast h
  have hEventOddReal : (O.card : ℝ) =
      (A.card : ℝ) * (2 : ℝ) ^ (n - m - 1) := by
    have h := hEventOdd
    rw [hcoordsCard] at h
    exact_mod_cast h
  have hPowParity := HypercubeRamsey.Lane_q_s04_gadget.pow_two_partition_mul m n hmLt
  have hEvenBound :
      ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) ≤
        Real.exp (-x / 10) * Fintype.card (EvenRole n) := by
    calc
      ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) =
          ((HypercubeRamsey.evenRoleSet n).filter fun v : CubeVertex n =>
            key β γ n v = κ).card := by
              exact_mod_cast HypercubeRamsey.Lane_q_s04_gadget.evenRole_filter_card_eq_key_filter κ
      _ ≤ (E.card : ℝ) := by exact_mod_cast Finset.card_le_card hsubE
      _ = (A.card : ℝ) * (2 : ℝ) ^ (n - m - 1) := hEventEvenReal
      _ ≤ (Real.exp (-x / 10) * (2 : ℝ) ^ m) * (2 : ℝ) ^ (n - m - 1) :=
        mul_le_mul_of_nonneg_right hAcard (by positivity)
      _ = Real.exp (-x / 10) * (2 : ℝ) ^ (n - 1) := by
        rw [mul_assoc, hPowParity]
      _ = Real.exp (-x / 10) * Fintype.card (EvenRole n) := by rw [hRoleCardEven]
  have hOddBound :
      ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) ≤
        Real.exp (-x / 10) * Fintype.card (OddRole n) := by
    calc
      ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) =
          ((Finset.univ \ HypercubeRamsey.evenRoleSet n).filter fun v : CubeVertex n =>
            key β γ n v = κ).card := by
              exact_mod_cast HypercubeRamsey.Lane_q_s04_gadget.oddRole_filter_card_eq_key_filter κ
      _ ≤ (O.card : ℝ) := by exact_mod_cast Finset.card_le_card hsubO
      _ = (A.card : ℝ) * (2 : ℝ) ^ (n - m - 1) := hEventOddReal
      _ ≤ (Real.exp (-x / 10) * (2 : ℝ) ^ m) * (2 : ℝ) ^ (n - m - 1) :=
        mul_le_mul_of_nonneg_right hAcard (by positivity)
      _ = Real.exp (-x / 10) * (2 : ℝ) ^ (n - 1) := by
        rw [mul_assoc, hPowParity]
      _ = Real.exp (-x / 10) * Fintype.card (OddRole n) := by rw [hRoleCardOdd]
  change ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) ≤
      Real.exp (-(n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10) *
        Fintype.card (EvenRole n) ∧
    ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) ≤
      Real.exp (-(n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10) *
        Fintype.card (OddRole n)
  constructor
  · simpa [x, ω] using hEvenBound
  · simpa [x, ω] using hOddBound

/-- D4.3/L4.1d (04:145–162): independent tags `tag κ ∼ ρ`; at a fixed label the normalized parity average is a
sum of independent terms `α_κ N μ_{tag κ}(x) ≤ exp(-n^{γ+ω}/10 + 3n^β/2)` (`KeyFiber` and the width `sX ≤ 3n^β/2`;
on the odd side `sY + 1 ≤ 3n^γ/2 + 1`) with mean at most `K`; bounded-summand concentration bounds a deviation `K`
by `exp(-Ω(exp(c n^{γ+ω})))`, and a union over the `2N ≤ 2n2^n` labels leaves an assignment with both averages at
most `2K`. -/
theorem tag_exists (β γ K : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyFiber β γ n →
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (ρ : FinProb M.ι), N ≤ n * 2 ^ n →
        Balanced ρ M.μ M.ν K → ∃ tag : Key β γ n → M.ι, TagBal M tag (2 * K) := by
  exact HypercubeRamsey.Lane_q_s04_gadget.tag_exists_bound β γ K hβ hβγ hγ hK

end HypercubeRamsey.S04
