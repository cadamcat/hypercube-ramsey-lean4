import HypercubeRamsey.Framework.Props
import HypercubeRamsey.S04.Lemma41
import HypercubeRamsey.S03.Mixtures
import HypercubeRamsey.S03.Stabilization

/-!
# Shared interfaces consumed by Section 8

These declarations are the checked interfaces requested from the common framework. The shared implementation
can replace their placeholder proofs when the Section 4 and Section 3 lanes are integrated.
-/

namespace HypercubeRamsey

/-- SHARED: L3.3a (03:70–80), balanced mixture in pair form. -/
theorem L3_3a_consumed (κ : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop)
    (X Y : Finset (Fin N)) (Q : PairProp)
    (hκ : 0 < κ)
    (hA : AvailableAt κ Q.toPatch n N E X Y) :
    ∃ M : TagMix N, M.Balanced (4 / κ) ∧
      ∀ i, 0 < M.Λ i →
        (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧ Q n N E (M.μ i) (M.ν i) := by
  classical
  have hzero : (∅ : Finset (Fin N)).card = 0 := Finset.card_empty
  have hzeroBound : ((∅ : Finset (Fin N)).card : ℝ) ≤ κ * N := by
    rw [hzero]
    simpa using mul_nonneg hκ.le (Nat.cast_nonneg N)
  obtain ⟨A₀, B₀, hAB₀, hA₀, hB₀⟩ := hA ∅ ∅ hzeroBound hzeroBound
  change ∃ μ ν : Law N, μ.SupportedIn A₀ ∧ ν.SupportedIn B₀ ∧ Q n N E μ ν at hAB₀
  obtain ⟨μ₀, ν₀, _, _, _⟩ := hAB₀
  have hN : 0 < N := by
    by_contra hN
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    have hsum : (0 : ℝ) = 1 := by simpa using μ₀.sum_eq_one
    exact zero_ne_one hsum
  let I := {p : Finset (Fin N) × Finset (Fin N) //
    (p.1.card : ℝ) ≤ κ * N ∧ (p.2.card : ℝ) ≤ κ * N}
  have hmenu : ∀ i : I, ∃ p : Law N × Law N,
      p.1.SupportedIn (X \ i.1.1) ∧ p.2.SupportedIn (Y \ i.1.2) ∧
        Q n N E p.1 p.2 := by
    intro i
    obtain ⟨A, B, hAB, hAsub, hBsub⟩ := hA i.1.1 i.1.2 i.2.1 i.2.2
    change ∃ μ ν : Law N, μ.SupportedIn A ∧ ν.SupportedIn B ∧ Q n N E μ ν at hAB
    obtain ⟨μ, ν, hμA, hνB, hQ⟩ := hAB
    refine ⟨(μ, ν), ?_, ?_, hQ⟩
    · intro x hx
      apply hμA x
      intro hxA
      exact hx (hAsub hxA)
    · intro y hy
      apply hνB y
      intro hyB
      exact hy (hBsub hyB)
  let p : I → Law N × Law N := fun i => Classical.choose (hmenu i)
  have hp (i : I) :
      (p i).1.SupportedIn (X \ i.1.1) ∧
      (p i).2.SupportedIn (Y \ i.1.2) ∧ Q n N E (p i).1 (p i).2 :=
    Classical.choose_spec (hmenu i)
  let μ : I → Law N := fun i => (p i).1
  let ν : I → Law N := fun i => (p i).2
  have hmenuAvail : ∀ RX RY : Finset (Fin N),
      (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
      ∃ i : I, (∀ x ∈ RX, (μ i).w x = 0) ∧ (∀ y ∈ RY, (ν i).w y = 0) := by
    intro RX RY hRX hRY
    let i : I := ⟨(RX, RY), hRX, hRY⟩
    refine ⟨i, ?_, ?_⟩
    · intro x hx
      exact (hp i).1 x (by simp [i, hx])
    · intro y hy
      exact (hp i).2.1 y (by simp [i, hy])
  obtain ⟨t, ht0, htSum, htX, htY⟩ :=
    balanced_mixture hN μ ν κ hκ hmenuAvail
  let M : TagMix N := {
    ι := I
    Λ := t
    Λ_nonneg := ht0
    Λ_sum := htSum
    μ := μ
    ν := ν
  }
  refine ⟨M, ?_, ?_⟩
  · constructor
    · intro x
      calc
        (N : ℝ) * ∑ i, M.Λ i * (M.μ i).w x ≤
            (N : ℝ) * (4 / (κ * N)) :=
          mul_le_mul_of_nonneg_left (htX x) (by exact_mod_cast hN.le)
        _ = 4 / κ := by
          have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
          field_simp
    · intro y
      calc
        (N : ℝ) * ∑ i, M.Λ i * (M.ν i).w y ≤
            (N : ℝ) * (4 / (κ * N)) :=
          mul_le_mul_of_nonneg_left (htY y) (by exact_mod_cast hN.le)
        _ = 4 / κ := by
          have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
          field_simp
  · intro i hi
    have hs := hp i
    constructor
    · intro x hx
      exact hs.1 x (by
        intro hxTrim
        exact hx (Finset.mem_sdiff.mp hxTrim).1)
    constructor
    · intro y hy
      exact hs.2.1 y (by
        intro hyTrim
        exact hy (Finset.mem_sdiff.mp hyTrim).1)
    · exact hs.2.2

/-- SHARED: L4.1 (04:9–16), bias versus purity in the consumed form. -/
theorem L4_1_consumed (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ H > (0 : ℝ), ∀ h' : ℝ, 0 < h' → h' ≤ H → ∀ T : Stage,
      Available T (PBias (pw β) (pw γ) h').toPatch →
      EventuallyAbsent T (PPure β γ h').toPatch → False :=
  L4_1 β γ hβ hβγ hγ

end HypercubeRamsey
