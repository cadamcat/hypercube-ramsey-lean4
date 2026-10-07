import HypercubeRamsey.PartC.Tiling

namespace HypercubeRamsey.S13

open Classical

theorem nat_le_two_pow (j : ℕ) : j ≤ 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ j := one_le_pow₀ (by decide)
      omega

theorem biasWitness_mono {κ : CConsts} {T : Stage} {k : ℕ}
    {RX RX' RY RY' : Finset (Fin (T.S.N k))}
    (hX : RX ⊆ RX') (hY : RY ⊆ RY') {b : ℕ}
    (h : BiasWitness κ T k RX RY b) : BiasWitness κ T k RX' RY' b := by
  rcases h with ⟨U, V, hU, hV, hUR, hVR, hcardU, hcardV, hden⟩
  exact ⟨U, V, hU, hV, hUR.trans hX, hVR.trans hY, hcardU, hcardV, hden⟩

theorem cluScaleWitness_mono {κ : CConsts} {T : Stage} {k : ℕ}
    {RX RX' RY RY' : Finset (Fin (T.S.N k))}
    (hX : RX ⊆ RX') (hY : RY ⊆ RY') {b : ℕ} {o : Bool}
    (h : CluScaleWitness κ T k RX RY b o) :
    CluScaleWitness κ T k RX' RY' b o := by
  rcases h with ⟨U, hU, m, B, hUside, hBside, hdisj, hsize, hUcard, hBcard, hcorr⟩
  refine ⟨U, hU, m, B, ?_, ?_, hdisj, hsize, hUcard, hBcard, hcorr⟩
  · intro x hx
    by_cases ho : o
    · have hx' : x ∈ RY := by simpa [ho] using hUside hx
      simpa [ho] using hY hx'
    · have hx' : x ∈ RX := by simpa [ho] using hUside hx
      simpa [ho] using hX hx'
  · intro j
    intro x hx
    by_cases ho : o
    · have hx' : x ∈ RX := by simpa [ho] using hBside j hx
      simpa [ho] using hX hx'
    · have hx' : x ∈ RY := by simpa [ho] using hBside j hx
      simpa [ho] using hY hx'

@[simp] theorem pairCorr_transpose {N : ℕ} (E : Fin N → Fin N → Prop) (o : Bool)
    (μ : Law N) (y y' : Fin N) :
    pairCorr (transposeRel E) o μ y y' = pairCorr E (!o) μ y y' := by
  cases o <;> simp [pairCorr, corr, fv, hit, Hits, transposeRel]

end HypercubeRamsey.S13
