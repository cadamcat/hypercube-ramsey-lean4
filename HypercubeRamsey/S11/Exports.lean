import HypercubeRamsey.S10.ClusterExclusion
import HypercubeRamsey.S07.InitialDiscrepancy
import HypercubeRamsey.S11.Nodes

/-!
The Section 11 stage-level exports. The first theorem assembles the one-shot embedding with the selected
discrepancy and cluster absence; the second combines Section 9's regime exclusions with that theorem.
-/

namespace HypercubeRamsey.S11

open HypercubeRamsey Filter

private theorem eventually_pw_mono {a b : ℚ} (hab : a ≤ b) :
    ∀ᶠ t : ℝ in atTop, pw a t ≤ pw b t := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simpa [pw] using Real.rpow_le_rpow_of_exponent_le ht (by exact_mod_cast hab)

private theorem eventually_lw_mono {a b : ℚ} (hab : a ≤ b) :
    ∀ᶠ t : ℝ in atTop, lw a t ≤ lw b t := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) ht

private theorem eventually_error_mono (h₀ : ℚ) (ε : ℝ) (h : (h₀ : ℝ) > 1 - ε) :
    ∀ᶠ t : ℝ in atTop, t ^ (-(h₀ : ℝ)) ≤ t ^ (-1 + ε) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)

/-- P11.1 (11:4–6): exclude the linear-budget jump. -/
theorem not_linear_jump (T : Stage) (hT : StabilizedOn T FamB)
    (hNoHdag : ¬ HdagLtOne T.swap) (hZero : HLdagZero T) : False := by
  obtain ⟨η₀, hη₀, hInit⟩ := HypercubeRamsey.S07.initial_discrepancy_proof
  let ζ : ℚ := 1 / 100
  let ζR : ℝ := (ζ : ℝ)
  let cap : ℝ := min η₀ ζR / 2000
  have hcap : 0 < cap := by
    dsimp [cap, ζR, ζ]
    positivity
  obtain ⟨δ, hδposR, hδcap⟩ :=
    exists_rat_btwn (show (0 : ℝ) < cap by exact hcap)
  have hδpos : 0 < δ := by exact_mod_cast hδposR
  have hminle : min η₀ ζR ≤ 1 := le_trans (min_le_right _ _) (by norm_num [ζR, ζ])
  have hclusterBound : min (min η₀ ζR) 1 / 2000 = cap := by
    simp [cap, min_eq_left hminle]
  have hδcluster : (δ : ℝ) < min (min η₀ ζR) 1 / 2000 := by
    rw [hclusterBound]
    exact hδcap
  have hcapSmall : cap ≤ (1 : ℝ) / 200000 := by
    change min η₀ ζR / 2000 ≤ (1 : ℝ) / 200000
    calc
      min η₀ ζR / 2000 ≤ ζR / 2000 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = (1 : ℝ) / 200000 := by norm_num
  have hδSmall : (δ : ℝ) < (1 : ℝ) / 200000 := lt_of_lt_of_le hδcap hcapSmall
  have hδOneR : (δ : ℝ) < 1 := lt_trans hδSmall (by norm_num)
  have hδOne : δ < 1 := by exact_mod_cast hδOneR
  have hδCore : (δ : ℝ) < 1 / 20000 := lt_trans hδSmall (by norm_num)
  have hζpos : 0 < ζ := by norm_num [ζ]
  have hDinit := hInit T hT
  have hclusters : ∀ G : Colour,
      EventuallyAbsent T (PCluster G ζR (δ : ℝ)) ∧
      EventuallyAbsent T.swap (PCluster G ζR (δ : ℝ)) := by
    intro G
    exact HypercubeRamsey.S10.eventual_cluster_absence_proof η₀ hη₀ T hT hDinit G ζ δ
      hζpos hδpos hδcluster
  obtain ⟨x₀, hx₀, hx₀1, hDisc, hAvail⟩ :=
    linear_jump_selection T hT hNoHdag hZero δ hδpos hδOne
  let P : PatchProp :=
    (PBias (pw ((1 / 100 : ℚ) : ℝ)) (lw ((1 / 100 : ℚ) : ℝ)) ((1 / 200 : ℚ) : ℝ)).toPatch
  let side : ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Finset (Fin N) → Finset (Fin N) → Prop :=
    fun n N E X Y =>
      DiscOne E X Y ((n : ℝ) ^ ((1 : ℝ) - (δ : ℝ) / 16))
        ((n : ℝ) ^ (x₀ : ℝ)) ((n : ℝ) ^ (-(19 : ℝ) / 20)) ∧
      (∀ (G : Colour) A B, A ⊆ X → B ⊆ Y →
        (A, B) ∉ PCluster G ζR (δ : ℝ) n N E) ∧
      (∀ (G : Colour) A B, A ⊆ Y → B ⊆ X →
        (A, B) ∉ PCluster G ζR (δ : ℝ) n N (transposeRel E))
  have hDiscEvent : ∀ᶠ k in atTop,
      DiscOne (T.S.E k) (T.X k) (T.Y k)
        ((T.S.n k : ℝ) ^ ((1 : ℝ) - (δ : ℝ) / 16))
        ((T.S.n k : ℝ) ^ (x₀ : ℝ)) ((T.S.n k : ℝ) ^ (-(19 : ℝ) / 20)) :=
    (discAt_iff_eventually_discOne T
      (pw ((1 : ℝ) - (δ : ℝ) / 16)) (pw x₀)
      (fun n => n ^ (-(19 : ℝ) / 20))).mp hDisc
  have hClusterEvent : ∀ᶠ k in atTop,
      (∀ (G : Colour) A B, A ⊆ T.X k → B ⊆ T.Y k →
        (A, B) ∉ PCluster G ζR (δ : ℝ) (T.S.n k) (T.S.N k) (T.S.E k)) ∧
      (∀ (G : Colour) A B, A ⊆ T.Y k → B ⊆ T.X k →
        (A, B) ∉ PCluster G ζR (δ : ℝ) (T.S.n k) (T.S.N k)
          (transposeRel (T.S.E k))) := by
    have hTrue := hclusters true
    have hFalse := hclusters false
    filter_upwards [hTrue.1, hTrue.2, hFalse.1, hFalse.2] with k hAt hBt hAf hBf
    constructor
    · intro G A B hAX hBY hmem
      cases G with
      | false => exact hAf A B hmem ⟨hAX, hBY⟩
      | true => exact hAt A B hmem ⟨hAX, hBY⟩
    · intro G A B hAY hBX hmem
      cases G with
      | false => exact hBf A B hmem ⟨hAY, hBX⟩
      | true => exact hBt A B hmem ⟨hAY, hBX⟩
  have hside : ∀ᶠ k in atTop,
      side (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k) := by
    filter_upwards [hDiscEvent, hClusterEvent] with k hD hC
    exact ⟨hD, hC.1, hC.2⟩
  have hshot : ∀ κ > (0 : ℝ), ∃ n₀ C₀,
      ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
        LargeAt n₀ C₀ n N →
        side n N E X Y →
        AvailableAt κ P n N E X Y → CubeAt n N E := by
    intro κ hκ
    obtain ⟨n₀, C₀, hcore⟩ :=
      linear_jump_embedding_core δ x₀ (1 / 200) κ hδpos hδCore hx₀ hx₀1
        (by norm_num) (by norm_num) hκ
    refine ⟨n₀, C₀, ?_⟩
    intro n N E X Y hLarge hS hAvailable
    exact hcore n N E X Y hLarge hS.1 hS.2.1 hS.2.2 hAvailable
  have hnot : ¬ Available T P :=
    not_available_of_oneShot' (T := T) (P := P) side hside hshot
  exact hnot hAvail

private theorem exists_linear_discrepancy (T : Stage) (hT : StabilizedOn T FamB)
    (hNoHdag : ¬ HdagLtOne T) (hNoHdagSwap : ¬ HdagLtOne T.swap)
    (h₀ : ℚ) (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1) :
    ∃ x α : ℚ, 0 < x ∧ 0 < α ∧
      DiscAt T (pw x) (lw α) (fun n => n ^ (-(h₀ : ℝ))) := by
  by_cases hExists : ∃ x α : ℚ, 0 < x ∧ x < 1 ∧ 0 < α ∧ ¬ AvL T x α h₀
  · obtain ⟨x, α, hx, hx1, hα, hUnavailable⟩ := hExists
    exact ⟨x, α, hx, hα,
      disc_of_unavailable_linear T hT x α h₀ hx hx1 hα hh₀ hUnavailable⟩
  · have hall : ∀ x α : ℚ, 0 < x → x < 1 → 0 < α → AvL T x α h₀ := by
      intro x α hx hx1 hα
      by_contra hUnavailable
      exact hExists ⟨x, α, hx, hx1, hα, hUnavailable⟩
    have hLin : HLdagLtOne T := by
      refine ⟨h₀, hh₀1, ?_⟩
      intro x α hx hx1 hα
      exact hall x α hx hx1 hα
    have hZero : HLdagZero T := by
      classical
      by_contra hNotZero
      exact not_intermediate_linear T hT hNoHdag hLin hNotZero
    exact (not_linear_jump T hT hNoHdagSwap hZero).elim

private theorem swap_swap_eq (T : Stage) : T.swap.swap = T := by
  cases T
  rfl

/-- C11.4 (11:397–403): the remaining deep regime, in both orientations. This has exactly the type of
`HypercubeRamsey.S11.remaining_deep_regime_proof` in `Interface.lean`.
-/
theorem remaining_deep_regime_proof (T : Stage) (hT : StabilizedOn T FamB) :
    ∀ ε : ℝ, 0 < ε → ∃ x α : ℚ, 0 < x ∧ 0 < α ∧
      DiscAt T (pw x) (lw α) (fun n => n ^ (-1 + ε)) ∧
      DiscAt T.swap (pw x) (lw α) (fun n => n ^ (-1 + ε)) := by
  intro ε hε
  let ε₀ := min ε (1 / 2 : ℝ)
  have hε₀pos : 0 < ε₀ := by dsimp [ε₀]; exact lt_min hε (by norm_num)
  have hε₀lt : ε₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨h₀, hh₀lo, hh₀hi⟩ :=
    exists_rat_btwn (show (1 : ℝ) - ε₀ < 1 by linarith)
  have hh₀pos : 0 < h₀ := by
    have hhalf : (1 : ℝ) / 2 ≤ 1 - ε₀ := by
      dsimp [ε₀]
      have hmin : min ε (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
      linarith
    have h₀posR : (0 : ℝ) < (h₀ : ℝ) := by linarith [hhalf, hh₀lo]
    exact_mod_cast h₀posR
  have hh₀lt : h₀ < 1 := by exact_mod_cast hh₀hi
  have hh₀ε : (1 : ℝ) - ε < (h₀ : ℝ) := by
    have hminε : ε₀ ≤ ε := by dsimp [ε₀]; exact min_le_left _ _
    exact lt_of_le_of_lt (by linarith) hh₀lo
  have hTswap : StabilizedOn T.swap FamB := hT.swap FamB_swap
  have hNoT : ¬ HdagLtOne T := not_HdagLtOne T hT
  have hNoTswap : ¬ HdagLtOne T.swap := not_HdagLtOne T.swap hTswap
  have hNoSwapSwap : ¬ HdagLtOne T.swap.swap := by
    rw [swap_swap_eq T]
    exact hNoT
  obtain ⟨x₁, α₁, hx₁, hα₁, hD₁⟩ :=
    exists_linear_discrepancy T hT hNoT hNoTswap h₀ hh₀pos hh₀lt
  obtain ⟨x₂, α₂, hx₂, hα₂, hD₂⟩ :=
    exists_linear_discrepancy T.swap hTswap hNoTswap hNoSwapSwap h₀ hh₀pos hh₀lt
  let x := min x₁ x₂
  let α := min α₁ α₂
  have hx : 0 < x := by dsimp [x]; exact lt_min hx₁ hx₂
  have hα : 0 < α := by dsimp [α]; exact lt_min hα₁ hα₂
  have hD₁' : DiscAt T (pw x) (lw α) (fun n => n ^ (-(h₀ : ℝ))) :=
    DiscAt.mono hD₁ (eventually_pw_mono (min_le_left _ _))
      (eventually_lw_mono (min_le_left _ _)) (Filter.Eventually.of_forall (fun _ => le_rfl))
  have hD₂' : DiscAt T.swap (pw x) (lw α) (fun n => n ^ (-(h₀ : ℝ))) :=
    DiscAt.mono hD₂ (eventually_pw_mono (min_le_right _ _))
      (eventually_lw_mono (min_le_right _ _)) (Filter.Eventually.of_forall (fun _ => le_rfl))
  have herr : ∀ᶠ n : ℝ in atTop, n ^ (-(h₀ : ℝ)) ≤ n ^ (-1 + ε) :=
    eventually_error_mono h₀ ε hh₀ε
  have hD₁'' : DiscAt T (pw x) (lw α) (fun n => n ^ (-1 + ε)) :=
    DiscAt.mono hD₁' (Filter.Eventually.of_forall (fun _ => le_rfl))
      (Filter.Eventually.of_forall (fun _ => le_rfl)) herr
  have hD₂'' : DiscAt T.swap (pw x) (lw α) (fun n => n ^ (-1 + ε)) :=
    DiscAt.mono hD₂' (Filter.Eventually.of_forall (fun _ => le_rfl))
      (Filter.Eventually.of_forall (fun _ => le_rfl)) herr
  exact ⟨x, α, hx, hα, hD₁'', hD₂''⟩

end HypercubeRamsey.S11
