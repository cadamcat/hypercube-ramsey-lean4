import HypercubeRamsey.S05.Even_load_selection_sol_s05_even
import HypercubeRamsey.S05.Even_load_scopes_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem center_dimension_lower : (n : ℝ) ≤ X.St.d + (n : ℝ) ^ (1 / 2 : ℝ) := by
  let D := (Finset.univ.biUnion X.g.coarseChunks) ∪ (Finset.univ.biUnion X.g.fineChunks)
  have hcard : n ≤ D.card + X.g.residual.card := by
    have hh := Finset.card_union_le D X.g.residual
    change ((Finset.univ.biUnion X.g.coarseChunks) ∪ (Finset.univ.biUnion X.g.fineChunks) ∪ X.g.residual).card ≤ _ at hh
    rw [X.g.chunks_cover, Finset.card_univ, Fintype.card_fin] at hh
    exact hh
  have hres : X.g.residual.card ≤ X.St.d := by
    have hh := Fintype.card_le_of_injective X.St.resCoord X.St.resCoord_injective
    simpa only [Fintype.card_coe, Fintype.card_fin] using hh
  have hcardR : (n : ℝ) ≤ (D.card : ℝ) + X.g.residual.card := by exact_mod_cast hcard
  have hresR : (X.g.residual.card : ℝ) ≤ X.St.d := by exact_mod_cast hres
  have hocc : (D.card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := X.g.occupied_sublinear
  linarith

theorem eventual_linear_height_geometry (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G), X.p = p → ∀ h : X.HeightChoice5,
      (1 / 2 : ℝ) * n ≤ X.St.d ∧ (X.St.d : ℝ) ≤ 2 * n ∧
        (canonicalHeightRegime p).ok n X.St.d h.hp.r := by
  let g : ℝ := 1 - 4 * p.rho
  have hg : 0 < g := by dsimp [g]; linarith [p.hrho.2]
  have hroot : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hroot.eventually_ge_atTop (max 6 (1 / g)),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / p.rho),
    Filter.eventually_ge_atTop (602 : ℕ)] with n hnroot hnρ hn
  intro N E G X hp h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hroot0 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hn0.le _
  have hroot6 : (6 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := (le_max_left _ _).trans hnroot
  have hrootg : 1 / g ≤ (n : ℝ) ^ (1 / 2 : ℝ) := (le_max_right _ _).trans hnroot
  have hsquare : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = n := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hsmall6 : 6 * (n : ℝ) ^ (1 / 2 : ℝ) ≤ n := by
    have hh := mul_le_mul_of_nonneg_right hroot6 hroot0
    rwa [hsquare] at hh
  have hsmallg : (n : ℝ) ^ (1 / 2 : ℝ) ≤ g * n := by
    have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hg).mp hrootg) hroot0
    nlinarith [hsquare]
  have hlo := center_dimension_lower X
  have hup := X.St.dimension_upper
  have hn602 : (602 : ℝ) ≤ n := by exact_mod_cast hn
  have hdlo : (1 / 2 : ℝ) * n ≤ X.St.d := by linarith
  have hdup : (X.St.d : ℝ) ≤ 2 * n := by linarith
  refine ⟨hdlo, hdup, ?_⟩
  have hrupper : (h.hp.r : ℝ) ≤ p.rho * n := by
    change (⌊X.p.rho * n⌋₊ : ℝ) ≤ _
    rw [hp]
    exact Nat.floor_le (mul_nonneg p.hrho.1.le hn0.le)
  have hrlower : p.rho * n - 1 ≤ (h.hp.r : ℝ) := by
    change _ ≤ (⌊X.p.rho * n⌋₊ : ℝ)
    rw [hp]
    have hh := Nat.lt_floor_add_one (p.rho * (n : ℝ))
    linarith
  have hρn : 2 ≤ p.rho * n := by
    have hh := (div_le_iff₀ p.hrho.1).mp hnρ
    nlinarith
  change (p.rho / 4) * (X.St.d : ℝ) ≤ (h.hp.r : ℝ) ∧ 4 * h.hp.r ≤ X.St.d
  constructor
  · have hh := mul_le_mul_of_nonneg_left hdup (div_nonneg p.hrho.1.le (by norm_num : (0 : ℝ) ≤ 4))
    linarith
  · have hrd : 4 * (h.hp.r : ℝ) ≤ X.St.d := by
      dsimp only [g] at hsmallg
      nlinarith
    exact_mod_cast hrd

end
end HypercubeRamsey.Lane_sol_s05_even
