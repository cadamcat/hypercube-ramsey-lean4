import HypercubeRamsey.S15.Defs
import HypercubeRamsey.S15.Needs
import HypercubeRamsey.S05.Clock_q_s05_even
import HypercubeRamsey.Framework.FinProbLemmas

/-! Geometric and locality adapters for the direct assignment proof lane. -/

namespace HypercubeRamsey.Lane_q_s15_direct

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open Filter
open scoped BigOperators

noncomputable def star {T : Stage} {k : ℕ}
    (a : S15.EvenPosition T k) :
    Finset (S15.OddPosition T k) :=
  Finset.univ.filter fun b => S15.Adjacent a b

theorem star_card_le {T : Stage} {k : ℕ}
    (a : S15.EvenPosition T k) :
    (star a).card ≤ T.S.n k := by
  classical
  let S := star a
  have himage : S.card = (S.image Subtype.val).card :=
    (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hsub : S.image Subtype.val ⊆
      Finset.univ.filter fun v : CubeVertex (T.S.n k) =>
        (cube (T.S.n k)).Adj a.1 v := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  calc
    S.card = (S.image Subtype.val).card := himage
    _ ≤ (Finset.univ.filter fun v : CubeVertex (T.S.n k) =>
        (cube (T.S.n k)).Adj a.1 v).card := Finset.card_le_card hsub
    _ ≤ T.S.n k := cube_adj_neighbors_card_le (T.S.n k) a.1

noncomputable def starIncidence {T : Stage} {k : ℕ}
    (b : S15.OddPosition T k) :
    Finset (S15.EvenPosition T k) :=
  Finset.univ.filter fun a => b ∈ star a

theorem star_incidence_card_le {T : Stage} {k : ℕ}
    (b : S15.OddPosition T k) :
    (starIncidence b).card ≤ T.S.n k := by
  classical
  let S := starIncidence b
  have himage : S.card = (S.image Subtype.val).card :=
    (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hsub : S.image Subtype.val ⊆
      Finset.univ.filter fun v : CubeVertex (T.S.n k) =>
        (cube (T.S.n k)).Adj b.1 v := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨a, ha, rfl⟩
    have hb : b ∈ star a := (Finset.mem_filter.mp ha).2
    have hab : S15.Adjacent a b := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩
  calc
    S.card = (S.image Subtype.val).card := himage
    _ ≤ (Finset.univ.filter fun v : CubeVertex (T.S.n k) =>
        (cube (T.S.n k)).Adj b.1 v).card := Finset.card_le_card hsub
    _ ≤ T.S.n k := cube_adj_neighbors_card_le (T.S.n k) b.1

theorem prefixLeaf_card_le {n ell : ℕ} (w : CubeVertex n) (hle : ell ≤ n) :
    (Finset.univ.filter fun v : CubeVertex n => v ∈ prefixLeaf ell w).card ≤ 2 ^ (n - ell) := by
  classical
  let A : Finset (CubeVertex n) := Finset.univ.filter fun v => v ∈ prefixLeaf ell w
  let tail (v : CubeVertex n) : CubeVertex (n - ell) := fun j =>
    v ⟨ell + j.val, by have := j.isLt; omega⟩
  have hcoord : Set.InjOn tail A := by
    intro v hv z hz hEq
    have hvpre : ∀ j : Fin n, j.val < ell → v j = w j :=
      (Finset.mem_filter.mp hv).2
    have hzpre : ∀ j : Fin n, j.val < ell → z j = w j :=
      (Finset.mem_filter.mp hz).2
    funext j
    by_cases hpre : j.val < ell
    · exact (hvpre j hpre).trans (hzpre j hpre).symm
    · let q : Fin (n - ell) := ⟨j.val - ell, by omega⟩
      have hidx : (⟨ell + q.val, by omega⟩ : Fin n) = j := Fin.ext (by simp [q]; omega)
      have htail : v ⟨ell + q.val, by omega⟩ = z ⟨ell + q.val, by omega⟩ := by
        exact congrFun hEq q
      simpa only [hidx] using htail
  have himage : A.card = (A.image tail).card :=
    (Finset.card_image_of_injOn hcoord).symm
  calc
    A.card = (A.image tail).card := himage
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ (n - ell) := by simp [CubeVertex]

theorem patchAssignment_count_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    (Finset.univ.filter fun b : S15.OddPosition T k =>
      S15.patchAt PT hPT b.1 = i).card ≤ 2 ^ (T.S.n k - (PT.tiling.P i).ℓ) := by
  classical
  let S := Finset.univ.filter fun b : S15.OddPosition T k => S15.patchAt PT hPT b.1 = i
  have himage : S.card = (S.image Subtype.val).card :=
    (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hsub : S.image Subtype.val ⊆
      Finset.univ.filter fun v : CubeVertex (T.S.n k) => v ∈ PT.tiling.leaf i := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
    have hpatch : S15.patchAt PT hPT b.1 = i := (Finset.mem_filter.mp hb).2
    have hleaf : b.1 ∈ PT.tiling.leaf (S15.patchAt PT hPT b.1) := by
      exact (Classical.choose_spec (hPT.tiling_valid.prefix_complete b.1)).1
    simpa [hpatch] using hleaf
  calc
    S.card = (S.image Subtype.val).card := himage
    _ ≤ (Finset.univ.filter fun v : CubeVertex (T.S.n k) => v ∈ PT.tiling.leaf i).card :=
      Finset.card_le_card hsub
    _ ≤ 2 ^ (T.S.n k - (PT.tiling.P i).ℓ) := by
      have hh := hPT.tiling_valid.prefix_internal_length
      have hℓ : (PT.tiling.P i).ℓ ≤ Finset.univ.sup
          (fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) :=
        Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
          (Finset.mem_univ i)
      have hlen : (PT.tiling.P i).ℓ ≤ T.S.n k := by omega
      exact prefixLeaf_card_le (PT.tiling.w i) hlen

theorem evenPatchPositions_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    (S15.evenPatchPositions PT.tiling i).card ≤
      2 ^ (T.S.n k - (PT.tiling.P i).ℓ) := by
  classical
  let S := S15.evenPatchPositions PT.tiling i
  have himage : S.card = (S.image Subtype.val).card :=
    (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hsub : S.image Subtype.val ⊆
      Finset.univ.filter fun v : CubeVertex (T.S.n k) => v ∈ PT.tiling.leaf i := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨a, ha, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  have hh := hPT.tiling_valid.prefix_internal_length
  have hℓ : (PT.tiling.P i).ℓ ≤ Finset.univ.sup
      (fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) :=
    Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
      (Finset.mem_univ i)
  have hlen : (PT.tiling.P i).ℓ ≤ T.S.n k := by omega
  calc
    S.card = (S.image Subtype.val).card := himage
    _ ≤ (Finset.univ.filter fun v : CubeVertex (T.S.n k) => v ∈ PT.tiling.leaf i).card :=
      Finset.card_le_card hsub
    _ ≤ 2 ^ (T.S.n k - (PT.tiling.P i).ℓ) := by
      exact prefixLeaf_card_le (PT.tiling.w i) hlen

theorem evenPatchPositions_ratio_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    ((S15.evenPatchPositions PT.tiling i).card : ℝ) / ((PT.tiling.P i).M : ℝ) ≤
      800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k := by
  classical
  have hcountNat := evenPatchPositions_card_le PT hPT i
  have hcount : ((S15.evenPatchPositions PT.tiling i).card : ℝ) ≤
      (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ) := by exact_mod_cast hcountNat
  have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hSpos : (0 : ℝ) < PT.tiling.S := by
    have h := hPT.tiling_valid.S_lower
    nlinarith
  have hMpos : (0 : ℝ) < (PT.tiling.P i).M := by
    have hcard : 0 < ((PT.tiling.P i).X.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1)
    rw [(PT.tiling.P i).cardX] at hcard
    exact hcard
  have hh := hPT.tiling_valid.prefix_internal_length
  have hℓ : (PT.tiling.P i).ℓ ≤ Finset.univ.sup
      (fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) :=
    Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
      (Finset.mem_univ i)
  have hℓn : (PT.tiling.P i).ℓ ≤ T.S.n k := by omega
  have hpow : (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ) *
      (2 : ℝ) ^ (PT.tiling.P i).ℓ = (2 : ℝ) ^ (T.S.n k) := by
    rw [← pow_add]
    congr 1
    omega
  have hpowℓ : (0 : ℝ) < (2 : ℝ) ^ (PT.tiling.P i).ℓ := by positivity
  have hdyad := hPT.tiling_valid.dyadic_mass_upper i
  have hinv : (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) =
      1 / (2 : ℝ) ^ (PT.tiling.P i).ℓ := by simp [zpow_neg]
  rw [hinv] at hdyad
  have hdyad' : (PT.tiling.S : ℝ) < 2 * (PT.tiling.P i).M *
      (2 : ℝ) ^ (PT.tiling.P i).ℓ := by
    have hmul := mul_lt_mul_of_pos_right hdyad hSpos
    have hdiv : (PT.tiling.S : ℝ) / (2 : ℝ) ^ (PT.tiling.P i).ℓ <
        2 * (PT.tiling.P i).M := by
      calc
        _ = (1 / (2 : ℝ) ^ (PT.tiling.P i).ℓ) * PT.tiling.S := by ring
        _ < (2 * (PT.tiling.P i).M / PT.tiling.S) * PT.tiling.S := hmul
        _ = 2 * (PT.tiling.P i).M := by field_simp [ne_of_gt hSpos]
    exact (div_lt_iff₀ hpowℓ).mp hdiv
  have hrecip : 1 / (PT.tiling.P i).M <
      2 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S := by
    apply (div_lt_div_iff₀ hMpos hSpos).2
    nlinarith [hdyad']
  have hscaled :
      ((S15.evenPatchPositions PT.tiling i).card : ℝ) / ((PT.tiling.P i).M : ℝ) ≤
        2 * (2 : ℝ) ^ (T.S.n k) / PT.tiling.S := by
    calc
      ((S15.evenPatchPositions PT.tiling i).card : ℝ) / ((PT.tiling.P i).M : ℝ) =
          (S15.evenPatchPositions PT.tiling i).card * (1 / (PT.tiling.P i).M) := by ring
      _ ≤ (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ) *
            (1 / (PT.tiling.P i).M) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ ≤ (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ) *
            (2 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S) :=
        mul_le_mul_of_nonneg_left hrecip.le (by positivity)
      _ = 2 * (2 : ℝ) ^ (T.S.n k) / PT.tiling.S := by
        calc
          _ = 2 * ((2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ) *
                (2 : ℝ) ^ (PT.tiling.P i).ℓ) / PT.tiling.S := by ring
          _ = 2 * (2 : ℝ) ^ (T.S.n k) / PT.tiling.S := by rw [hpow]
  have hSlower : (1 / 400 : ℝ) * T.S.N k ≤ PT.tiling.S :=
    hPT.tiling_valid.S_lower
  have hSratio : (1 : ℝ) / PT.tiling.S ≤ 400 / (T.S.N k : ℝ) := by
    apply (div_le_div_iff₀ hSpos hNpos).2
    nlinarith [hSlower]
  have hfinal : 2 * (2 : ℝ) ^ (T.S.n k) / PT.tiling.S ≤
      800 * (2 : ℝ) ^ (T.S.n k) / (T.S.N k : ℝ) := by
    calc
      _ = (2 * (2 : ℝ) ^ (T.S.n k)) * (1 / PT.tiling.S) := by ring
      _ ≤ (2 * (2 : ℝ) ^ (T.S.n k)) * (400 / (T.S.N k : ℝ)) :=
        mul_le_mul_of_nonneg_left hSratio (by positivity)
      _ = 800 * (2 : ℝ) ^ (T.S.n k) / (T.S.N k : ℝ) := by ring
  exact hscaled.trans hfinal

theorem direct_marginal_column_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (y : Fin (T.S.N k)) :
    (∑ b : S15.OddPosition T k, (S15.lawAtOdd PT hPT b).w y) ≤
      8800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k := by
  classical
  let patch (b : S15.OddPosition T k) : Fin PT.tiling.m :=
    S15.patchAt PT hPT b.1
  by_cases hex : ∃ i, y ∈ (PT.tiling.P i).Y
  · obtain ⟨i₀, hy₀⟩ := hex
    let S₀ := Finset.univ.filter fun b : S15.OddPosition T k => patch b = i₀
    have hzero (b : S15.OddPosition T k) (hb : patch b ≠ i₀) :
        (S15.lawAtOdd PT hPT b).w y = 0 := by
      apply hPT.law_supported (patch b)
      intro hy
      have hne : i₀ ≠ patch b := fun heq => hb heq.symm
      have hdisj := hPT.tiling_valid.patch_Y_disjoint i₀ (patch b) hne
      exact Finset.disjoint_left.mp hdisj hy₀ hy
    have hsumEq :
        (∑ b : S15.OddPosition T k, (S15.lawAtOdd PT hPT b).w y) =
          ∑ b ∈ S₀, (S15.lawAtOdd PT hPT b).w y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S₀)
      intro b hb hnot
      apply hzero
      intro heq
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
    have hsumCap :
        (∑ b ∈ S₀, (S15.lawAtOdd PT hPT b).w y) ≤
          (S₀.card : ℝ) * (11 / (PT.tiling.P i₀).M) := by
      calc
        _ ≤ ∑ b ∈ S₀, (11 / (PT.tiling.P i₀).M : ℝ) := by
          apply Finset.sum_le_sum
          intro b hb
          have hp : patch b = i₀ := (Finset.mem_filter.mp hb).2
          simpa [S15.lawAtOdd, patch, hp] using hPT.law_cap i₀ y
        _ = (S₀.card : ℝ) * (11 / (PT.tiling.P i₀).M) := by simp
    have hcountNat : S₀.card ≤ 2 ^ (T.S.n k - (PT.tiling.P i₀).ℓ) := by
      simpa [S₀, patch] using patchAssignment_count_le PT hPT i₀
    have hcount : (S₀.card : ℝ) ≤ (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ) := by
      exact_mod_cast hcountNat
    have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    have hSpos : (0 : ℝ) < PT.tiling.S := by
      have h := hPT.tiling_valid.S_lower
      nlinarith
    have hMpos : (0 : ℝ) < (PT.tiling.P i₀).M := by
      have hcard : 0 < ((PT.tiling.P i₀).X.card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i₀).1)
      rw [(PT.tiling.P i₀).cardX] at hcard
      exact hcard
    have hℓn : (PT.tiling.P i₀).ℓ ≤ T.S.n k := by
      have hh := hPT.tiling_valid.prefix_internal_length
      have hℓ : (PT.tiling.P i₀).ℓ ≤ Finset.univ.sup
          (fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) :=
        Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
          (Finset.mem_univ i₀)
      omega
    have hpowℓ : (0 : ℝ) < (2 : ℝ) ^ (PT.tiling.P i₀).ℓ := by positivity
    have hpow : (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ) *
        (2 : ℝ) ^ (PT.tiling.P i₀).ℓ = (2 : ℝ) ^ (T.S.n k) := by
      rw [← pow_add, Nat.sub_add_cancel hℓn]
    have hdyad := hPT.tiling_valid.dyadic_mass_upper i₀
    have hinv : (2 : ℝ) ^ (-((PT.tiling.P i₀).ℓ : ℤ)) =
        1 / (2 : ℝ) ^ (PT.tiling.P i₀).ℓ := by
      simp [zpow_neg]
    rw [hinv] at hdyad
    have hdyad' :
        (PT.tiling.S : ℝ) < 2 * (PT.tiling.P i₀).M * (2 : ℝ) ^ (PT.tiling.P i₀).ℓ := by
      have hmul := mul_lt_mul_of_pos_right hdyad hSpos
      have hdiv : (1 / (2 : ℝ) ^ (PT.tiling.P i₀).ℓ) * PT.tiling.S <
          2 * (PT.tiling.P i₀).M := by
        calc
          (1 / (2 : ℝ) ^ (PT.tiling.P i₀).ℓ) * PT.tiling.S <
              (2 * (PT.tiling.P i₀).M / PT.tiling.S) * PT.tiling.S := hmul
          _ = 2 * (PT.tiling.P i₀).M := by field_simp [ne_of_gt hSpos]
      have hdiv' : (PT.tiling.S : ℝ) / (2 : ℝ) ^ (PT.tiling.P i₀).ℓ <
          2 * (PT.tiling.P i₀).M := by simpa [div_eq_mul_inv, mul_comm] using hdiv
      exact (div_lt_iff₀ hpowℓ).mp hdiv'
    have hrecip : 1 / (PT.tiling.P i₀).M <
        2 * (2 : ℝ) ^ (PT.tiling.P i₀).ℓ / PT.tiling.S := by
      apply (div_lt_div_iff₀ hMpos hSpos).2
      nlinarith [hdyad']
    have hscaled :
        11 * (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ) /
            (PT.tiling.P i₀).M <
          22 * (2 : ℝ) ^ (T.S.n k) / PT.tiling.S := by
      calc
        11 * (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ) /
            (PT.tiling.P i₀).M =
            11 * (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ) *
              (1 / (PT.tiling.P i₀).M) := by ring
        _ < 11 * (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ) *
              (2 * (2 : ℝ) ^ (PT.tiling.P i₀).ℓ / PT.tiling.S) :=
          mul_lt_mul_of_pos_left hrecip (by positivity)
        _ = 22 * ((2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ) *
              (2 : ℝ) ^ (PT.tiling.P i₀).ℓ) / PT.tiling.S := by ring
        _ = 22 * (2 : ℝ) ^ (T.S.n k) / PT.tiling.S := by rw [hpow]
    have hSlower : (1 / 400 : ℝ) * T.S.N k ≤ PT.tiling.S :=
      hPT.tiling_valid.S_lower
    have hSratio : (1 : ℝ) / PT.tiling.S ≤ 400 / (T.S.N k : ℝ) := by
      apply (div_le_div_iff₀ hSpos hNpos).2
      nlinarith [hSlower]
    have hfinal : 22 * (2 : ℝ) ^ (T.S.n k) / PT.tiling.S ≤
        8800 * (2 : ℝ) ^ (T.S.n k) / (T.S.N k : ℝ) := by
      calc
        _ = (22 * (2 : ℝ) ^ (T.S.n k)) * (1 / PT.tiling.S) := by ring
        _ ≤ (22 * (2 : ℝ) ^ (T.S.n k)) * (400 / (T.S.N k : ℝ)) :=
          mul_le_mul_of_nonneg_left hSratio (by positivity)
        _ = 8800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k := by ring
    calc
      _ = ∑ b ∈ S₀, (S15.lawAtOdd PT hPT b).w y := hsumEq
      _ ≤ (S₀.card : ℝ) * (11 / (PT.tiling.P i₀).M) := hsumCap
      _ ≤ 11 * (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ) /
            (PT.tiling.P i₀).M := by
          have hfactor : (0 : ℝ) ≤ 11 / (PT.tiling.P i₀).M := by positivity
          calc
            _ = (S₀.card : ℝ) * (11 / (PT.tiling.P i₀).M) := rfl
            _ ≤ ((2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ)) *
                  (11 / (PT.tiling.P i₀).M) :=
                mul_le_mul_of_nonneg_right hcount hfactor
            _ = 11 * (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i₀).ℓ) /
                  (PT.tiling.P i₀).M := by ring
      _ ≤ 22 * (2 : ℝ) ^ (T.S.n k) / PT.tiling.S := hscaled.le
      _ ≤ 8800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k := hfinal
  · have hzero (b : S15.OddPosition T k) : (S15.lawAtOdd PT hPT b).w y = 0 := by
      apply hPT.law_supported (S15.patchAt PT hPT b.1)
      intro hy
      exact hex ⟨S15.patchAt PT hPT b.1, hy⟩
    have hpos : 0 ≤ 8800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k := by positivity
    simpa [hzero] using hpos

theorem direct_atom_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (b : S15.OddPosition T k)
    (y : Fin (T.S.N k)) :
    (S15.lawAtOdd PT hPT b).w y ≤
      8800 * (2 : ℝ) ^ ((PT.tiling.P (S15.patchAt PT hPT b.1)).ℓ) / T.S.N k := by
  classical
  let i := S15.patchAt PT hPT b.1
  have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hSpos : (0 : ℝ) < PT.tiling.S := by
    have h := hPT.tiling_valid.S_lower
    nlinarith
  have hMpos : (0 : ℝ) < (PT.tiling.P i).M := by
    have hcard : 0 < ((PT.tiling.P i).X.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1)
    rw [(PT.tiling.P i).cardX] at hcard
    exact hcard
  have hpowℓ : (0 : ℝ) < (2 : ℝ) ^ (PT.tiling.P i).ℓ := by positivity
  have hdyad := hPT.tiling_valid.dyadic_mass_upper i
  have hinv : (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) =
      1 / (2 : ℝ) ^ (PT.tiling.P i).ℓ := by simp [zpow_neg]
  rw [hinv] at hdyad
  have hdyad' : (PT.tiling.S : ℝ) < 2 * (PT.tiling.P i).M *
      (2 : ℝ) ^ (PT.tiling.P i).ℓ := by
    have hmul := mul_lt_mul_of_pos_right hdyad hSpos
    have hdiv : (PT.tiling.S : ℝ) / (2 : ℝ) ^ (PT.tiling.P i).ℓ <
        2 * (PT.tiling.P i).M := by
      calc
        _ = (1 / (2 : ℝ) ^ (PT.tiling.P i).ℓ) * PT.tiling.S := by ring
        _ < (2 * (PT.tiling.P i).M / PT.tiling.S) * PT.tiling.S := hmul
        _ = 2 * (PT.tiling.P i).M := by field_simp [ne_of_gt hSpos]
    exact (div_lt_iff₀ hpowℓ).mp hdiv
  have hrecip : 1 / (PT.tiling.P i).M <
      2 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S := by
    apply (div_lt_div_iff₀ hMpos hSpos).2
    nlinarith [hdyad']
  have hsum : (11 : ℝ) / ((PT.tiling.P i).M : ℝ) <
      22 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S := by
    calc
      _ = 11 * (1 / ((PT.tiling.P i).M : ℝ)) := by ring
      _ < 11 * (2 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S) :=
        mul_lt_mul_of_pos_left hrecip (by norm_num)
      _ = 22 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S := by ring
  have hSlower : (1 / 400 : ℝ) * T.S.N k ≤ PT.tiling.S :=
    hPT.tiling_valid.S_lower
  have hSratio : (1 : ℝ) / PT.tiling.S ≤ 400 / (T.S.N k : ℝ) := by
    apply (div_le_div_iff₀ hSpos hNpos).2
    nlinarith [hSlower]
  have hfinal : 22 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S ≤
      8800 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / (T.S.N k : ℝ) := by
    calc
      _ = (22 * (2 : ℝ) ^ (PT.tiling.P i).ℓ) * (1 / PT.tiling.S) := by ring
      _ ≤ (22 * (2 : ℝ) ^ (PT.tiling.P i).ℓ) * (400 / (T.S.N k : ℝ)) :=
        mul_le_mul_of_nonneg_left hSratio (by positivity)
      _ = 8800 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / (T.S.N k : ℝ) := by ring
  calc
    (S15.lawAtOdd PT hPT b).w y ≤ (11 : ℝ) / ((PT.tiling.P i).M : ℝ) := by
      simpa [S15.lawAtOdd, i] using hPT.law_cap i y
    _ ≤ 22 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S := hsum.le
    _ ≤ 8800 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / (T.S.N k : ℝ) := hfinal

theorem eventually_two_pow_tail (A : ℝ) (hA : 0 < A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      8800 * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) ≤ (n : ℝ) ^ (-A) := by
  have hb : 0 < Real.log 2 / 2 := by positivity
  have hlim : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ A * Real.exp (-(Real.log 2 / 2) * (n : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A (Real.log 2 / 2) hb).comp
      tendsto_natCast_atTop_atTop
  have hsmall := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8800))
  filter_upwards [hsmall, Filter.eventually_gt_atTop 0] with n hn hnpos
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hpow : (n : ℝ) ^ A * (n : ℝ) ^ (-A) = 1 := by
    rw [← Real.rpow_add hnreal]
    simp
  have hmul := mul_le_mul_of_nonneg_right hn.le (Real.rpow_nonneg hnreal.le (-A))
  have hexp : Real.exp (-(Real.log 2 / 2) * (n : ℝ)) ≤
      (1 / 8800) * (n : ℝ) ^ (-A) := by
    calc
      Real.exp (-(Real.log 2 / 2) * (n : ℝ)) =
          ((n : ℝ) ^ A * (n : ℝ) ^ (-A)) *
            Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by rw [hpow]; ring
      _ = ((n : ℝ) ^ A * Real.exp (-(Real.log 2 / 2) * (n : ℝ))) *
            (n : ℝ) ^ (-A) := by ring
      _ ≤ (1 / 8800) * (n : ℝ) ^ (-A) := hmul
  nlinarith

theorem weight_le_pr {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop)
    (x : α) (hA : A x) : P.w x ≤ P.pr A := by
  classical
  unfold FinProb.pr
  have hx : x ∈ Finset.univ.filter A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩
  calc
    P.w x ≤ ∑ y ∈ Finset.univ.filter A, P.w y :=
      Finset.single_le_sum (fun y hy => P.nonneg y) hx
    _ = ∑ y, if A y then P.w y else 0 := by rw [Finset.sum_filter]

theorem row_mass_failure_subset {cross bulk row threshold : ℝ}
    (hrow : row = cross * bulk) (hsmall : threshold ≤ 1 / 10)
    (hbad : row < 1 / 2) :
    |cross - 1| > threshold ∨ (9 / 10 ≤ cross ∧ bulk < 3 / 4) := by
  by_cases hcrossBad : |cross - 1| > threshold
  · exact Or.inl hcrossBad
  · right
    have hclose : |cross - 1| ≤ threshold := le_of_not_gt hcrossBad
    have hcrossLower : 9 / 10 ≤ cross := by
      rw [abs_le] at hclose
      linarith
    have hbulkLt : bulk < 5 / 9 := by
      by_contra hnot
      have hbulkLower : 5 / 9 ≤ bulk := le_of_not_gt hnot
      have hprod : 1 / 2 ≤ cross * bulk := by
        calc
          (1 / 2 : ℝ) = (9 / 10) * (5 / 9) := by norm_num
          _ ≤ (9 / 10) * bulk :=
            mul_le_mul_of_nonneg_left hbulkLower (by norm_num)
          _ ≤ cross * bulk :=
            mul_le_mul_of_nonneg_right hcrossLower (le_trans (by norm_num) hbulkLower)
      rw [hrow] at hbad
      linarith
    exact ⟨hcrossLower, lt_of_lt_of_le hbulkLt (by norm_num)⟩

theorem finLaw_pr_union {α : Type*} [Fintype α] (P : FinLaw α) (A B : α → Prop) :
    P.pr (fun x => A x ∨ B x) ≤ P.pr A + P.pr B := by
  classical
  let C : α → Prop := fun x => A x ∨ B x
  letI : DecidablePred A := fun x => Classical.propDecidable (A x)
  letI : DecidablePred B := fun x => Classical.propDecidable (B x)
  letI : DecidablePred C := fun x => Classical.propDecidable (C x)
  change P.pr C ≤ P.pr A + P.pr B
  unfold FinLaw.pr
  calc
    (∑ x, if C x then P.w x else 0) ≤
        ∑ x, ((if A x then P.w x else 0) + (if B x then P.w x else 0)) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hA : A x <;> by_cases hB : B x <;> simp [C, hA, hB, P.nonneg x]
    _ = (∑ x, if A x then P.w x else 0) + ∑ x, if B x then P.w x else 0 := by
      rw [Finset.sum_add_distrib]

theorem finLaw_pr_mono {α : Type*} [Fintype α] (P : FinLaw α)
    (A B : α → Prop) (hAB : ∀ x, A x → B x) : P.pr A ≤ P.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro x hx
  by_cases hA : A x
  · have hB := hAB x hA
    simp [hA, hB]
  · by_cases hB : B x <;> simp [hA, hB, P.nonneg x]

theorem finProb_expect_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (P : FinProb α) (f : α → ι → ℝ) :
    P.expect (fun x => ∑ i, f x i) = ∑ i, P.expect (fun x => f x i) := by
  classical
  unfold FinProb.expect
  change (∑ x, P.w x * ∑ i, f x i) = ∑ i, ∑ x, P.w x * f x i
  calc
    (∑ x, P.w x * ∑ i, f x i) = ∑ x, ∑ i, P.w x * f x i := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ x, P.w x * f x i := Finset.sum_comm

theorem exists_support_outside {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) (hpr : P.pr A < 1) :
    ∃ x, P.w x ≠ 0 ∧ ¬A x := by
  classical
  by_contra h
  have hzero : ∀ x, ¬A x → P.w x = 0 := by
    intro x hx
    by_contra hne
    exact h ⟨x, hne, hx⟩
  have hprEq : P.pr A = 1 := by
    unfold FinProb.pr
    calc
      (∑ x, if A x then P.w x else 0) = ∑ x, P.w x := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hA : A x
        · simp [hA]
        · simp [hA, hzero x hA]
      _ = 1 := P.sum_eq_one
  linarith

theorem eventually_nat_sq_over_two_pow_lt_one :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ 2 / (2 : ℝ) ^ n < 1 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlim : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ (2 : ℝ) * Real.exp (-(Real.log 2) * (n : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (Real.log 2) hlog).comp
      tendsto_natCast_atTop_atTop
  have hsmall := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall] with n hn
  have hpowInv : (2 : ℝ) ^ (-(n : ℝ)) = 1 / (2 : ℝ) ^ n :=
    by simpa [Real.rpow_natCast, one_div] using
      (Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)) (n : ℝ))
  have hexp : Real.exp (-(Real.log 2) * (n : ℝ)) = (2 : ℝ) ^ (-(n : ℝ)) := by
    calc
      Real.exp (-(Real.log 2) * (n : ℝ)) =
          Real.exp (-(n : ℝ) * Real.log 2) := by congr 1 <;> ring
      _ = (2 : ℝ) ^ (-(n : ℝ)) :=
        by
          rw [show -(n : ℝ) * Real.log 2 = Real.log 2 * (-(n : ℝ)) by ring]
          exact (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-(n : ℝ))).symm
  have hEq : (n : ℝ) ^ 2 / (2 : ℝ) ^ n =
      (n : ℝ) ^ (2 : ℝ) * Real.exp (-(Real.log 2) * (n : ℝ)) := by
    calc
      (n : ℝ) ^ 2 / (2 : ℝ) ^ n = (n : ℝ) ^ 2 * ((2 : ℝ) ^ n)⁻¹ := by
        rw [div_eq_mul_inv]
      _ = (n : ℝ) ^ 2 * (2 : ℝ) ^ (-(n : ℝ)) := by
        simpa only [one_div] using congrArg (fun z : ℝ => (n : ℝ) ^ 2 * z) hpowInv.symm
      _ = (n : ℝ) ^ 2 * Real.exp (-(Real.log 2) * (n : ℝ)) := by rw [hexp]
      _ = (n : ℝ) ^ (2 : ℝ) * Real.exp (-(Real.log 2) * (n : ℝ)) := by
        simp [Real.rpow_natCast]
  simpa [hEq] using hn

theorem tiling_patch_count_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) : PT.tiling.m ≤ T.S.N k := by
  classical
  let f : Fin PT.tiling.m → Fin (T.S.N k) := fun i =>
    Classical.choose (hPT.tiling_valid.patch_nonempty i).1
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hdisj := hPT.tiling_valid.patch_X_disjoint i j hne
    have hi := Classical.choose_spec (hPT.tiling_valid.patch_nonempty i).1
    have hj := Classical.choose_spec (hPT.tiling_valid.patch_nonempty j).1
    have hji : f i ∈ (PT.tiling.P j).X := by simpa [hij] using hj
    exact (Finset.disjoint_left.mp hdisj) hi hji
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

theorem exists_support_all_below_of_sum_moment {α ι : Type*} [Fintype α] [Fintype ι]
    (P : FinProb α) (stats : ι → α → ℝ) (n : ℕ) (t : ℝ)
    (hn : 0 < n) (ht : 0 < t)
    (hstats : ∀ i x, 0 ≤ stats i x)
    (hmoment : P.expect (fun x => ∑ i, (stats i x) ^ n) < t ^ n) :
    ∃ x, P.w x ≠ 0 ∧ ∀ i, stats i x < t := by
  classical
  let total (x : α) := ∑ i, (stats i x) ^ n
  have htotal : ∀ x, 0 ≤ total x := by
    intro x
    unfold total
    apply Finset.sum_nonneg
    intro i hi
    exact pow_nonneg (hstats i x) n
  have hbad : P.pr (fun x => t ^ n ≤ total x) ≤ P.expect total / (t ^ n) :=
    FinProb.markov P total (t ^ n) htotal (pow_pos ht n)
  have hbadlt : P.pr (fun x => t ^ n ≤ total x) < 1 := by
    have hbound : P.expect total / (t ^ n) < 1 := (div_lt_one (pow_pos ht n)).2 hmoment
    exact lt_of_le_of_lt hbad hbound
  obtain ⟨x, hxw, hxgood⟩ :=
    exists_support_outside P (fun x => t ^ n ≤ total x) hbadlt
  refine ⟨x, hxw, ?_⟩
  intro i
  by_contra hnot
  have hle : t ≤ stats i x := le_of_not_gt hnot
  have hpowl : t ^ n ≤ (stats i x) ^ n :=
    pow_le_pow_left₀ ht.le hle n
  have hsum : (stats i x) ^ n ≤ total x := by
    unfold total
    exact Finset.single_le_sum (fun j hj => pow_nonneg (hstats j x) n)
      (Finset.mem_univ i)
  exact hxgood (le_trans hpowl hsum)

theorem row_failure_probability_le {α : Type*} [Fintype α]
    (P : FinLaw α) (cross bulk row threshold : α → ℝ) (δcross δbulk : ℝ)
    (hrow : ∀ x, row x = cross x * bulk x)
    (hsmall : ∀ x, threshold x ≤ 1 / 10)
    (hcross : P.pr (fun x => |cross x - 1| > threshold x) ≤ δcross)
    (hbulk : P.pr (fun x => 9 / 10 ≤ cross x ∧ bulk x < 3 / 4) ≤ δbulk) :
    P.pr (fun x => row x < 1 / 2) ≤ δcross + δbulk := by
  classical
  have hsub (x : α) (hx : row x < 1 / 2) :
      (|cross x - 1| > threshold x) ∨
        (9 / 10 ≤ cross x ∧ bulk x < 3 / 4) :=
    row_mass_failure_subset (hrow x) (hsmall x) hx
  calc
    P.pr (fun x => row x < 1 / 2) ≤
        P.pr (fun x => |cross x - 1| > threshold x ∨
          (9 / 10 ≤ cross x ∧ bulk x < 3 / 4)) :=
      finLaw_pr_mono P _ _ hsub
    _ ≤ P.pr (fun x => |cross x - 1| > threshold x) +
        P.pr (fun x => 9 / 10 ≤ cross x ∧ bulk x < 3 / 4) := finLaw_pr_union P _ _
    _ ≤ δcross + δbulk := add_le_add hcross hbulk

theorem prefix_ratio_le_exp {n ell N : ℕ} (hell : 2 * ell ≤ n)
    (hN : (2 : ℝ) ^ n ≤ N) :
    (2 : ℝ) ^ ell / N ≤ Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by
  have hℓn : ell ≤ n := by omega
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ n) hN
  have hpow : (2 : ℝ) ^ ell * (2 : ℝ) ^ (n - ell) = (2 : ℝ) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  have hquot : (2 : ℝ) ^ ell / (2 : ℝ) ^ n = 1 / (2 : ℝ) ^ (n - ell) := by
    field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact hpow
  have hminus :
      1 / (2 : ℝ) ^ (n - ell) = (2 : ℝ) ^ (-((n - ell : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((n - ell : ℕ) : ℝ)]
    simp [one_div]
  have hhalf : ((n - ell : ℕ) : ℝ) ≥ (n : ℝ) / 2 := by
    have hnat : n ≤ 2 * (n - ell) := by omega
    have hcast : (n : ℝ) ≤ 2 * ((n - ell : ℕ) : ℝ) := by exact_mod_cast hnat
    nlinarith
  have hmono : (2 : ℝ) ^ (-((n - ell : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hexp : (2 : ℝ) ^ (-((n : ℝ) / 2)) =
      Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    (2 : ℝ) ^ ell / N ≤ (2 : ℝ) ^ ell / (2 : ℝ) ^ n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hN
    _ = 1 / (2 : ℝ) ^ (n - ell) := hquot
    _ = (2 : ℝ) ^ (-((n - ell : ℕ) : ℝ)) := hminus
    _ ≤ (2 : ℝ) ^ (-((n : ℝ) / 2)) := hmono
    _ = Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := hexp

theorem highDirect_prefix_gain_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (hκ : κ.Admissible)
    (hmode : PT.tiling.mode = .highDirect) (i : Fin PT.tiling.m) :
    ((PT.tiling.P i).ℓ : ℝ) ≤ (PT.tiling.P i).g / (1000000 * κ.u) := by
  have hnotBound : PT.tiling.mode ≠ .bounded := by
    intro hb
    rw [hb] at hmode
    cases hmode
  rcases hPT.tiling_valid.allocation_bounds i with ⟨_, halloc⟩
  rcases halloc with hb | ⟨hℓ, hlog⟩
  · exact (hnotBound hb).elim
  have hgain : PT.tiling.gain i = (PT.tiling.P i).g / 1000 := by
    simp [HypercubeRamsey.Tiling.gain, hmode]
  rw [hgain] at hℓ
  have hℓ' : ((PT.tiling.P i).ℓ : ℝ) ≤
      (PT.tiling.P i).g / (1000000 * κ.u) := by
    calc
      ((PT.tiling.P i).ℓ : ℝ) ≤ ((PT.tiling.P i).g / 1000) / (1000 * κ.u) := hℓ
      _ = (PT.tiling.P i).g / (1000000 * κ.u) := by ring
  exact hℓ'

theorem highDirect_prefix_le_half {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (hκ : κ.Admissible)
    (hmode : PT.tiling.mode = .highDirect) (hn : 1 ≤ T.S.n k)
    (i : Fin PT.tiling.m) : 2 * (PT.tiling.P i).ℓ ≤ T.S.n k := by
  have hscale := hPT.tiling_valid.direct_scale_bound (Or.inr hmode) i
  have hℓ' := highDirect_prefix_gain_bound PT hPT hκ hmode i
  have hu : 1 ≤ κ.u := by
    have hlarge := hκ.u_rng.2
    omega
  have hmin1 := min_le_right κ.η0 (1 / 100 : ℝ)
  have hmin2 := min_le_right κ.xs (min κ.η0 (1 / 100 : ℝ))
  have hι : κ.ι / 2 ≤ 1 := by
    have hι0 := hκ.ι_rng.2
    nlinarith
  have hnR : (1 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hn
  have hg : (PT.tiling.P i).g ≤ (T.S.n k : ℝ) := by
    calc
      (PT.tiling.P i).g ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := hscale
      _ ≤ (T.S.n k : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnR hι
      _ = (T.S.n k : ℝ) := by rw [Real.rpow_one]
  have huCast : (1000000 : ℝ) ≤ 1000000 * κ.u := by
    exact_mod_cast (show 1000000 ≤ 1000000 * κ.u by omega)
  have hg0 : (0 : ℝ) ≤ (PT.tiling.P i).g := by positivity
  have hdiv : (PT.tiling.P i).g / (1000000 * (κ.u : ℝ)) ≤
      (PT.tiling.P i).g / (1000000 : ℝ) := by
    have hden : (0 : ℝ) < 1000000 * κ.u := by positivity
    have hmul := mul_le_mul_of_nonneg_left huCast hg0
    have hcross : (PT.tiling.P i).g * 1000000 ≤
        (PT.tiling.P i).g * (1000000 * (κ.u : ℝ)) := by nlinarith
    exact (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 1000000)).2 hcross
  have hℓn : ((PT.tiling.P i).ℓ : ℝ) ≤ (T.S.n k : ℝ) / 1000000 := by
    calc
      ((PT.tiling.P i).ℓ : ℝ) ≤ (PT.tiling.P i).g / (1000000 * (κ.u : ℝ)) := hℓ'
      _ ≤ (PT.tiling.P i).g / (1000000 : ℝ) := hdiv
      _ ≤ (T.S.n k : ℝ) / 1000000 :=
        div_le_div_of_nonneg_right hg (by norm_num)
  have hdouble : 2 * ((PT.tiling.P i).ℓ : ℝ) ≤ (T.S.n k : ℝ) := by
    nlinarith
  exact_mod_cast hdouble

theorem highDirect_cross_threshold_small {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      PT.tiling.mode = .highDirect → ∀ i : Fin PT.tiling.m,
        Real.exp (20 * (PT.tiling.P i).ℓ * bstar T k) - 1 ≤ 1 / 10 := by
  have hnPos : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    have hnNat : ∀ᶠ k in atTop, 1 ≤ T.S.n k :=
      T.S.n_tendsto.eventually (eventually_ge_atTop 1)
    filter_upwards [hnNat] with k hk
    exact_mod_cast hk
  have hsmall : ∀ᶠ k in atTop,
      (1 / 50000 : ℝ) * (T.S.n k : ℝ) ^ (-(0.95 : ℝ)) ≤ Real.log (11 / 10) := by
    have hlim := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.95)).comp
      (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    have hlim' := hlim.const_mul (1 / 50000 : ℝ)
    exact hlim'.eventually (Iic_mem_nhds (by
      simpa using Real.log_pos (by norm_num : (1 : ℝ) < 11 / 10)))
  filter_upwards [hnPos, hsmall] with k hn hsmall
  intro PT hPT hmode i
  have hprefix := highDirect_prefix_gain_bound PT hPT hκ hmode i
  have hscale := hPT.tiling_valid.direct_scale_bound (Or.inr hmode) i
  have hu : 1 ≤ κ.u := by
    have hlarge := hκ.u_rng.2
    omega
  have hιsmall : κ.ι / 2 ≤ 1 / 100 := by
    have hminA : min κ.η0 (0.01 : ℝ) ≤ 0.01 := min_le_right _ _
    have hmin : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ 0.01 :=
      le_trans (min_le_right _ _) hminA
    have hι := hκ.ι_rng.2
    linarith
  have huCast : (1 : ℝ) ≤ (κ.u : ℝ) := by exact_mod_cast hu
  have hden : (0 : ℝ) < 1000000 * (κ.u : ℝ) := by positivity
  have hℓbound : ((PT.tiling.P i).ℓ : ℝ) ≤
      (T.S.n k : ℝ) ^ (κ.ι / 2) / 1000000 := by
    have hfirst : (PT.tiling.P i).g / (1000000 * (κ.u : ℝ)) ≤
        (PT.tiling.P i).g / (1000000 : ℝ) := by
      apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 1000000)).2
      have hnonneg : (0 : ℝ) ≤ (PT.tiling.P i).g := by positivity
      have hdenle : (1000000 : ℝ) ≤ 1000000 * (κ.u : ℝ) := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hdenle hnonneg
      nlinarith
    calc
      ((PT.tiling.P i).ℓ : ℝ) ≤ (PT.tiling.P i).g / (1000000 * (κ.u : ℝ)) := hprefix
      _ ≤ (PT.tiling.P i).g / 1000000 := hfirst
      _ ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) / 1000000 :=
        div_le_div_of_nonneg_right hscale (by norm_num)
  have hbstar : bstar T k = (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) := by
    simp [bstar]
    norm_num
  have hnonnegPow : 0 ≤ (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) := by positivity
  have hcombine :
      ((T.S.n k : ℝ) ^ (κ.ι / 2) / 1000000) *
          (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) =
        (1 / 1000000 : ℝ) * (T.S.n k : ℝ) ^ (κ.ι / 2 - 0.96) := by
    calc
      ((T.S.n k : ℝ) ^ (κ.ι / 2) / 1000000) *
          (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) =
        (1 / 1000000 : ℝ) *
          ((T.S.n k : ℝ) ^ (κ.ι / 2) * (T.S.n k : ℝ) ^ (-(0.96 : ℝ))) := by ring
      _ = (1 / 1000000 : ℝ) * (T.S.n k : ℝ) ^ (κ.ι / 2 - 0.96) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < (T.S.n k : ℝ))]
        ring
  have hexp : κ.ι / 2 - 0.96 ≤ -(0.95 : ℝ) := by linarith
  have hpowmono : (T.S.n k : ℝ) ^ (κ.ι / 2 - 0.96) ≤
      (T.S.n k : ℝ) ^ (-(0.95 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn hexp
  have hscaled : (PT.tiling.P i).ℓ * bstar T k ≤
      (1 / 1000000 : ℝ) * (T.S.n k : ℝ) ^ (-(0.95 : ℝ)) := by
    calc
      (PT.tiling.P i).ℓ * bstar T k ≤
          ((T.S.n k : ℝ) ^ (κ.ι / 2) / 1000000) *
            (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) := by
        rw [hbstar]
        exact mul_le_mul_of_nonneg_right hℓbound hnonnegPow
      _ = (1 / 1000000 : ℝ) * (T.S.n k : ℝ) ^ (κ.ι / 2 - 0.96) := hcombine
      _ ≤ (1 / 1000000 : ℝ) * (T.S.n k : ℝ) ^ (-(0.95 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpowmono (by norm_num)
  have harg : 20 * (PT.tiling.P i).ℓ * bstar T k ≤ Real.log (11 / 10) := by
    calc
      20 * (PT.tiling.P i).ℓ * bstar T k =
          20 * ((PT.tiling.P i).ℓ * bstar T k) := by ring
      _ ≤ 20 * ((1 / 1000000 : ℝ) * (T.S.n k : ℝ) ^ (-(0.95 : ℝ))) :=
        mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ = (1 / 50000 : ℝ) * (T.S.n k : ℝ) ^ (-(0.95 : ℝ)) := by ring
      _ ≤ Real.log (11 / 10) := hsmall
  calc
    Real.exp (20 * (PT.tiling.P i).ℓ * bstar T k) - 1 ≤
        Real.exp (Real.log (11 / 10)) - 1 := by
      exact sub_le_sub_right (Real.exp_le_exp.mpr harg) 1
    _ = 1 / 10 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 11 / 10)]; norm_num

theorem directRowMass_dependsOn {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k)
    (ys ys' : S15.OddAssignment T k)
    (hys : ∀ b ∈ star a, ys b = ys' b) :
    S15.directRowMass PT hPT ys a = S15.directRowMass PT hPT ys' a := by
  classical
  have hcrossSubset : S15.crossingNeighbours PT hPT a ⊆ star a := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
  have hbulkSubset : S15.bulkNeighbours PT hPT a ⊆ star a := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
  have hfactor (b : S15.OddPosition T k) (hb : b ∈ star a) (x : Fin (T.S.N k)) :
      S15.directFactor PT hPT a ys b x = S15.directFactor PT hPT a ys' b x := by
    simp [S15.directFactor, hys b hb]
  have hcross : S15.directCrossingMass PT hPT ys a =
      S15.directCrossingMass PT hPT ys' a := by
    unfold S15.directCrossingMass
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact hfactor b (hcrossSubset hb) x
  have hpost (x : Fin (T.S.N k)) :
      S15.directPostCrossingWeight PT hPT ys a x =
        S15.directPostCrossingWeight PT hPT ys' a x := by
    unfold S15.directPostCrossingWeight
    rw [hcross]
    by_cases hm : 0 < S15.directCrossingMass PT hPT ys' a
    · simp [hm]
      apply congrArg (fun z : ℝ => z / S15.directCrossingMass PT hPT ys' a)
      apply congrArg (fun z : ℝ => S15.directBaseWeight PT hPT a x * z)
      apply Finset.prod_congr rfl
      intro b hb
      exact hfactor b (hcrossSubset hb) x
    · simp [hm]
  have hbulk : S15.directBulkMass PT hPT ys a = S15.directBulkMass PT hPT ys' a := by
    unfold S15.directBulkMass
    apply Finset.sum_congr rfl
    intro x hx
    rw [hpost]
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact hfactor b (hbulkSubset hb) x
  simp [S15.directRowMass, hcross, hbulk]

theorem directFactor_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k)
    (ys : S15.OddAssignment T k) (b : S15.OddPosition T k)
    (x : Fin (T.S.N k)) : 0 ≤ S15.directFactor PT hPT a ys b x := by
  unfold S15.directFactor S15.normalizedHit
  by_cases hd : 0 < deg (T.S.E k) PT.tiling.c (S15.lawAtOdd PT hPT b).w x
  · simp [hd, hit]
    positivity
  · simp [hd]

theorem directFactor_nonzero_hit {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k)
    (ys : S15.OddAssignment T k) (b : S15.OddPosition T k)
    (x : Fin (T.S.N k)) (hfactor : S15.directFactor PT hPT a ys b x ≠ 0) :
    Hits (T.S.E k) PT.tiling.c x (ys b) := by
  by_contra hnot
  unfold S15.directFactor at hfactor
  simp [S15.normalizedHit, HypercubeRamsey.hit, hnot] at hfactor

theorem directFactor_eq_one_add_acoef {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k)
    (ys : S15.OddAssignment T k) (b : S15.OddPosition T k) (x : Fin (T.S.N k))
    (π : Law (T.S.N k))
    (hπ : S15.lawAtOdd PT hPT b = π) :
    S15.directFactor PT hPT a ys b x =
      1 + S15.Needs.acoef (T.S.E k) PT.tiling.c π.w x (ys b) := by
  unfold S15.directFactor S15.normalizedHit S15.Needs.acoef
  rw [hπ]
  by_cases hd : 0 < deg (T.S.E k) PT.tiling.c π.w x
  · simp [hd]
  · simp [hd]

theorem directBulkMass_eq_centered_product {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k)
    (ys : S15.OddAssignment T k) (π : Law (T.S.N k))
    (hπ : ∀ b ∈ S15.bulkNeighbours PT hPT a, S15.lawAtOdd PT hPT b = π) :
    S15.directBulkMass PT hPT ys a =
      ∑ x, S15.directPostCrossingWeight PT hPT ys a x *
        ∏ b ∈ S15.bulkNeighbours PT hPT a,
          (1 + S15.Needs.acoef (T.S.E k) PT.tiling.c π.w x (ys b)) := by
  classical
  unfold S15.directBulkMass
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  exact directFactor_eq_one_add_acoef PT hPT a ys b x π (hπ b hb)

theorem directRowWeight_dependsOn {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k)
    (ys ys' : S15.OddAssignment T k)
    (hys : ∀ b ∈ star a, ys b = ys' b) (x : Fin (T.S.N k)) :
    S15.directRowWeight PT hPT ys a x = S15.directRowWeight PT hPT ys' a x := by
  classical
  have hcrossSubset : S15.crossingNeighbours PT hPT a ⊆ star a := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
  have hbulkSubset : S15.bulkNeighbours PT hPT a ⊆ star a := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
  have hfactor (b : S15.OddPosition T k) (hb : b ∈ star a)
      (z : Fin (T.S.N k)) :
      S15.directFactor PT hPT a ys b z = S15.directFactor PT hPT a ys' b z := by
    simp [S15.directFactor, hys b hb]
  have hcross : S15.directCrossingMass PT hPT ys a =
      S15.directCrossingMass PT hPT ys' a := by
    unfold S15.directCrossingMass
    apply Finset.sum_congr rfl
    intro z hz
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact hfactor b (hcrossSubset hb) z
  have hpost (z : Fin (T.S.N k)) :
      S15.directPostCrossingWeight PT hPT ys a z =
        S15.directPostCrossingWeight PT hPT ys' a z := by
    unfold S15.directPostCrossingWeight
    rw [hcross]
    by_cases hm : 0 < S15.directCrossingMass PT hPT ys' a
    · simp [hm]
      apply congrArg (fun q : ℝ => q / S15.directCrossingMass PT hPT ys' a)
      apply congrArg (fun q : ℝ => S15.directBaseWeight PT hPT a z * q)
      apply Finset.prod_congr rfl
      intro b hb
      exact hfactor b (hcrossSubset hb) z
    · simp [hm]
  unfold S15.directRowWeight
  rw [hcross, hpost]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  exact hfactor b (hbulkSubset hb) x

theorem directRowWeight_product_dependsOn {κ : CConsts} {T : Stage} {k n : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (positions : Fin n → S15.EvenPosition T k) (x : Fin (T.S.N k))
    (S : Finset (S15.OddPosition T k))
    (hscope : ∀ i, star (positions i) ⊆ S) :
    FinProb.DependsOn
      (fun ys => ∏ i, S15.directRowWeight PT hPT ys (positions i) x) S := by
  intro ys ys' hys
  apply Finset.prod_congr rfl
  intro i hi
  apply directRowWeight_dependsOn PT hPT (positions i) ys ys'
  · intro b hb
    exact hys b (hscope i hb)

theorem directBaseWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k)
    (x : Fin (T.S.N k)) : 0 ≤ S15.directBaseWeight PT hPT a x := by
  dsimp [S15.directBaseWeight]
  split_ifs <;> positivity

theorem directCrossingMass_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) : 0 ≤ S15.directCrossingMass PT hPT ys a := by
  classical
  unfold S15.directCrossingMass
  apply Finset.sum_nonneg
  intro x hx
  apply mul_nonneg
  · exact directBaseWeight_nonneg PT hPT a x
  · apply Finset.prod_nonneg
    intro b hb
    exact directFactor_nonneg PT hPT a ys b x

theorem directPostCrossingWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) (x : Fin (T.S.N k)) :
    0 ≤ S15.directPostCrossingWeight PT hPT ys a x := by
  dsimp [S15.directPostCrossingWeight]
  split_ifs with hm
  · apply div_nonneg
    · apply mul_nonneg
      · exact directBaseWeight_nonneg PT hPT a x
      · apply Finset.prod_nonneg
        intro b hb
        exact directFactor_nonneg PT hPT a ys b x
    · exact hm.le
  · exact le_rfl

theorem directBulkMass_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) : 0 ≤ S15.directBulkMass PT hPT ys a := by
  classical
  unfold S15.directBulkMass
  apply Finset.sum_nonneg
  intro x hx
  apply mul_nonneg
  · exact directPostCrossingWeight_nonneg PT hPT ys a x
  · apply Finset.prod_nonneg
    intro b hb
    exact directFactor_nonneg PT hPT a ys b x

theorem directRowWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) (x : Fin (T.S.N k)) :
    0 ≤ S15.directRowWeight PT hPT ys a x := by
  unfold S15.directRowWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact directCrossingMass_nonneg PT hPT ys a
    · exact directPostCrossingWeight_nonneg PT hPT ys a x
  · apply Finset.prod_nonneg
    intro b hb
    exact directFactor_nonneg PT hPT a ys b x

theorem patchAt_eq_of_leaf {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v : S15.Position T k) (hv : v ∈ PT.tiling.leaf i) :
    S15.patchAt PT hPT v = i := by
  dsimp [S15.patchAt]
  exact ((Classical.choose_spec (hPT.tiling_valid.prefix_complete v)).2 i hv).symm

theorem directRowWeight_zero_of_not_envelope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) (x : Fin (T.S.N k))
    (hnot : x ∉ PT.envelope (S15.patchAt PT hPT a.1)) :
    S15.directRowWeight PT hPT ys a x = 0 := by
  classical
  unfold S15.directRowWeight
  by_cases hcross : 0 < S15.directCrossingMass PT hPT ys a
  · simp [S15.directPostCrossingWeight, hcross, S15.directBaseWeight, hnot]
  · simp [S15.directPostCrossingWeight, hcross]

theorem patchColumnAverage_directRowWeight_zero {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (ys : S15.OddAssignment T k) (x : Fin (T.S.N k))
    (hnot : x ∉ PT.envelope i) :
    S15.patchColumnAverage PT i (S15.directRowWeight PT hPT) ys x = 0 := by
  classical
  unfold S15.patchColumnAverage
  have hterms : ∀ a ∈ S15.evenPatchPositions PT.tiling i,
      S15.directRowWeight PT hPT ys a x = 0 := by
    intro a ha
    have hleaf : a.1 ∈ PT.tiling.leaf i := (Finset.mem_filter.mp ha).2
    have hpatch := patchAt_eq_of_leaf PT hPT i a.1 hleaf
    exact directRowWeight_zero_of_not_envelope PT hPT ys a x (by simpa [hpatch] using hnot)
  have hsum :
      (∑ a ∈ S15.evenPatchPositions PT.tiling i,
        (PT.tiling.P i).M * S15.directRowWeight PT hPT ys a x) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [hterms a ha]
    simp
  simp [hsum]

theorem directRowWeight_sum {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) :
    (∑ x, S15.directRowWeight PT hPT ys a x) = S15.directRowMass PT hPT ys a := by
  classical
  unfold S15.directRowWeight S15.directRowMass S15.directBulkMass
  calc
    (∑ x, S15.directCrossingMass PT hPT ys a *
        S15.directPostCrossingWeight PT hPT ys a x *
          ∏ b ∈ S15.bulkNeighbours PT hPT a, S15.directFactor PT hPT a ys b x) =
      ∑ x, S15.directCrossingMass PT hPT ys a *
        (S15.directPostCrossingWeight PT hPT ys a x *
          ∏ b ∈ S15.bulkNeighbours PT hPT a, S15.directFactor PT hPT a ys b x) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = S15.directCrossingMass PT hPT ys a *
        ∑ x, S15.directPostCrossingWeight PT hPT ys a x *
          ∏ b ∈ S15.bulkNeighbours PT hPT a, S15.directFactor PT hPT a ys b x := by
      rw [← Finset.mul_sum]

theorem directNormalizedRow_sum {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) (hpos : 0 < S15.directRowMass PT hPT ys a) :
    (∑ x, S15.directNormalizedRow PT hPT ys a x) = 1 := by
  classical
  unfold S15.directNormalizedRow
  simp [hpos]
  calc
    (∑ x, S15.directRowWeight PT hPT ys a x / S15.directRowMass PT hPT ys a) =
        (∑ x, S15.directRowWeight PT hPT ys a x) / S15.directRowMass PT hPT ys a := by
      rw [Finset.sum_div]
    _ = 1 := by rw [directRowWeight_sum]; exact div_self (ne_of_gt hpos)

theorem directNormalizedRow_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) (x : Fin (T.S.N k)) :
    0 ≤ S15.directNormalizedRow PT hPT ys a x := by
  dsimp [S15.directNormalizedRow]
  split_ifs with hmass
  · exact div_nonneg (directRowWeight_nonneg PT hPT ys a x) hmass.le
  · exact le_rfl

theorem directNormalizedRow_supported {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) (x : Fin (T.S.N k))
    (hrow : S15.directNormalizedRow PT hPT ys a x ≠ 0) : x ∈ T.X k := by
  classical
  have hmass : 0 < S15.directRowMass PT hPT ys a := by
    by_contra hnot
    have hnonpos : ¬0 < S15.directRowMass PT hPT ys a := hnot
    simp [S15.directNormalizedRow, hnonpos] at hrow
  have hweight : S15.directRowWeight PT hPT ys a x ≠ 0 := by
    intro hz
    apply hrow
    simp [S15.directNormalizedRow, hmass, hz]
  have hbase : S15.directBaseWeight PT hPT a x ≠ 0 := by
    intro hz
    apply hweight
    simp [S15.directRowWeight, S15.directPostCrossingWeight, hz]
  have henv : x ∈ PT.envelope (S15.patchAt PT hPT a.1) := by
    by_contra hnot
    apply hbase
    simp [S15.directBaseWeight, hnot]
  have hpatch := hPT.tiling_valid.patch_supports (S15.patchAt PT hPT a.1)
  have hxres : x ∈ T.X k \ PT.tiling.reserveX :=
    hpatch.2.1 (hpatch.1 (hPT.envelope_subset _ henv))
  simp only [Finset.mem_sdiff] at hxres
  exact hxres.1

theorem directNormalizedRow_envelope_supported {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) (x : Fin (T.S.N k))
    (hrow : S15.directNormalizedRow PT hPT ys a x ≠ 0) :
    x ∈ PT.envelope (S15.patchAt PT hPT a.1) := by
  classical
  have hmass : 0 < S15.directRowMass PT hPT ys a := by
    by_contra hnot
    have hnonpos : ¬0 < S15.directRowMass PT hPT ys a := hnot
    simp [S15.directNormalizedRow, hnonpos] at hrow
  have hweight : S15.directRowWeight PT hPT ys a x ≠ 0 := by
    intro hz
    apply hrow
    simp [S15.directNormalizedRow, hmass, hz]
  have hbase : S15.directBaseWeight PT hPT a x ≠ 0 := by
    intro hz
    apply hweight
    simp [S15.directRowWeight, S15.directPostCrossingWeight, hz]
  by_contra hnot
  apply hbase
  simp [S15.directBaseWeight, hnot]

theorem patchColumnAverage_directRowWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (ys : S15.OddAssignment T k) (x : Fin (T.S.N k)) :
    0 ≤ S15.patchColumnAverage PT i (S15.directRowWeight PT hPT) ys x := by
  classical
  unfold S15.patchColumnAverage
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (Nat.cast_nonneg _) (directRowWeight_nonneg PT hPT ys a x)

theorem directNormalizedRow_common_hit {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : S15.OddAssignment T k)
    (a : S15.EvenPosition T k) (x : Fin (T.S.N k))
    (hrow : S15.directNormalizedRow PT hPT ys a x ≠ 0)
    (b : S15.OddPosition T k) (hadj : S15.Adjacent a b) :
    Hits (T.S.E k) PT.tiling.c x (ys b) := by
  classical
  have hmass : 0 < S15.directRowMass PT hPT ys a := by
    by_contra hnot
    apply hrow
    simp [S15.directNormalizedRow, hnot]
  have hweight : S15.directRowWeight PT hPT ys a x ≠ 0 := by
    intro hz
    apply hrow
    simp [S15.directNormalizedRow, hmass, hz]
  have hcross : S15.directCrossingMass PT hPT ys a ≠ 0 := by
    intro hz
    apply hweight
    simp [S15.directRowWeight, hz]
  have hpost : S15.directPostCrossingWeight PT hPT ys a x ≠ 0 := by
    intro hz
    apply hweight
    simp [S15.directRowWeight, hz]
  have hbulkProd :
      (∏ b' ∈ S15.bulkNeighbours PT hPT a, S15.directFactor PT hPT a ys b' x) ≠ 0 := by
    intro hz
    apply hweight
    simp [S15.directRowWeight, hz]
  have hcrossPos : 0 < S15.directCrossingMass PT hPT ys a :=
    lt_of_le_of_ne (directCrossingMass_nonneg PT hPT ys a) (Ne.symm hcross)
  have hcrossProd :
      (∏ b' ∈ S15.crossingNeighbours PT hPT a, S15.directFactor PT hPT a ys b' x) ≠ 0 := by
    by_contra hz
    have hpostzero : S15.directPostCrossingWeight PT hPT ys a x = 0 := by
      simp [S15.directPostCrossingWeight, hcrossPos, hz]
    exact hpost hpostzero
  have hsets : b ∈ S15.crossingNeighbours PT hPT a ∨ b ∈ S15.bulkNeighbours PT hPT a := by
    by_cases hp : S15.patchAt PT hPT b.1 = S15.patchAt PT hPT a.1
    · right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hadj, hp⟩⟩
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hadj, hp⟩⟩
  rcases hsets with hcrossMem | hbulkMem
  · exact directFactor_nonzero_hit PT hPT a ys b x
      ((Finset.prod_ne_zero_iff.mp hcrossProd) b hcrossMem)
  · exact directFactor_nonzero_hit PT hPT a ys b x
      ((Finset.prod_ne_zero_iff.mp hbulkProd) b hbulkMem)

noncomputable def directHallRows_of_sampler {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (J : S15.DirectSampler PT hPT) (ys : S15.OddAssignment T k)
    (hys : J.law.w ys ≠ 0)
    (hcol : ∀ x, ∑ a : S15.EvenPosition T k,
      S15.directNormalizedRow PT hPT ys a x ≤ 1) :
    S15.DirectHallRows (T := T) (k := k) PT.tiling.c := by
  refine {
    oddLabel := ys
    odd_injective := J.injective_on_support ys hys
    odd_in_Y := fun b => by
      let hi := S15.patchAt PT hPT b.1
      have hpatch := hPT.tiling_valid.patch_supports hi
      have hlabel := J.label_supported ys hys b
      have hlabel' : ys b ∈ (PT.tiling.P hi).Y := by simpa [hi] using hlabel
      have hres := hpatch.2.2.1 hlabel'
      have hwhole := hpatch.2.2.2 hres
      exact (Finset.mem_sdiff.mp hwhole).1
    row := fun a x => S15.directNormalizedRow PT hPT ys a x
    row_nonneg := fun a x => directNormalizedRow_nonneg PT hPT ys a x
    row_sum := ?_
    row_supported := fun a x hrow => directNormalizedRow_supported PT hPT ys a x hrow
    common_neighbour := fun a x hrow b hab =>
      directNormalizedRow_common_hit PT hPT ys a x hrow b hab
    column_load := hcol }
  intro a
  have hmass : 0 < S15.directRowMass PT hPT ys a := by
    have hgate := J.row_mass_gate ys hys a
    linarith
  exact directNormalizedRow_sum PT hPT ys a hmass

theorem direct_column_le_of_patch_averages {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (J : S15.DirectSampler PT hPT) (ys : S15.OddAssignment T k)
    (hys : J.law.w ys ≠ 0)
    (havg : ∀ i x, S15.patchColumnAverage PT i
      (S15.directRowWeight PT hPT) ys x ≤ (T.S.N k : ℝ) / (2 : ℝ) ^ (T.S.n k) / 1600) :
    ∀ x, ∑ a : S15.EvenPosition T k, S15.directNormalizedRow PT hPT ys a x ≤ 1 := by
  classical
  intro x
  by_cases hex : ∃ i, x ∈ PT.envelope i
  · obtain ⟨i₀, hxi₀⟩ := hex
    let E := S15.evenPatchPositions PT.tiling i₀
    have hrowzero (a : S15.EvenPosition T k) (ha : a ∈ Finset.univ) (hnot : a ∉ E) :
        S15.directNormalizedRow PT hPT ys a x = 0 := by
      by_contra hne
      have henv := Lane_q_s15_direct.directNormalizedRow_envelope_supported PT hPT ys a x hne
      let j := S15.patchAt PT hPT a.1
      have hjeq : j ≠ i₀ := by
        intro hEq
        apply hnot
        have hleaf : a.1 ∈ PT.tiling.leaf j :=
          (Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).1
        have hleaf' : a.1 ∈ PT.tiling.leaf i₀ := by simpa [hEq] using hleaf
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hleaf'⟩
      have hneq : i₀ ≠ j := fun hEq => hjeq hEq.symm
      have hdisj := hPT.tiling_valid.patch_X_disjoint i₀ j hneq
      have hxi : x ∈ (PT.tiling.P i₀).X := hPT.envelope_subset i₀ hxi₀
      have hxj : x ∈ (PT.tiling.P j).X := by simpa [j] using hPT.envelope_subset j henv
      exact (Finset.disjoint_left.mp hdisj) hxi hxj
    have hsumSupport :
        (∑ a : S15.EvenPosition T k, S15.directNormalizedRow PT hPT ys a x) =
          ∑ a ∈ E, S15.directNormalizedRow PT hPT ys a x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ E)
      intro a ha hnot
      simp [hrowzero a (Finset.mem_univ a) hnot]
    by_cases hEzero : E.card = 0
    · have hEempty : E = ∅ := Finset.card_eq_zero.mp hEzero
      rw [hsumSupport]
      simp [hEempty]
    · have hEpos : (0 : ℝ) < (E.card : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hEzero)
      have hMpos : (0 : ℝ) < (PT.tiling.P i₀).M := by
        have hcard : 0 < ((PT.tiling.P i₀).X.card : ℝ) :=
          Nat.cast_pos.mpr (Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i₀).1)
        rw [(PT.tiling.P i₀).cardX] at hcard
        exact hcard
      have hsumRaw :
          (∑ a ∈ E, S15.directRowWeight PT hPT ys a x) =
            (E.card : ℝ) / (PT.tiling.P i₀).M *
              S15.patchColumnAverage PT i₀ (S15.directRowWeight PT hPT) ys x := by
        let M : ℝ := ((PT.tiling.P i₀).M : ℝ)
        let Tot : ℝ := ∑ a ∈ E,
          M * S15.directRowWeight PT hPT ys a x
        have havgEq :
            S15.patchColumnAverage PT i₀ (S15.directRowWeight PT hPT) ys x =
              (E.card : ℝ)⁻¹ * Tot := by
          simp [S15.patchColumnAverage, E, Tot, M]
        calc
          (∑ a ∈ E, S15.directRowWeight PT hPT ys a x) =
              ∑ a ∈ E, M⁻¹ * (M * S15.directRowWeight PT hPT ys a x) := by
            apply Finset.sum_congr rfl
            intro a ha
            dsimp [M]
            field_simp [ne_of_gt hMpos]
          _ = M⁻¹ * Tot := by
            rw [← Finset.mul_sum]
          _ = (E.card : ℝ) / (PT.tiling.P i₀).M *
                S15.patchColumnAverage PT i₀ (S15.directRowWeight PT hPT) ys x := by
            rw [havgEq]
            dsimp [M]
            field_simp [hEpos.ne', hMpos.ne'] <;> ring
      have hrowFactor (a : S15.EvenPosition T k) (ha : a ∈ E) :
          S15.directNormalizedRow PT hPT ys a x ≤
            2 * S15.directRowWeight PT hPT ys a x := by
        have hmass := J.row_mass_gate ys hys a
        have hpos : 0 < S15.directRowMass PT hPT ys a := by linarith
        have hweight0 := directRowWeight_nonneg PT hPT ys a x
        unfold S15.directNormalizedRow
        simp [hpos]
        apply (div_le_iff₀ hpos).2
        have hmul := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤
          2 * S15.directRowWeight PT hPT ys a x by positivity)
        nlinarith
      have hratio := evenPatchPositions_ratio_le PT hPT i₀
      calc
        (∑ a : S15.EvenPosition T k, S15.directNormalizedRow PT hPT ys a x) =
            ∑ a ∈ E, S15.directNormalizedRow PT hPT ys a x := hsumSupport
        _ ≤ 2 * ∑ a ∈ E, S15.directRowWeight PT hPT ys a x := by
          calc
            _ ≤ ∑ a ∈ E, 2 * S15.directRowWeight PT hPT ys a x :=
              Finset.sum_le_sum fun a ha => hrowFactor a ha
            _ = 2 * ∑ a ∈ E, S15.directRowWeight PT hPT ys a x := by rw [Finset.mul_sum]
        _ = 2 * ((E.card : ℝ) / (PT.tiling.P i₀).M) *
              S15.patchColumnAverage PT i₀ (S15.directRowWeight PT hPT) ys x := by
          rw [hsumRaw]
          ring
        _ ≤ 2 * (800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k) *
              ((T.S.N k : ℝ) / (2 : ℝ) ^ (T.S.n k) / 1600) := by
          have hratio2 : 2 * ((E.card : ℝ) / ((PT.tiling.P i₀).M : ℝ)) ≤
              2 * (800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k) :=
            mul_le_mul_of_nonneg_left hratio (by norm_num)
          have havg0 := Lane_q_s15_direct.patchColumnAverage_directRowWeight_nonneg PT hPT i₀ ys x
          calc
            _ ≤ 2 * (800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k) *
                S15.patchColumnAverage PT i₀ (S15.directRowWeight PT hPT) ys x :=
              mul_le_mul_of_nonneg_right hratio2 havg0
            _ ≤ 2 * (800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k) *
                ((T.S.N k : ℝ) / (2 : ℝ) ^ (T.S.n k) / 1600) :=
              mul_le_mul_of_nonneg_left (havg i₀ x) (by positivity)
        _ = 1 := by
          field_simp [ne_of_gt (T.S.N_pos k), pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
  · have hzero (a : S15.EvenPosition T k) :
        S15.directNormalizedRow PT hPT ys a x = 0 := by
      by_contra hne
      have hi := Lane_q_s15_direct.directNormalizedRow_envelope_supported PT hPT ys a x hne
      exact hex ⟨S15.patchAt PT hPT a.1, hi⟩
    simp [hzero]

theorem expect_le_of_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (hΩ : ∀ i, Nonempty (Ω i)) (P : FinProb (∀ i, Ω i)) (laws : ∀ i, FinProb (Ω i))
    (S : Finset ι) (F : (∀ i, Ω i) → ℝ) (α : ℝ)
    (hF : ∀ ω, 0 ≤ F ω)
    (hdep : FinProb.DependsOn F S)
    (hbound : ∀ o : ∀ i, Ω i,
      P.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤ α * ∏ i ∈ S, (laws i).w (o i)) :
    P.expect F ≤ α * (FinProb.pi laws).expect F := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ S) Ω
  let proj : (∀ i, Ω i) → (∀ i : {i // i ∈ S}, Ω i.1) := fun ω i => ω i.1
  let outside : ∀ i : {i // i ∉ S}, Ω i.1 := fun i => Classical.choice (hΩ i.1)
  let Fsub : (∀ i : {i // i ∈ S}, Ω i.1) → ℝ := fun a => F (e.symm (a, outside))
  let Psub : FinProb (∀ i : {i // i ∈ S}, Ω i.1) := FinProb.map P proj
  let Qsub : FinProb (∀ i : {i // i ∈ S}, Ω i.1) :=
    FinProb.pi (fun i : {i // i ∈ S} => laws i.1)
  have hFsub : ∀ a, 0 ≤ Fsub a := fun a => hF (e.symm (a, outside))
  have hproj (ω : ∀ i, Ω i) (i : {i // i ∈ S}) :
      e.symm (proj ω, outside) i.1 = ω i.1 := by
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2, proj]
  have hFfactor (ω : ∀ i, Ω i) : F ω = Fsub (proj ω) := by
    unfold Fsub
    apply hdep
    intro i hi
    exact (hproj ω ⟨i, hi⟩).symm
  have hPexpect : P.expect F = Psub.expect Fsub := by
    calc
      P.expect F = P.expect (fun ω => Fsub (proj ω)) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro ω hω
        rw [hFfactor]
      _ = Psub.expect Fsub := (FinProb.map_expect P proj Fsub).symm
  have hrawexpect : (FinProb.pi laws).expect F = Qsub.expect Fsub := by
    exact FinProb.pi_expect_depends laws S F
      (fun i => Classical.choice (hΩ i)) hdep
  have hPsubWeight (a : ∀ i : {i // i ∈ S}, Ω i.1) :
      Psub.w a = P.pr (fun ω => ∀ i (hi : i ∈ S), ω i = a ⟨i, hi⟩) := by
    unfold Psub FinProb.map FinProb.pr
    apply Finset.sum_congr rfl
    intro ω hω
    have hiff : proj ω = a ↔ ∀ i (hi : i ∈ S), ω i = a ⟨i, hi⟩ := by
      constructor
      · intro h i hi
        exact congrFun h ⟨i, hi⟩
      · intro h
        funext i
        exact h i.1 i.2
    by_cases h : ∀ i (hi : i ∈ S), ω i = a ⟨i, hi⟩ <;> simp [hiff, h]
  have htarget (a : ∀ i : {i // i ∈ S}, Ω i.1) :
      Psub.w a ≤ α * Qsub.w a := by
    rw [hPsubWeight]
    let o : ∀ i, Ω i := e.symm (a, outside)
    have ho (i : ι) (hi : i ∈ S) : o i = a ⟨i, hi⟩ := by
      simp [o, e, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
    have hprob : P.pr (fun ω => ∀ i (hi : i ∈ S), ω i = a ⟨i, hi⟩) =
        P.pr (fun ω => ∀ i (hi : i ∈ S), ω i = o i) := by
      congr 1
      funext ω
      apply propext
      constructor
      · intro h i hi
        calc
          ω i = a ⟨i, hi⟩ := h i hi
          _ = o i := (ho i hi).symm
      · intro h i hi
        calc
          ω i = o i := h i hi
          _ = a ⟨i, hi⟩ := ho i hi
    rw [hprob]
    calc
      P.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤ α * ∏ i ∈ S, (laws i).w (o i) := hbound o
      _ = α * Qsub.w a := by
        congr 1
        have hattach (g : ι → ℝ) :
            (∏ i : {i // i ∈ S}, g i.1) = ∏ i ∈ S, g i := by
          rw [Finset.univ_eq_attach]
          exact Finset.prod_attach S g
        calc
          ∏ i ∈ S, (laws i).w (o i) =
              ∏ i : {i // i ∈ S}, (laws i.1).w (o i.1) :=
            (hattach (fun i => (laws i).w (o i))).symm
          _ = ∏ i : {i // i ∈ S}, (laws i.1).w (a i) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [ho i.1 i.2]
          _ = Qsub.w a := by simp [Qsub, FinProb.pi]
  calc
    P.expect F = Psub.expect Fsub := hPexpect
    _ = ∑ a, Psub.w a * Fsub a := rfl
    _ ≤ ∑ a, (α * Qsub.w a) * Fsub a := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right (htarget a) (hFsub a)
    _ = α * Qsub.expect Fsub := by
      simp [FinProb.expect, Finset.mul_sum, mul_assoc]
    _ = α * (FinProb.pi laws).expect F := by rw [hrawexpect]

theorem pi_expect_finset_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (laws : ∀ i, FinProb (Ω i))
    (S : Finset ι) (f : ∀ i, Ω i → ℝ) :
    (FinProb.pi laws).expect (fun ω => ∏ i ∈ S, f i (ω i)) =
      ∏ i ∈ S, (laws i).expect (f i) := by
  classical
  let g : ∀ i, Ω i → ℝ := fun i y =>
    (laws i).w y * if i ∈ S then f i y else 1
  have hterm (ω : ∀ i, Ω i) :
      ∏ i, g i (ω i) = (∏ i, (laws i).w (ω i)) *
        (∏ i ∈ S, f i (ω i)) := by
    simp only [g]
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_ite (s := Finset.univ) (p := fun i : ι => i ∈ S)
      (f := fun i => f i (ω i)) (g := fun _ => (1 : ℝ))]
    simp
  calc
    (FinProb.pi laws).expect (fun ω => ∏ i ∈ S, f i (ω i)) =
        ∑ ω : ∀ i, Ω i, ∏ i, g i (ω i) := by
      simp only [FinProb.expect, FinProb.pi]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [hterm]
    _ = ∏ i, ∑ y, g i y := by rw [Fintype.prod_sum]
    _ = ∏ i ∈ S, (laws i).expect (f i) := by
      have hsum_i (i : ι) :
          ∑ y, g i y = if i ∈ S then (laws i).expect (f i) else 1 := by
        by_cases hi : i ∈ S
        · simp [g, hi, FinProb.expect]
        · simp [g, hi, (laws i).sum_eq_one]
      calc
        ∏ i, ∑ y, g i y =
            ∏ i, (if i ∈ S then (laws i).expect (f i) else 1) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hsum_i i
        _ = ∏ i ∈ S, (laws i).expect (f i) := by
          rw [Finset.prod_ite (s := Finset.univ) (p := fun i : ι => i ∈ S)
            (f := fun i => (laws i).expect (f i)) (g := fun _ => (1 : ℝ))]
          simp

theorem finLaw_pi_E_finset_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (laws : ∀ i, FinLaw (Ω i))
    (S : Finset ι) (f : ∀ i, Ω i → ℝ) :
    (FinLaw.pi laws).E (fun ω => ∏ i ∈ S, f i (ω i)) =
      ∏ i ∈ S, (laws i).E (f i) := by
  classical
  let g : ∀ i, Ω i → ℝ := fun i y =>
    (laws i).w y * if i ∈ S then f i y else 1
  have hterm (ω : ∀ i, Ω i) :
      ∏ i, g i (ω i) = (∏ i, (laws i).w (ω i)) *
        (∏ i ∈ S, f i (ω i)) := by
    simp only [g]
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_ite (s := Finset.univ) (p := fun i : ι => i ∈ S)
      (f := fun i => f i (ω i)) (g := fun _ => (1 : ℝ))]
    simp
  calc
    (FinLaw.pi laws).E (fun ω => ∏ i ∈ S, f i (ω i)) =
        ∑ ω : ∀ i, Ω i, ∏ i, g i (ω i) := by
      simp only [FinLaw.E, FinLaw.pi]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [hterm]
    _ = ∏ i, ∑ y, g i y := by rw [Fintype.prod_sum]
    _ = ∏ i ∈ S, (laws i).E (f i) := by
      have hsum_i (i : ι) :
          ∑ y, g i y = if i ∈ S then (laws i).E (f i) else 1 := by
        by_cases hi : i ∈ S
        · simp [g, hi, FinLaw.E]
        · simp [g, hi, (laws i).sum_one]
      calc
        ∏ i, ∑ y, g i y =
            ∏ i, (if i ∈ S then (laws i).E (f i) else 1) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hsum_i i
        _ = ∏ i ∈ S, (laws i).E (f i) := by
          rw [Finset.prod_ite (s := Finset.univ) (p := fun i : ι => i ∈ S)
            (f := fun i => (laws i).E (f i)) (g := fun _ => (1 : ℝ))]
          simp

theorem expect_normalizedHit_eq_one {N : ℕ} (π : Law N)
    (E : Fin N → Fin N → Prop) (c : Colour) (x : Fin N)
    (hd : 0 < deg E c π.w x) :
    (π).expect (fun y => S15.normalizedHit E c π x y) = 1 := by
  classical
  have hfactor (y : Fin N) : S15.normalizedHit E c π x y =
      hit E c x y / deg E c π.w x := by
    simp [S15.normalizedHit, hd]
  unfold FinProb.expect
  simp_rw [hfactor]
  have hsum :
      (∑ y, π.w y * (hit E c x y / deg E c π.w x)) =
        (∑ y, π.w y * hit E c x y) / deg E c π.w x := by
    have hterm (y : Fin N) :
        π.w y * (hit E c x y / deg E c π.w x) =
          (π.w y * hit E c x y) / deg E c π.w x := by ring
    simp_rw [hterm]
    rw [Finset.sum_div]
  rw [hsum]
  unfold deg
  exact div_self (ne_of_gt hd)

theorem directRowWeight_split_cross_bulk {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (ys : S15.OddAssignment T k) (a : S15.EvenPosition T k)
    (x : Fin (T.S.N k))
    (hcross : 0 < S15.directCrossingMass PT hPT ys a) :
    S15.directRowWeight PT hPT ys a x =
      S15.directBaseWeight PT hPT a x *
        (∏ b ∈ S15.crossingNeighbours PT hPT a,
          S15.directFactor PT hPT a ys b x) *
        (∏ b ∈ S15.bulkNeighbours PT hPT a,
          S15.directFactor PT hPT a ys b x) := by
  unfold S15.directRowWeight S15.directPostCrossingWeight
  simp only [if_pos hcross]
  field_simp [ne_of_gt hcross]

theorem directRowWeight_eq_base_prod {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (ys : S15.OddAssignment T k) (a : S15.EvenPosition T k)
    (x : Fin (T.S.N k)) :
    S15.directRowWeight PT hPT ys a x =
      S15.directBaseWeight PT hPT a x *
        (∏ b ∈ S15.crossingNeighbours PT hPT a,
          S15.directFactor PT hPT a ys b x) *
        (∏ b ∈ S15.bulkNeighbours PT hPT a,
          S15.directFactor PT hPT a ys b x) := by
  classical
  by_cases hcross : 0 < S15.directCrossingMass PT hPT ys a
  · exact directRowWeight_split_cross_bulk PT hPT ys a x hcross
  · have hmass0 : S15.directCrossingMass PT hPT ys a = 0 := by
      apply le_antisymm
      · exact le_of_not_gt hcross
      · exact directCrossingMass_nonneg PT hPT ys a
    have hbaseNonneg := directBaseWeight_nonneg PT hPT a x
    have hcrossProdNonneg : 0 ≤
        ∏ b ∈ S15.crossingNeighbours PT hPT a,
          S15.directFactor PT hPT a ys b x :=
      Finset.prod_nonneg fun b hb => directFactor_nonneg PT hPT a ys b x
    have hbaseProdZero : S15.directBaseWeight PT hPT a x *
        (∏ b ∈ S15.crossingNeighbours PT hPT a,
          S15.directFactor PT hPT a ys b x) = 0 := by
      by_contra hne
      have hbaseNe : S15.directBaseWeight PT hPT a x ≠ 0 := by
        intro hz
        simp [hz] at hne
      have hcrossProdNe :
          (∏ b ∈ S15.crossingNeighbours PT hPT a,
            S15.directFactor PT hPT a ys b x) ≠ 0 := by
        intro hz
        simp [hz] at hne
      have hbasePos : 0 < S15.directBaseWeight PT hPT a x :=
        lt_of_le_of_ne hbaseNonneg (Ne.symm hbaseNe)
      have hcrossProdPos : 0 <
          ∏ b ∈ S15.crossingNeighbours PT hPT a,
            S15.directFactor PT hPT a ys b x :=
        lt_of_le_of_ne hcrossProdNonneg (Ne.symm hcrossProdNe)
      have htermPos : 0 < S15.directBaseWeight PT hPT a x *
          (∏ b ∈ S15.crossingNeighbours PT hPT a,
            S15.directFactor PT hPT a ys b x) := mul_pos hbasePos hcrossProdPos
      have htermLe : S15.directBaseWeight PT hPT a x *
          (∏ b ∈ S15.crossingNeighbours PT hPT a,
            S15.directFactor PT hPT a ys b x) ≤
              S15.directCrossingMass PT hPT ys a := by
        unfold S15.directCrossingMass
        exact Finset.single_le_sum
          (fun z hz => mul_nonneg (directBaseWeight_nonneg PT hPT a z)
            (Finset.prod_nonneg fun b hb => directFactor_nonneg PT hPT a ys b z))
          (Finset.mem_univ x)
      have hmass0le : S15.directCrossingMass PT hPT ys a ≤ 0 := by rw [hmass0]
      exact (not_le_of_gt htermPos) (le_trans htermLe hmass0le)
    unfold S15.directRowWeight
    rw [hmass0]
    simp [S15.directPostCrossingWeight, hbaseProdZero]

theorem direct_neighbor_union {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k) :
    S15.crossingNeighbours PT hPT a ∪ S15.bulkNeighbours PT hPT a = star a := by
  classical
  ext b
  simp only [Finset.mem_union, star, S15.crossingNeighbours, S15.bulkNeighbours,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨hadj, _⟩ | ⟨hadj, _⟩) <;> exact hadj
  · intro hadj
    by_cases hpatch : S15.patchAt PT hPT b.1 = S15.patchAt PT hPT a.1
    · exact Or.inr ⟨hadj, hpatch⟩
    · exact Or.inl ⟨hadj, hpatch⟩

theorem direct_neighbor_sets_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k) :
    Disjoint (S15.crossingNeighbours PT hPT a) (S15.bulkNeighbours PT hPT a) := by
  apply Finset.disjoint_left.mpr
  intro b hbCross hbBulk
  have hneq := (Finset.mem_filter.mp hbCross).2.2
  have heq := (Finset.mem_filter.mp hbBulk).2.2
  exact hneq heq

theorem directRowWeight_eq_base_star_prod {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (ys : S15.OddAssignment T k) (a : S15.EvenPosition T k)
    (x : Fin (T.S.N k)) :
    S15.directRowWeight PT hPT ys a x = S15.directBaseWeight PT hPT a x *
      (∏ b ∈ star a, S15.directFactor PT hPT a ys b x) := by
  rw [directRowWeight_eq_base_prod]
  calc
    _ = S15.directBaseWeight PT hPT a x *
        ((∏ b ∈ S15.crossingNeighbours PT hPT a,
          S15.directFactor PT hPT a ys b x) *
         (∏ b ∈ S15.bulkNeighbours PT hPT a,
          S15.directFactor PT hPT a ys b x)) := by ring
    _ = S15.directBaseWeight PT hPT a x *
        (∏ b ∈ S15.crossingNeighbours PT hPT a ∪ S15.bulkNeighbours PT hPT a,
          S15.directFactor PT hPT a ys b x) := by
      rw [Finset.prod_union (direct_neighbor_sets_disjoint PT hPT a)]
    _ = S15.directBaseWeight PT hPT a x *
        (∏ b ∈ star a, S15.directFactor PT hPT a ys b x) := by
      rw [direct_neighbor_union PT hPT a]

theorem direct_raw_row_weight_expect {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : S15.EvenPosition T k) (x : Fin (T.S.N k))
    (hdegree : ∀ b ∈ star a,
      0 < deg (T.S.E k) PT.tiling.c (S15.lawAtOdd PT hPT b).w x) :
    (S15.directRawLaw PT hPT).E (fun ys => S15.directRowWeight PT hPT ys a x) =
      S15.directBaseWeight PT hPT a x := by
  classical
  let laws : ∀ b : S15.OddPosition T k, FinLaw (Fin (T.S.N k)) :=
    fun b => S15.lawToFinLaw (S15.lawAtOdd PT hPT b)
  let f : ∀ b : S15.OddPosition T k, Fin (T.S.N k) → ℝ :=
    fun b y => S15.normalizedHit (T.S.E k) PT.tiling.c
      (S15.lawAtOdd PT hPT b) x y
  have hraw : S15.directRawLaw PT hPT = FinLaw.pi laws := by
    simp [S15.directRawLaw, laws, S15.lawToFinLaw]
  have hmean (b : S15.OddPosition T k) (hb : b ∈ star a) :
      (laws b).E (f b) = 1 := by
    have h := expect_normalizedHit_eq_one (S15.lawAtOdd PT hPT b)
      (T.S.E k) PT.tiling.c x (hdegree b hb)
    simpa [laws, f, S15.lawToFinLaw, FinLaw.E, FinProb.expect] using h
  have hproduct :
      (FinLaw.pi laws).E (fun ys => ∏ b ∈ star a, f b (ys b)) = 1 := by
    rw [finLaw_pi_E_finset_product laws (star a) f]
    calc
      ∏ b ∈ star a, (laws b).E (f b) = ∏ b ∈ star a, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro b hb
        exact hmean b hb
      _ = 1 := by simp
  have hrow (ys : S15.OddAssignment T k) :
      S15.directRowWeight PT hPT ys a x = S15.directBaseWeight PT hPT a x *
        ∏ b ∈ star a, f b (ys b) := by
    rw [directRowWeight_eq_base_star_prod]
    rfl
  rw [hraw]
  rw [FinLaw.E]
  calc
    (∑ ys, (FinLaw.pi laws).w ys *
        S15.directRowWeight PT hPT ys a x) =
        S15.directBaseWeight PT hPT a x *
          ∑ ys, (FinLaw.pi laws).w ys * ∏ b ∈ star a, f b (ys b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ys hys
      rw [hrow]
      ring
    _ = S15.directBaseWeight PT hPT a x := by
      rw [← FinLaw.E]
      rw [hproduct]
      ring

theorem direct_raw_product_rows_expect {κ : CConsts} {T : Stage} {k m : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (rows : Fin m → S15.EvenPosition T k) (x : Fin (T.S.N k))
    (hdegree : ∀ i b, b ∈ star (rows i) →
      0 < deg (T.S.E k) PT.tiling.c (S15.lawAtOdd PT hPT b).w x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (star (rows i)) (star (rows j))) :
    (S15.directRawLaw PT hPT).E
      (fun ys => ∏ i, S15.directRowWeight PT hPT ys (rows i) x) =
        ∏ i, S15.directBaseWeight PT hPT (rows i) x := by
  classical
  let laws : ∀ b : S15.OddPosition T k, FinLaw (Fin (T.S.N k)) :=
    fun b => S15.lawToFinLaw (S15.lawAtOdd PT hPT b)
  let f : ∀ b : S15.OddPosition T k, Fin (T.S.N k) → ℝ :=
    fun b y => S15.normalizedHit (T.S.E k) PT.tiling.c
      (S15.lawAtOdd PT hPT b) x y
  let allStars : Finset (S15.OddPosition T k) :=
    Finset.univ.biUnion fun i : Fin m => star (rows i)
  have hraw : S15.directRawLaw PT hPT = FinLaw.pi laws := by
    simp [S15.directRawLaw, laws, S15.lawToFinLaw]
  have hpair : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin m)) : Set (Fin m))
      (fun i : Fin m => star (rows i)) := by
    intro i hi j hj hij
    exact hdisj i j hij
  have hmean (i : Fin m) (b : S15.OddPosition T k) (hb : b ∈ star (rows i)) :
      (laws b).E (f b) = 1 := by
    have h := expect_normalizedHit_eq_one (S15.lawAtOdd PT hPT b)
      (T.S.E k) PT.tiling.c x (hdegree i b hb)
    simpa [laws, f, S15.lawToFinLaw, FinLaw.E, FinProb.expect] using h
  have hrowprod (ys : S15.OddAssignment T k) :
      (∏ i, S15.directRowWeight PT hPT ys (rows i) x) =
        (∏ i, S15.directBaseWeight PT hPT (rows i) x) *
          ∏ b ∈ allStars, f b (ys b) := by
    calc
      ∏ i, S15.directRowWeight PT hPT ys (rows i) x =
          ∏ i, (S15.directBaseWeight PT hPT (rows i) x *
            ∏ b ∈ star (rows i), f b (ys b)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [directRowWeight_eq_base_star_prod]
        rfl
      _ = (∏ i, S15.directBaseWeight PT hPT (rows i) x) *
          ∏ i, ∏ b ∈ star (rows i), f b (ys b) := by rw [Finset.prod_mul_distrib]
      _ = (∏ i, S15.directBaseWeight PT hPT (rows i) x) *
          ∏ b ∈ allStars, f b (ys b) := by
        rw [← Finset.prod_biUnion hpair]
  have hallMean : ∏ b ∈ allStars, (laws b).E (f b) = 1 := by
    rw [Finset.prod_biUnion hpair]
    calc
      ∏ i, ∏ b ∈ star (rows i), (laws b).E (f b) =
          ∏ i, ∏ b ∈ star (rows i), (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        apply Finset.prod_congr rfl
        intro b hb
        exact hmean i b hb
      _ = 1 := by simp
  have hproduct : (FinLaw.pi laws).E (fun ys => ∏ b ∈ allStars, f b (ys b)) = 1 := by
    rw [finLaw_pi_E_finset_product laws allStars f, hallMean]
  rw [hraw, FinLaw.E]
  calc
    (∑ ys, (FinLaw.pi laws).w ys *
        ∏ i, S15.directRowWeight PT hPT ys (rows i) x) =
        (∏ i, S15.directBaseWeight PT hPT (rows i) x) *
          ∑ ys, (FinLaw.pi laws).w ys * ∏ b ∈ allStars, f b (ys b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ys hys
      rw [hrowprod]
      ring
    _ = ∏ i, S15.directBaseWeight PT hPT (rows i) x := by
      rw [← FinLaw.E, hproduct]
      ring

theorem highDirect_envelope_card_lower {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hmode : PT.tiling.mode = .highDirect) (i : Fin PT.tiling.m) :
    ((PT.tiling.P i).M : ℝ) / 2 ≤ (PT.envelope i).card := by
  classical
  have hnotCluster : ¬ PT.tiling.mode.isCluster := by
    simp [hmode, Mode.isCluster]
  have hcardone := hPT.direct_single_corner hnotCluster
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcardone
  have hvActive : v ∈ PT.activeVertices := by rw [hv]; simp
  have henv : PT.envelope i = PT.mesh.corner v i := by
    rw [hPT.envelope_eq i, hv]
    simp
  rw [henv]
  exact (hPT.corner_clean i v hvActive).card_lower

theorem highDirect_scaled_baseweight_le_two {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hmode : PT.tiling.mode = .highDirect) (i : Fin PT.tiling.m)
    (a : S15.EvenPosition T k) (ha : S15.patchAt PT hPT a.1 = i)
    (x : Fin (T.S.N k)) :
    ((PT.tiling.P i).M : ℝ) * S15.directBaseWeight PT hPT a x ≤ 2 := by
  classical
  have hMpos : 0 < ((PT.tiling.P i).M : ℝ) := by
    have hcard : 0 < ((PT.tiling.P i).X.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1)
    rw [(PT.tiling.P i).cardX] at hcard
    exact hcard
  have hEnv := highDirect_envelope_card_lower PT hPT hmode i
  have hcardPos : 0 < ((PT.envelope i).card : ℝ) := by
    exact lt_of_lt_of_le (div_pos hMpos (by norm_num)) hEnv
  have hratio : ((PT.tiling.P i).M : ℝ) / (PT.envelope i).card ≤ 2 := by
    apply (div_le_iff₀ hcardPos).2
    have hEnv' : ((PT.tiling.P i).M : ℝ) / 2 ≤ (PT.envelope i).card := by exact_mod_cast hEnv
    nlinarith
  by_cases hx : x ∈ PT.envelope i
  · simpa [S15.directBaseWeight, ha, hx, div_eq_mul_inv] using hratio
  · simp [S15.directBaseWeight, ha, hx]

theorem star_card_eq_dimension {T : Stage} {k : ℕ}
    (a : S15.EvenPosition T k) : (star a).card = T.S.n k := by
  classical
  let f : Fin (T.S.n k) → S15.OddPosition T k := fun j =>
    ⟨cubeFlip a.1 j, by
      intro hEven
      exact ((cubeFlip_parity a.1 j).mp hEven) a.2⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hval : cubeFlip a.1 i = cubeFlip a.1 j := congrArg Subtype.val hij
    by_contra hne
    have hcoord := congrFun hval i
    have hleft : cubeFlip a.1 i i = !a.1 i := by simp [cubeFlip]
    have hright : cubeFlip a.1 j i = a.1 i := by simp [cubeFlip, hne]
    rw [hleft, hright] at hcoord
    cases hbit : a.1 i <;> simp [hbit] at hcoord
  have himage : (Finset.univ.image f).card = T.S.n k := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hsub : Finset.univ.image f ⊆ star a := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨j, hj, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cubeFlip_adj a.1 j⟩
  have hle : T.S.n k ≤ (star a).card := by
    have h := Finset.card_le_card hsub
    omega
  exact Nat.le_antisymm (star_card_le a) hle

private theorem cubeAdj_eq_cubeFlip {n : ℕ} {v w : CubeVertex n}
    (h : (cube n).Adj v w) : ∃ j : Fin n, w = cubeFlip v j := by
  classical
  change hammingDist v w = 1 at h
  unfold hammingDist at h
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
  have hjmem : j ∈ Finset.univ.filter (fun q : Fin n => v q ≠ w q) := by
    rw [hj]
    simp
  have hdiff : v j ≠ w j := (Finset.mem_filter.mp hjmem).2
  have hsame : ∀ q : Fin n, q ≠ j → v q = w q := by
    intro q hq
    by_contra hne
    have hqmem : q ∈ Finset.univ.filter (fun r : Fin n => v r ≠ w r) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    have hqEq : q = j := by
      rw [hj] at hqmem
      simpa using hqmem
    exact hq hqEq
  refine ⟨j, ?_⟩
  funext q
  by_cases hq : q = j
  · subst q
    have hcoord : cubeFlip v j j = !v j := by simp [cubeFlip, Function.update_self]
    rw [hcoord]
    cases hv : v j <;> cases hw : w j <;> simp_all
  · simp [cubeFlip, hq, hsame q hq]

theorem highDirect_crossingNeighbours_card_le_prefix {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : S15.EvenPosition T k) (i : Fin PT.tiling.m)
    (hi : S15.patchAt PT hPT a.1 = i) :
    (S15.crossingNeighbours PT hPT a).card ≤ (PT.tiling.P i).ℓ := by
  classical
  let ell := (PT.tiling.P i).ℓ
  let C := S15.crossingNeighbours PT hPT a
  have haLeaf : a.1 ∈ PT.tiling.leaf i := by
    have h : a.1 ∈ PT.tiling.leaf (S15.patchAt PT hPT a.1) := by
      dsimp [S15.patchAt]
      exact (Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).1
    rw [hi] at h
    exact h
  let coord (b : {b : S15.OddPosition T k // b ∈ C}) : Fin (T.S.n k) :=
    Classical.choose (cubeAdj_eq_cubeFlip (by
      have hb := (Finset.mem_filter.mp b.2).2.1
      simpa [S15.Adjacent] using hb))
  have hflip (b : {b : S15.OddPosition T k // b ∈ C}) :
      b.1.1 = cubeFlip a.1 (coord b) :=
    Classical.choose_spec (cubeAdj_eq_cubeFlip (by
      have hb := (Finset.mem_filter.mp b.2).2.1
      simpa [S15.Adjacent] using hb))
  have hcoord_lt (b : {b : S15.OddPosition T k // b ∈ C}) :
      (coord b).val < ell := by
    by_contra hnot
    have hjge : ell ≤ (coord b).val := Nat.le_of_not_gt hnot
    have hbLeaf : b.1.1 ∈ PT.tiling.leaf i := by
      rw [hflip b]
      change ∀ q : Fin (T.S.n k), q.val < ell →
        cubeFlip a.1 (coord b) q = PT.tiling.w i q
      intro q hq
      have hqne : q ≠ coord b := by
        intro heq
        have hval := congrArg Fin.val heq
        omega
      simpa [cubeFlip, hqne] using haLeaf q hq
    have hbPatch : S15.patchAt PT hPT b.1.1 = i := by
      dsimp [S15.patchAt]
      exact ((Classical.choose_spec
        (hPT.tiling_valid.prefix_complete b.1.1)).2 i hbLeaf).symm
    have hcrossne := (Finset.mem_filter.mp b.2).2.2
    rw [hbPatch, hi] at hcrossne
    exact hcrossne rfl
  let f : {b : S15.OddPosition T k // b ∈ C} → Fin ell := fun b =>
    ⟨(coord b).val, hcoord_lt b⟩
  have hf : Function.Injective f := by
    intro b1 b2 heq
    have hval : (coord b1).val = (coord b2).val := by
      simpa [f] using congrArg Fin.val heq
    have hcoord : coord b1 = coord b2 := Fin.ext hval
    have hverts : b1.1.1 = b2.1.1 := by
      rw [hflip b1, hflip b2, hcoord]
    apply Subtype.ext
    apply Subtype.ext
    exact hverts
  have hcardSub : Fintype.card {b : S15.OddPosition T k // b ∈ C} ≤ ell :=
    by simpa using Fintype.card_le_of_injective f hf
  calc
    C.card = Fintype.card {b : S15.OddPosition T k // b ∈ C} :=
      (Fintype.card_coe C).symm
    _ ≤ ell := hcardSub

theorem directBulkNeighbours_card_lower {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : S15.EvenPosition T k) (i : Fin PT.tiling.m)
    (hi : S15.patchAt PT hPT a.1 = i) :
    T.S.n k - (PT.tiling.P i).ℓ ≤ (S15.bulkNeighbours PT hPT a).card := by
  have hcardUnion := Finset.card_union_of_disjoint
    (direct_neighbor_sets_disjoint PT hPT a)
  rw [direct_neighbor_union PT hPT a, star_card_eq_dimension] at hcardUnion
  have hcross := highDirect_crossingNeighbours_card_le_prefix PT hPT a i hi
  omega

theorem evenPatchPositions_card_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).ℓ < T.S.n k) :
    (S15.evenPatchPositions PT.tiling i).card =
      2 ^ (T.S.n k - (PT.tiling.P i).ℓ - 1) := by
  classical
  let ell := (PT.tiling.P i).ℓ
  let n := T.S.n k
  let w := PT.tiling.w i
  let S : Finset (Fin n) := Finset.Iio ⟨ell, hle⟩
  let z : ∀ j : S, Bool := fun j => w j.1
  have hScard : S.card = ell := by simp [S]
  have hSlt : S.card < n := by rw [hScard]; exact hle
  have hAgree (v : CubeVertex n) :
      (∀ j : S, v j.1 = z j) ↔ v ∈ prefixLeaf ell w := by
    change (∀ j : S, v j.1 = w j.1) ↔
      (∀ j : Fin n, j.val < ell → v j = w j)
    constructor
    · intro h j hj
      have hjS : j ∈ S := by
        exact Finset.mem_Iio.mpr (Fin.lt_iff_val_lt_val.mpr hj)
      exact h ⟨j, hjS⟩
    · intro h j
      have hjIio : j.1 ∈ Finset.Iio (⟨ell, hle⟩ : Fin n) := by
        simpa [S] using j.2
      have hjlt : (j.1).val < ell := by
        have hlt := Fin.lt_iff_val_lt_val.mp (Finset.mem_Iio.mp hjIio)
        simpa using hlt
      exact h j.1 hjlt
  let Eset : Finset (CubeVertex n) := Finset.univ.filter fun v =>
    v ∈ prefixLeaf ell w ∧ IsEvenRole v
  have hset : (evenRoleSet n).filter (fun v => ∀ j : S, v j.1 = z j) = Eset := by
    ext v
    simp only [Eset, evenRoleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hEven, hEq⟩
      exact ⟨(hAgree v).mp hEq, hEven⟩
    · rintro ⟨hPrefix, hEven⟩
      exact ⟨hEven, (hAgree v).mpr hPrefix⟩
  have hUniform := parity_projection_uniform S hSlt z
  have hEcard :
      (S15.evenPatchPositions PT.tiling i).card = Eset.card := by
    apply Finset.card_bij (fun a _ => a.1)
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨(Finset.mem_filter.mp ha).2, a.2⟩⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro v hv
      rcases (Finset.mem_filter.mp hv).2 with ⟨hleaf, hEven⟩
      refine ⟨⟨v, hEven⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hleaf⟩, ?_⟩
      rfl
  have hcardTarget : Eset.card = 2 ^ (n - ell - 1) := by
    rw [← hset]
    simpa [n, ell, hScard] using hUniform
  rw [hEcard, hcardTarget]

theorem direct_sampler_separated_product_bound {κ : CConsts} {T : Stage} {k m : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (J : S15.DirectSampler PT hPT) (rows : Fin m → S15.EvenPosition T k)
    (x : Fin (T.S.N k)) (M : ℕ) (S : Finset (S15.OddPosition T k))
    (hM : 0 < M)
    (hdegree : ∀ i b, b ∈ star (rows i) →
      0 < deg (T.S.E k) PT.tiling.c (S15.lawAtOdd PT hPT b).w x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (star (rows i)) (star (rows j)))
    (hscope : ∀ i, star (rows i) ⊆ S)
    (hScard : (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5)
    (hbase : ∀ i, (M : ℝ) * S15.directBaseWeight PT hPT (rows i) x ≤ 2)
    (hm : 0 < m) :
    (∑ ys ∈ Finset.univ.filter (fun ys : S15.OddAssignment T k => J.law.w ys ≠ 0),
      J.law.w ys * ∏ i, (M : ℝ) * S15.directRowWeight PT hPT ys (rows i) x) ≤
        4 ^ m := by
  classical
  let F : S15.OddAssignment T k → ℝ := fun ys =>
    ∏ i, (M : ℝ) * S15.directRowWeight PT hPT ys (rows i) x
  have hrow_nonneg (i : Fin m) (ys : S15.OddAssignment T k) :
      0 ≤ S15.directRowWeight PT hPT ys (rows i) x := by
    rw [directRowWeight_eq_base_star_prod]
    apply mul_nonneg (directBaseWeight_nonneg PT hPT (rows i) x)
    exact Finset.prod_nonneg fun b hb => directFactor_nonneg PT hPT (rows i) ys b x
  have hFnonneg : ∀ ys, 0 ≤ F ys := by
    intro ys
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (by positivity) (hrow_nonneg i ys)
  have hdep : FinProb.DependsOn F S := by
    intro ys ys' hys
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    apply directRowWeight_dependsOn PT hPT (rows i) ys ys'
    intro b hb
    exact hys b (hscope i hb)
  have hrawScaled : J.rawLaw.E F ≤ 2 ^ m := by
    have hrawProd := direct_raw_product_rows_expect PT hPT rows x hdegree hdisj
    have hscalePoint (ys : S15.OddAssignment T k) :
        F ys = (M : ℝ) ^ m * ∏ i, S15.directRowWeight PT hPT ys (rows i) x := by
      dsimp [F]
      calc
        ∏ i, (M : ℝ) * S15.directRowWeight PT hPT ys (rows i) x =
            (∏ i : Fin m, (M : ℝ)) *
              ∏ i, S15.directRowWeight PT hPT ys (rows i) x := Finset.prod_mul_distrib
        _ = (M : ℝ) ^ m *
              ∏ i, S15.directRowWeight PT hPT ys (rows i) x := by simp
    have hscaledMean :
        J.rawLaw.E F = (M : ℝ) ^ m *
          ∏ i, S15.directBaseWeight PT hPT (rows i) x := by
      rw [J.rawLaw_eq]
      unfold FinLaw.E
      calc
        (∑ ys, (S15.directRawLaw PT hPT).w ys * F ys) =
            (M : ℝ) ^ m *
              ∑ ys, (S15.directRawLaw PT hPT).w ys *
                ∏ i, S15.directRowWeight PT hPT ys (rows i) x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ys hys
          rw [hscalePoint]
          ring
        _ = (M : ℝ) ^ m *
              (S15.directRawLaw PT hPT).E
                (fun ys => ∏ i, S15.directRowWeight PT hPT ys (rows i) x) := by
          rw [FinLaw.E]
        _ = (M : ℝ) ^ m *
              ∏ i, S15.directBaseWeight PT hPT (rows i) x := by rw [hrawProd]
    have hbaseProd : (M : ℝ) ^ m *
        ∏ i, S15.directBaseWeight PT hPT (rows i) x =
          ∏ i, ((M : ℝ) * S15.directBaseWeight PT hPT (rows i) x) := by
      rw [Finset.prod_mul_distrib]
      simp
    have hproductBound :
        ∏ i, ((M : ℝ) * S15.directBaseWeight PT hPT (rows i) x) ≤ 2 ^ m := by
      calc
        _ ≤ ∏ _i : Fin m, (2 : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact mul_nonneg (by positivity) (directBaseWeight_nonneg PT hPT (rows i) x)
          · intro i hi
            exact hbase i
        _ = 2 ^ m := by simp
    rw [hscaledMean, hbaseProd]
    exact hproductBound
  have hcompare : J.law.E F ≤ 2 * J.rawLaw.E F :=
    J.local_upper_comparison F hFnonneg S hdep hScard
  have hsupport (G : S15.OddAssignment T k → ℝ) :
      (∑ ys ∈ Finset.univ.filter (fun ys : S15.OddAssignment T k => J.law.w ys ≠ 0),
        J.law.w ys * G ys) = J.law.E G := by
    unfold FinLaw.E
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ys hys
    by_cases hz : J.law.w ys = 0 <;> simp [hz]
  have hpower : 2 * (2 : ℝ) ^ m ≤ (4 : ℝ) ^ m := by
    have hnat : m + 1 ≤ 2 * m := by omega
    calc
      2 * (2 : ℝ) ^ m = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ (2 * m) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hnat
      _ = (4 : ℝ) ^ m := by rw [pow_mul]; norm_num
  rw [hsupport F]
  exact le_trans hcompare (le_trans (mul_le_mul_of_nonneg_left hrawScaled (by norm_num)) hpower)

end HypercubeRamsey.Lane_q_s15_direct
