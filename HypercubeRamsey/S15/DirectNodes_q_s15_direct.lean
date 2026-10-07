import HypercubeRamsey.S15.Defs
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

end HypercubeRamsey.Lane_q_s15_direct
