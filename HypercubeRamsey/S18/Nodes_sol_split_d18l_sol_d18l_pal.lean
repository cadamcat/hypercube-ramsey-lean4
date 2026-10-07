import HypercubeRamsey.S17.Nodes
import HypercubeRamsey.S18.Lists

namespace HypercubeRamsey.S18.Lane_sol_d18l_pal
open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}

theorem code_separation {i : Fin PT.tiling.m}
    {hle : (PT.tiling.P i).h ≤ T.S.n k} (ψ : S17PaletteCode i hle)
    (hCode : PaletteCodeSpec i hle ψ) (v w : Pos T k) (hne : v ≠ w)
    (hcolour : ψ.roleColour v = ψ.roleColour w)
    (houter : ∀ a, a ∉ PT.tiling.Icoord i → v a = w a) :
    500 * κ.ρ * (PT.tiling.P i).h < (hammingDist v w : ℝ) := by
  let z := ListGateContext.internalBits i hle v - ListGateContext.internalBits i hle w
  have hzmap : ψ.map z = 0 := by
    dsimp [z]
    rw [map_sub]
    change ψ.roleColour v - ψ.roleColour w = 0
    rw [hcolour, sub_self]
  have hz : z ≠ 0 := by
    intro hz
    apply hne
    funext a
    by_cases ha : a ∈ PT.tiling.Icoord i
    · have ha' : T.S.n k - (PT.tiling.P i).h ≤ a.val := by
        simpa [Tiling.Icoord, topCoordinates] using ha
      let j : Fin (PT.tiling.P i).h := ⟨a.val - (T.S.n k - (PT.tiling.P i).h), by omega⟩
      have hj : (⟨T.S.n k - (PT.tiling.P i).h + j.val, by omega⟩ : Fin (T.S.n k)) = a := by
        apply Fin.ext
        dsimp [j]
        omega
      have heq := congrFun hz j
      change (if v _ then (1 : ZMod 2) else 0) - (if w _ then 1 else 0) = 0 at heq
      rw [hj] at heq
      cases hv : v a <;> cases hw : w a <;> simp_all
    · exact houter a ha
  have hweight : internalWeight z ≤ hammingDist v w := by
    let f : Fin (PT.tiling.P i).h → Fin (T.S.n k) :=
      fun j => ⟨T.S.n k - (PT.tiling.P i).h + j.val, by omega⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Fin.ext
      have := congrArg Fin.val hab
      dsimp [f] at this
      omega
    have hsub : (Finset.univ.filter fun j => z j ≠ 0).image f ⊆
        Finset.univ.filter fun a => v a ≠ w a := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro heq
      apply hj
      change (if v (f j) then (1 : ZMod 2) else 0) - (if w (f j) then 1 else 0) = 0
      rw [heq, sub_self]
    unfold internalWeight hammingDist
    rw [← Finset.card_image_of_injective _ hf]
    exact Finset.card_le_card hsub
  apply lt_of_not_ge
  intro hleDist
  exact hCode.2.1 z hzmap hz (le_trans (by exact_mod_cast hweight) hleDist)

theorem code_fibre_count {i : Fin PT.tiling.m}
    {hle : (PT.tiling.P i).h ≤ T.S.n k} (ψ : S17PaletteCode i hle)
    (hCode : PaletteCodeSpec i hle ψ) (c : Fin ψ.dimension → ZMod 2) :
    s17Chi ψ * (Finset.univ.filter fun v : Pos T k =>
      v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c).card =
    (Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v).card := by
  let S := Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := ψ.roleColour) (s := S) (t := Finset.univ) (fun v hv => Finset.mem_univ _)
  have hcard : Fintype.card (Fin ψ.dimension → ZMod 2) = s17Chi ψ := by
    simp [s17Chi, ListGateContext.PaletteCode.chi, ZMod.card]
  rw [hsum]
  simp only [S, Finset.filter_filter, and_assoc]
  rw [Finset.sum_congr rfl (fun b hb => hCode.2.2.1 b c)]
  simp [hcard]

theorem code_chi_le {i : Fin PT.tiling.m}
    {hle : (PT.tiling.P i).h ≤ T.S.n k} (ψ : S17PaletteCode i hle)
    (hCode : PaletteCodeSpec i hle ψ) : s17Chi ψ ≤ 2 ^ (PT.tiling.P i).h := by
  have h := Fintype.card_le_of_surjective ψ.map hCode.1
  simpa [s17Chi, ListGateContext.PaletteCode.chi, ZMod.card] using h

theorem even_leaf_card (i : Fin PT.tiling.m) (hell : (PT.tiling.P i).ℓ < T.S.n k) :
    (Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v).card =
      2 ^ (T.S.n k - (PT.tiling.P i).ℓ - 1) := by
  let S : Finset (Fin (T.S.n k)) := Finset.univ.filter fun j => j.val < (PT.tiling.P i).ℓ
  have hS : S.card = (PT.tiling.P i).ℓ := by
    dsimp [S]
    rw [Fin.card_filter_val_lt]
    simp [Nat.min_eq_right (le_of_lt hell)]
  have h := parity_projection_uniform S (by omega) (fun j => PT.tiling.w i j.1)
  have heq : (evenRoleSet (T.S.n k)).filter (fun v => ∀ j : S, v j.1 = PT.tiling.w i j.1) =
      Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, evenRoleSet, true_and]
    constructor
    · intro hv
      refine ⟨?_, hv.1⟩
      intro j hj
      exact hv.2 ⟨j, by simp [S, hj]⟩
    · intro hv
      refine ⟨hv.2, ?_⟩
      intro j
      exact hv.1 j.1 ((Finset.mem_filter.mp j.2).2)
  rw [heq, hS] at h
  exact h

theorem small_prefix_height (T : Stage) :
    ∀ᶠ k in Filter.atTop, ∀ ell h : ℕ,
      (ell : ℝ) ≤ Real.sqrt (Real.log (T.S.n k : ℝ)) →
      (h : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) (1 / 10 : ℝ) →
      (ell : ℝ) + h + 1 ≤ Real.sqrt (T.S.n k : ℝ) ∧ ell < T.S.n k := by
  have hn : Filter.Tendsto (fun k => (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hb := (Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < 1 / 16 by norm_num))
  filter_upwards [hn.eventually (Filter.eventually_ge_atTop 16),
    (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 1, hn.eventually hb] with k hk hlog hbound
  intro ell h hell hh
  change 1 ≤ Real.log (T.S.n k : ℝ) at hlog
  have hn0 : 0 ≤ (T.S.n k : ℝ) := by positivity
  have hs := Real.sqrt_nonneg (T.S.n k : ℝ)
  have hsq := Real.sq_sqrt hn0
  have hs4 : 4 ≤ Real.sqrt (T.S.n k : ℝ) := by nlinarith
  have hlog0 : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog0, id_eq,
    abs_of_nonneg hn0] at hbound
  have hsmall : Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ Real.sqrt (T.S.n k : ℝ) / 4 := by
    have ht := Real.sqrt_le_sqrt hbound
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 1 / 16 by norm_num)] at ht
    norm_num at ht
    linarith
  have hh' : (h : ℝ) ≤ Real.sqrt (Real.log (T.S.n k : ℝ)) :=
    hh.trans (by rw [Real.sqrt_eq_rpow]; apply Real.rpow_le_rpow_of_exponent_le hlog; norm_num)
  constructor
  · linarith
  · have : (ell : ℝ) < (T.S.n k : ℝ) := by nlinarith
    exact_mod_cast this

theorem initial_weight_nonneg {hPT : PT.Valid} (D : LateData hPT)
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.initialValid v s) (x : Fin (T.S.N k)) :
    0 ≤ D.initialWeight v s x := by
  apply mul_nonneg (hvalid.1.1 x)
  apply Finset.prod_nonneg
  intro a ha
  apply div_nonneg
  · split_ifs <;> norm_num
  · unfold rowDeg
    apply Finset.sum_nonneg
    intro y hy
    split_ifs <;> simp [(PT.π _).nonneg y]

theorem initial_prior_cap_of_atom {hPT : PT.Valid} (D : LateData hPT)
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.initialValid v s)
    (hchi : (D.chi (D.geom.patchOf v) : ℝ) ≤ Real.exp (PT.tiling.gain (D.geom.patchOf v)))
    (B r : ℝ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hAtom : ∀ x, D.initialWeight v s x ≤ B * Real.exp (-200 * PT.tiling.gain (D.geom.patchOf v)) * r) :
    ∀ x, (D.initialPrior v s).w x ≤
      4 * B * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) * r := by
  let u := fun x => if x ∈ D.palette v then D.initialWeight v s x else 0
  have hu : ∀ x, 0 ≤ u x := by
    intro x
    dsimp [u]
    split_ifs
    · exact initial_weight_nonneg D v s hvalid x
    · exact le_rfl
  have hχ : (0 : ℝ) < D.chi (D.geom.patchOf v) := by exact_mod_cast D.chi_pos _
  have hm : 1 / (4 * (D.chi (D.geom.patchOf v) : ℝ)) ≤ ∑ x, u x := by
    simpa [u, Finset.sum_ite_mem, Finset.univ_inter] using hvalid.2.2
  have hpos : 0 < ∑ x, u x := lt_of_lt_of_le (by positivity) hm
  have huBound : ∀ x, u x ≤ B * Real.exp (-200 * PT.tiling.gain (D.geom.patchOf v)) * r := by
    intro x
    dsimp [u]
    split_ifs
    · exact hAtom x
    · positivity
  intro x
  change (if D.initialValid v s then D.normalize u else Law.dirac D.fallback).w x ≤ _
  rw [if_pos hvalid]
  unfold LateData.normalize
  rw [dif_pos ⟨hu, hpos⟩]
  change u x / (∑ x, u x) ≤ _
  have hm' : 1 ≤ (4 * (D.chi (D.geom.patchOf v) : ℝ)) * ∑ x, u x := by
    have hm' := (div_le_iff₀ (show (0 : ℝ) < 4 * (D.chi (D.geom.patchOf v) : ℝ) by positivity)).mp hm
    nlinarith
  have hx : u x / (∑ x, u x) ≤
      4 * (D.chi (D.geom.patchOf v) : ℝ) *
        (B * Real.exp (-200 * PT.tiling.gain (D.geom.patchOf v)) * r) := by
    apply (div_le_iff₀ hpos).mpr
    have hmult := mul_le_mul_of_nonneg_left hm'
      (show 0 ≤ B * Real.exp (-200 * PT.tiling.gain (D.geom.patchOf v)) * r by positivity)
    nlinarith [huBound x]
  apply hx.trans
  calc
    _ ≤ 4 * Real.exp (PT.tiling.gain (D.geom.patchOf v)) *
        (B * Real.exp (-200 * PT.tiling.gain (D.geom.patchOf v)) * r) := by gcongr
    _ = 4 * B * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) * r := by
      rw [show -199 * PT.tiling.gain (D.geom.patchOf v) =
        PT.tiling.gain (D.geom.patchOf v) + -200 * PT.tiling.gain (D.geom.patchOf v) by ring,
        Real.exp_add]
      ring

theorem inverse_degree_lower (d delta : ℝ) (hd : 1 / 2 - delta ≤ d)
    (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1 / 4) :
    0 < d ∧ 1 / d ≤ 2 * Real.exp (4 * delta) := by
  have hdpos : 0 < d := by linarith
  refine ⟨hdpos, (div_le_iff₀ hdpos).mpr ?_⟩
  have hexp := Real.add_one_le_exp (4 * delta)
  have hpoly : 1 ≤ (1 - 2 * delta) * (1 + 4 * delta) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1 - 2 * delta by linarith)
  have hdeg := mul_le_mul_of_nonneg_right hd (Real.exp_nonneg (4 * delta))
  nlinarith

theorem inverse_degree_gain (d t : ℝ) (hd : (1 + t) / 2 ≤ d)
    (ht : 0 ≤ t) (hsmall : t ≤ 1) :
    0 < d ∧ 1 / d ≤ 2 * Real.exp (-t / 2) := by
  have hdpos : 0 < d := by linarith
  refine ⟨hdpos, (div_le_iff₀ hdpos).mpr ?_⟩
  have hexp := Real.add_one_le_exp (-t / 2)
  have hpoly : 1 ≤ (1 + t) * (1 - t / 2) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1 + t by linarith)
  have hdeg := mul_le_mul_of_nonneg_right hd (Real.exp_nonneg (-t / 2))
  nlinarith

theorem internal_late_le_one (G : LowGeom PT) (v : Pos T k)
    (hCosets : ∀ a a', a ∈ PT.tiling.Icoord (G.patchOf v) →
      a' ∈ PT.tiling.Icoord (G.patchOf v) → G.ids a - G.ids a' ∈ G.Lsub → a = a') :
    ((PT.tiling.Icoord (G.patchOf v)).filter fun a =>
      (G.classOf (flipPos v a)).isSome).card ≤ 1 := by
  have hmem {z : Pos T k} (hz : (G.classOf z).isSome) : G.syndrome z ∈ G.Lsub := by
    by_contra hn
    simp [LowGeom.classOf, hn] at hz
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨haI, haL⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbI, hbL⟩ := Finset.mem_filter.mp hb
  apply hCosets a b haI hbI
  have hsub := G.Lsub.sub_mem (hmem haL) (hmem hbL)
  rw [HypercubeRamsey.Lane_q_s17_pool.lowGeom_syndrome_flip,
    HypercubeRamsey.Lane_q_s17_pool.lowGeom_syndrome_flip] at hsub
  simpa only [add_sub_add_left_eq_sub] using hsub

theorem remaining_zero_card {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k) :
    D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ =
      (Finset.univ.filter fun a : Fin (T.S.n k) =>
        (D.geom.classOf (flipPos v a)).isSome).card := by
  unfold LateData.remainingNeighbors
  apply congrArg Finset.card
  ext a
  simp only [LateData.remainingNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hc : D.geom.classOf (flipPos v a) <;> simp [hc]

theorem external_count_bounds {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k)
    (hle : (PT.tiling.P (D.geom.patchOf v)).h ≤ T.S.n k)
    (hInternal : ((PT.tiling.Icoord (D.geom.patchOf v)).filter fun a =>
      (D.geom.classOf (flipPos v a)).isSome).card ≤ 1) :
    T.S.n k ≤ (D.externalEarly v).card + (PT.tiling.P (D.geom.patchOf v)).h +
        D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ ∧
    (D.externalEarly v).card + (PT.tiling.P (D.geom.patchOf v)).h +
        D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ ≤ T.S.n k + 1 := by
  let I := PT.tiling.Icoord (D.geom.patchOf v)
  let L := Finset.univ.filter fun a : Fin (T.S.n k) =>
    (D.geom.classOf (flipPos v a)).isSome
  have hA : D.externalEarly v = Finset.univ \ (I ∪ L) := by
    ext a
    simp only [LateData.externalEarly, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_union, L, not_or]
    cases hc : D.geom.classOf (flipPos v a) <;> simp [hc, I]
  have hI : I.card = (PT.tiling.P (D.geom.patchOf v)).h :=
    HypercubeRamsey.Lane_q_s17_pool.tiling_internal_coord_card _ _ hle
  have hL : L.card = D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ :=
    (remaining_zero_card D v).symm
  have hIL : (I ∩ L).card ≤ 1 := by
    have heq : I ∩ L = I.filter fun a => (D.geom.classOf (flipPos v a)).isSome := by
      ext a
      simp [L]
    rw [heq]
    exact hInternal
  have hu := Finset.card_union_add_card_inter I L
  have hc := Finset.card_sdiff_of_subset (Finset.subset_univ (I ∪ L))
  have hub : (I ∪ L).card ≤ T.S.n k := (Finset.card_le_univ _).trans_eq (by simp)
  rw [← hA] at hc
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  constructor <;> omega

theorem external_crossing_count {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k)
    (hell : (PT.tiling.P (D.geom.patchOf v)).ℓ ≤ T.S.n k) :
    ((D.externalEarly v).filter fun a =>
      D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v).card ≤
      (PT.tiling.P (D.geom.patchOf v)).ℓ := by
  have hsub : (D.externalEarly v).filter (fun a =>
      D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v) ⊆
      Finset.univ.filter fun a : Fin (T.S.n k) => a.val < (PT.tiling.P (D.geom.patchOf v)).ℓ := by
    intro a ha
    have hne := (Finset.mem_filter.mp ha).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hn
    exact hne (HypercubeRamsey.Lane_q_s17_pool.lowGeom_patch_flip_of_after_prefix
      D.geom hPT v a (Nat.le_of_not_gt hn))
  exact (Finset.card_le_card hsub).trans_eq
    (HypercubeRamsey.Lane_q_s17_pool.fin_prefix_coord_card hell)

end HypercubeRamsey.S18.Lane_sol_d18l_pal
