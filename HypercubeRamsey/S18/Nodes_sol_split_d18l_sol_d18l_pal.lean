import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

theorem raw_row_bound {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k)
    (s : Config D.fresh) (hvalid : D.initialValid v s) (x : Fin (T.S.N k))
    (B : ℝ) (hPrior : D.sigma v s x ≤ B) (e : Fin (T.S.n k) → ℝ)
    (hdegree : ∀ a ∈ D.externalEarly v,
      0 < rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) ∧
      1 / rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) ≤ 2 * Real.exp (e a)) :
    D.initialWeight v s x ≤ B * (2 : ℝ) ^ (D.externalEarly v).card *
      Real.exp (∑ a ∈ D.externalEarly v, e a) := by
  have hprod : (∏ a ∈ D.externalEarly v,
      (if Hits (T.S.E k) PT.tiling.c x (D.earlyLabel s (flipPos v a)) then (1 : ℝ) else 0) /
        rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a)))) ≤
      (2 : ℝ) ^ (D.externalEarly v).card * Real.exp (∑ a ∈ D.externalEarly v, e a) := by
    calc
      _ ≤ ∏ a ∈ D.externalEarly v, 2 * Real.exp (e a) := by
        apply Finset.prod_le_prod₀
        · intro a ha
          apply div_nonneg
          · split_ifs <;> norm_num
          · exact (hdegree a ha).1.le
        · intro a ha
          split_ifs
          · exact (hdegree a ha).2
          · simp [Real.exp_nonneg]
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
  unfold LateData.initialWeight
  calc
    _ ≤ D.sigma v s x * ((2 : ℝ) ^ (D.externalEarly v).card *
        Real.exp (∑ a ∈ D.externalEarly v, e a)) :=
      mul_le_mul_of_nonneg_left hprod (hvalid.1.1 x)
    _ ≤ B * ((2 : ℝ) ^ (D.externalEarly v).card *
        Real.exp (∑ a ∈ D.externalEarly v, e a)) := mul_le_mul_of_nonneg_right hPrior (by positivity)
    _ = _ := by ring

theorem own_prior_supported {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k)
    (s : Config D.fresh) (hvalid : D.initialValid v s) (x : Fin (T.S.N k))
    (hx : D.sigma v s x ≠ 0) : x ∈ PT.envelope (D.geom.patchOf v) := by
  obtain ⟨q, hq, hSupport⟩ := hvalid.1.2.2.2.1
  have hxq : x ∈ PT.mesh.corner q (D.geom.patchOf v) := by
    by_contra hnot
    exact hx (hSupport x hnot)
  rw [hPT.envelope_eq]
  exact Finset.mem_biUnion.mpr ⟨q, hq, hxq⟩

theorem row_degree_eq (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) :
    rowDeg (T.S.E k) PT.tiling.c x (PT.π i) = deg (T.S.E k) PT.tiling.c (PT.π i).w x := rfl

theorem late_numeric_cutoff (T : Stage) (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) :
    ∀ᶠ k in Filter.atTop,
      1 ≤ Real.log (T.S.n k : ℝ) ∧
      1000 * (K + 2 * A / Real.log 2 + 1) * Real.log (T.S.n k : ℝ) ≤ T.S.n k ∧
      12 * bstar T k * Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ 1 := by
  have hn : Filter.Tendsto (fun k => (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  let C := K + 2 * A / Real.log 2 + 1
  have hC : 0 < C := by
    have hterm : 0 ≤ 2 * A / Real.log 2 := by positivity
    dsimp [C]
    linarith
  have hb := hn.eventually (Real.isLittleO_log_id_atTop.def
    (show (0 : ℝ) < 1 / (1000 * C) by positivity))
  have hp : Filter.Tendsto (fun k => (T.S.n k : ℝ) ^ (-(0.46 : ℝ))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.46)).comp hn
  have hp' := hp.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 12 by norm_num))
  have hlogsmall := hn.eventually (Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [(Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 1,
    hb, hp', hlogsmall] with k hlog hb hp hl
  change 1 ≤ Real.log (T.S.n k : ℝ) at hlog
  have hn0 : 0 ≤ (T.S.n k : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hn0, abs_of_nonneg hlog0] at hb hl
  refine ⟨hlog, ?_, ?_⟩
  · have hb' : Real.log (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) / (1000 * C) := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hb
    have := (le_div_iff₀ (show (0 : ℝ) < 1000 * C by positivity)).mp hb'
    dsimp [C] at this
    nlinarith
  · have hs : Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ Real.sqrt (T.S.n k : ℝ) :=
      Real.sqrt_le_sqrt (by simpa using hl)
    have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 12 * bstar T k by unfold bstar; positivity)
    have hnpos : 0 < (T.S.n k : ℝ) := by
      by_contra hn
      have hzero := le_antisymm (not_lt.mp hn) hn0
      rw [hzero] at hlog
      norm_num at hlog
    have hex : 12 * bstar T k * Real.sqrt (T.S.n k : ℝ) =
        12 * (T.S.n k : ℝ) ^ (-(0.46 : ℝ)) := by
      unfold bstar
      rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hnpos]
      norm_num
    rw [hex] at hmul
    exact hmul.trans (by linarith)

theorem cap_constant (hκ : κ.Admissible) (ht : LateThresholds κ) :
    1600 * Real.exp (8 * κ.Kbd) ≤ κ.KB := by
  have hbd : 1 ≤ κ.Kbd := hκ.bounded.2.2.2.1
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hmean : 0 ≤ rowMeanConstant κ := by unfold rowMeanConstant; positivity
  have hA : 0 ≤ κ.A0 := by nlinarith [hκ.A0_big]
  have hKB : Real.exp (100 * κ.Kbd) ≤ κ.KB := by linarith [ht.1]
  have h1600 : (1600 : ℝ) ≤ Real.exp 32 := by
    calc
      _ ≤ (9 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 8) ^ 4 := by gcongr; linarith [Real.add_one_le_exp 8]
      _ = Real.exp 32 := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp (92 * κ.Kbd) * Real.exp (8 * κ.Kbd) := by
      gcongr
      exact h1600.trans (Real.exp_le_exp.mpr (by linarith))
    _ = Real.exp (100 * κ.Kbd) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ κ.KB := hKB

theorem external_correction_sum {hPT : PT.Valid} (D : LateData hPT)
    (v : Pos T k) (c d : ℝ) :
    (∑ a ∈ D.externalEarly v, if D.geom.patchOf (flipPos v a) = D.geom.patchOf v then c else d) =
      c * (((D.externalEarly v).filter fun a => D.geom.patchOf (flipPos v a) = D.geom.patchOf v).card : ℝ) +
      d * (((D.externalEarly v).filter fun a => D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v).card : ℝ) := by
  rw [Finset.sum_ite]
  simp [mul_comm]

theorem uniform_prior_cap {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k)
    (s : Config D.fresh) (hvalid : D.initialValid v s) (hcluster : ¬ PT.tiling.mode.isCluster)
    (R : ℝ) (hR : 0 ≤ R) (hMass : (T.S.N k : ℝ) ≤ R * (PT.tiling.P (D.geom.patchOf v)).M) :
    ∀ x, D.sigma v s x ≤ 2 * R / T.S.N k := by
  have hshape := hvalid.1.2.2.1
  rw [if_neg hcluster] at hshape
  obtain ⟨q, hq, hσ⟩ := hshape
  have hcorner := hPT.corner_clean (D.geom.patchOf v) q hq
  have hcpos : (0 : ℝ) < (PT.mesh.corner q (D.geom.patchOf v)).card := by
    exact_mod_cast Finset.card_pos.mpr hcorner.nonempty
  have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hcMass : (T.S.N k : ℝ) ≤ 2 * R * (PT.mesh.corner q (D.geom.patchOf v)).card := by
    have hmul := mul_le_mul_of_nonneg_left hcorner.card_lower hR
    nlinarith
  intro x
  rw [hσ x]
  split_ifs
  · apply (div_le_div_iff₀ hcpos hNpos).mpr
    simpa using hcMass
  · positivity

theorem row_scale_factor (n h a p : ℕ) (hc : h + a + p ≤ n + 1) :
    (2 : ℝ) ^ h * (2 : ℝ) ^ a ≤
      2 * (2 : ℝ) ^ n * Real.rpow 2 (-(p : ℝ)) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (p : ℝ), Real.rpow_natCast,
    ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ p)).mpr
  calc
    _ = (2 : ℝ) ^ (h + a + p) := by rw [pow_add, pow_add]
    _ ≤ (2 : ℝ) ^ (n + 1) := by gcongr <;> norm_num
    _ = _ := by rw [pow_succ]; ring

theorem raw_atom_scalar {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k)
    (s : Config D.fresh) (hvalid : D.initialValid v s) (x : Fin (T.S.N k))
    (B E : ℝ) (hB : 0 ≤ B) (e : Fin (T.S.n k) → ℝ)
    (hPrior : D.sigma v s x ≤ (2 : ℝ) ^ (PT.tiling.P (D.geom.patchOf v)).h / T.S.N k * B)
    (hdegree : ∀ a ∈ D.externalEarly v,
      0 < rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) ∧
      1 / rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) ≤ 2 * Real.exp (e a))
    (he : (∑ a ∈ D.externalEarly v, e a) ≤ E)
    (hcount : (PT.tiling.P (D.geom.patchOf v)).h + (D.externalEarly v).card +
      D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ ≤ T.S.n k + 1) :
    D.initialWeight v s x ≤ 2 * B / densityScale T k * Real.exp E *
      Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) := by
  have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hp := row_scale_factor _ _ _ _ hcount
  have hexp := Real.exp_le_exp.mpr he
  have hraw := raw_row_bound D v s hvalid x _ hPrior e hdegree
  apply hraw.trans
  calc
    _ = B / T.S.N k * ((2 : ℝ) ^ (PT.tiling.P (D.geom.patchOf v)).h *
        (2 : ℝ) ^ (D.externalEarly v).card) * Real.exp (∑ a ∈ D.externalEarly v, e a) := by ring
    _ ≤ B / T.S.N k * (2 * (2 : ℝ) ^ T.S.n k *
        Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ))) * Real.exp E := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hp (div_nonneg hB hNpos.le)
      · exact hexp
      · exact Real.exp_nonneg _
      · exact mul_nonneg (div_nonneg hB hNpos.le)
          (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _))
    _ = _ := by
      unfold densityScale
      field_simp <;> ring


theorem remaining_zero_le_classes {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k) :
    D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ ≤ D.geom.r := by
  rw [remaining_zero_card]
  let S := Finset.univ.filter fun a : Fin (T.S.n k) =>
    (D.geom.classOf (flipPos v a)).isSome
  let f : S → Fin D.geom.r := fun a =>
    (D.geom.classOf (flipPos v a)).get (Finset.mem_filter.mp a.2).2
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply D.l16_valid.one_per_class v (f a)
    · exact (Option.some_get _).symm
    · rw [hab]
      exact (Option.some_get _).symm
  have hc := Fintype.card_le_of_injective f hf
  change S.card ≤ D.geom.r
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

theorem crossing_degree {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k)
    (x : Fin (T.S.N k)) (hx : x ∈ PT.envelope (D.geom.patchOf v))
    (hb : 3 * bstar T k ≤ 1 / 4) (a : Fin (T.S.n k))
    (ha : D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v) :
    0 < rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) ∧
    1 / rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) ≤
      2 * Real.exp (12 * bstar T k) := by
  have hd := (abs_le.mp (hPT.envelope_other_degree _ _ ha x hx)).1
  have hlow : 1 / 2 - 3 * bstar T k ≤ rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) := by
    rw [row_degree_eq]
    linarith
  convert inverse_degree_lower _ (3 * bstar T k) hlow (by unfold bstar; positivity) hb using 1 <;> congr 2 <;> ring

theorem bounded_atom {hPT : PT.Valid} (D : LateData hPT)
    (hm : PT.tiling.mode = .bounded) (hn : 0 < (T.S.n k : ℝ))
    (hsmall : κ.Kbd / T.S.n k ≤ 1 / 4) (hbd : 1 ≤ κ.Kbd)
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.initialValid v s) :
    ∀ x, D.initialWeight v s x ≤
      1600 / densityScale T k * Real.exp (4 * κ.Kbd) *
      Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) := by
  have hd := (hPT.tiling_valid.bounded_data hm).2 (D.geom.patchOf v)
  have hc : ¬ PT.tiling.mode.isCluster := by simp [hm, Mode.isCluster]
  have hprior := uniform_prior_cap D v s hvalid hc 400 (by norm_num) (by linarith [hd.2.2.2.1])
  have hcount := (external_count_bounds D v (by rw [hd.2.1]; omega)
    (internal_late_le_one D.geom v (D.l16_valid.internal_cosets _))).2
  have hcard : (D.externalEarly v).card ≤ T.S.n k :=
    (Finset.card_le_univ _).trans_eq (by simp)
  have hCpos : 0 < densityScale T k := by
    unfold densityScale
    have : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    positivity
  intro x
  by_cases hx : D.sigma v s x = 0
  · simp only [LateData.initialWeight, hx, zero_mul]
    exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hCpos.le) (Real.exp_nonneg _))
      (Real.rpow_nonneg (by norm_num) _)
  have hxenv := own_prior_supported D v s hvalid x hx
  have hrow := raw_atom_scalar D v s hvalid x 800 (4 * κ.Kbd) (by norm_num)
    (fun _ => 4 * κ.Kbd / T.S.n k) (by convert hprior x using 1 <;> simp [hd.2.1] <;> ring) ?_ ?_ (by omega)
  · convert hrow using 1 <;> ring
  · intro a ha
    have hp : D.geom.patchOf (flipPos v a) = D.geom.patchOf v := by
      apply HypercubeRamsey.Lane_q_s17_pool.lowGeom_patch_flip_of_after_prefix D.geom hPT
      rw [hd.1]
      omega
    rw [hp, row_degree_eq]
    have hdeg := hPT.envelope_degree _ x hxenv
    simp only [OwnDegOK, hm] at hdeg
    have hl := (abs_le.mp hdeg).1
    simpa [mul_div_assoc] using inverse_degree_lower _ (κ.Kbd / T.S.n k)
      (by linarith) (by positivity) hsmall
  · simp only [Finset.sum_const, nsmul_eq_mul]
    have hcr : ((D.externalEarly v).card : ℝ) ≤ T.S.n k := by exact_mod_cast hcard
    calc
      _ ≤ (T.S.n k : ℝ) * (4 * κ.Kbd / T.S.n k) := by gcongr
      _ = _ := by field_simp


theorem cluster_atom {hPT : PT.Valid} (D : LateData hPT)
    (hm : PT.tiling.mode = .lowCluster) (hn : 0 < (T.S.n k : ℝ))
    (hb : 3 * bstar T k ≤ 1 / 4)
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.initialValid v s)
    (hle : (PT.tiling.P (D.geom.patchOf v)).h ≤ T.S.n k)
    (hell : (PT.tiling.P (D.geom.patchOf v)).ℓ ≤ T.S.n k)
    (hcross : 12 * bstar T k * (PT.tiling.P (D.geom.patchOf v)).ℓ ≤ 1)
    (hOwn : 40 * Real.rpow ((PT.tiling.P (D.geom.patchOf v)).q : ℝ) κ.Cb ≤
      PT.tiling.gain (D.geom.patchOf v))
    (hg1 : 1 ≤ PT.tiling.gain (D.geom.patchOf v))
    (hgn : PT.tiling.gain (D.geom.patchOf v) ≤ T.S.n k) :
    ∀ x, D.initialWeight v s x ≤ 2 / densityScale T k *
      Real.exp (-498 * PT.tiling.gain (D.geom.patchOf v)) *
      Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) := by
  let g := PT.tiling.gain (D.geom.patchOf v)
  let Q := Real.rpow ((PT.tiling.P (D.geom.patchOf v)).q : ℝ) κ.Cb
  have hQ : 0 ≤ Q := Real.rpow_nonneg (by positivity) _
  change 40 * Q ≤ g at hOwn
  change g ≤ (T.S.n k : ℝ) at hgn
  have hsmall : 10 * Q / T.S.n k ≤ 1 / 4 := by
    apply (div_le_iff₀ hn).mpr
    linarith
  have hcount := (external_count_bounds D v hle
    (internal_late_le_one D.geom v (D.l16_valid.internal_cosets _))).2
  have hCpos : 0 < densityScale T k := by
    unfold densityScale
    have : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    positivity
  have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hshape := hvalid.1.2.2.1
  rw [if_pos (show PT.tiling.mode.isCluster by simp [hm, Mode.isCluster])] at hshape
  let e := fun a : Fin (T.S.n k) =>
    if D.geom.patchOf (flipPos v a) = D.geom.patchOf v then 40 * Q / T.S.n k else 12 * bstar T k
  intro x
  by_cases hx : D.sigma v s x = 0
  · simp only [LateData.initialWeight, hx, zero_mul]
    exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hCpos.le) (Real.exp_nonneg _))
      (Real.rpow_nonneg (by norm_num) _)
  have hxenv := own_prior_supported D v s hvalid x hx
  have hprior : D.sigma v s x ≤ (2 : ℝ) ^ (PT.tiling.P (D.geom.patchOf v)).h /
      T.S.N k * Real.exp (-500 * g) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hNpos).mpr
    simpa only [g, mul_comm] using hshape x
  have hrow := raw_atom_scalar D v s hvalid x (Real.exp (-500 * g)) (2 * g)
    (by positivity) e hprior ?_ ?_ (by omega)
  · convert hrow using 1
    rw [show -498 * PT.tiling.gain (D.geom.patchOf v) = -500 * g + 2 * g by dsimp [g]; ring, Real.exp_add]
    ring
  · intro a ha
    dsimp [e]
    split_ifs with hp
    · rw [hp, row_degree_eq]
      have hdeg := hPT.envelope_degree _ x hxenv
      simp only [OwnDegOK, hm] at hdeg
      change |deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x - 1 / 2| ≤ 10 * Q / T.S.n k at hdeg
      have hl : 1 / 2 - 10 * Q / T.S.n k ≤ deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x := by linarith [(abs_le.mp hdeg).1]
      convert inverse_degree_lower (deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x)
        (10 * Q / T.S.n k) hl (by positivity) hsmall using 1 <;> congr 2 <;> ring
    · exact crossing_degree D v x hxenv hb a hp
  · dsimp [e]
    rw [external_correction_sum]
    have hc1 : (((D.externalEarly v).filter fun a =>
      D.geom.patchOf (flipPos v a) = D.geom.patchOf v).card : ℝ) ≤ T.S.n k := by
      exact_mod_cast ((Finset.card_le_univ _).trans_eq (by simp) :
        ((D.externalEarly v).filter fun a => D.geom.patchOf (flipPos v a) = D.geom.patchOf v).card ≤ T.S.n k)
    have hc2 : (((D.externalEarly v).filter fun a =>
      D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v).card : ℝ) ≤ (PT.tiling.P (D.geom.patchOf v)).ℓ := by
      exact_mod_cast external_crossing_count D v hell
    have h1 : 40 * Q / T.S.n k * (((D.externalEarly v).filter fun a =>
      D.geom.patchOf (flipPos v a) = D.geom.patchOf v).card : ℝ) ≤ g := by
      calc
        _ ≤ 40 * Q / T.S.n k * T.S.n k := by gcongr
        _ = 40 * Q := div_mul_cancel₀ _ hn.ne'
        _ ≤ g := hOwn
    have h2 : 12 * bstar T k * (((D.externalEarly v).filter fun a =>
      D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v).card : ℝ) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hc2 (by unfold bstar; positivity)).trans hcross
    dsimp [g] at *
    linarith


theorem direct_atom {hPT : PT.Valid} (D : LateData hPT)
    (hm : PT.tiling.mode = .lowDirect) (hn : 0 < (T.S.n k : ℝ))
    (hb : 3 * bstar T k ≤ 1 / 4)
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.initialValid v s)
    (hell : (PT.tiling.P (D.geom.patchOf v)).ℓ ≤ T.S.n k)
    (hcross : 12 * bstar T k * (PT.tiling.P (D.geom.patchOf v)).ℓ ≤ 1)
    (hbudget : (D.geom.r : ℝ) + (PT.tiling.P (D.geom.patchOf v)).ℓ ≤ (T.S.n k : ℝ) / 10)
    (hgn : ((PT.tiling.P (D.geom.patchOf v)).g : ℝ) ≤ 2 * T.S.n k)
    (hgpow : Real.rpow ((PT.tiling.P (D.geom.patchOf v)).g : ℝ) κ.aB + 1 ≤
      ((PT.tiling.P (D.geom.patchOf v)).g : ℝ) / 40) :
    ∀ x, D.initialWeight v s x ≤ 1600 / densityScale T k *
      Real.exp (-200 * PT.tiling.gain (D.geom.patchOf v)) *
      Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) := by
  let g : ℝ := (PT.tiling.P (D.geom.patchOf v)).g
  let b := Real.rpow g κ.aB
  have hg : 0 ≤ g := by positivity
  have hdata := hPT.tiling_valid.direct_data (Or.inl hm) (D.geom.patchOf v)
  have hc : ¬ PT.tiling.mode.isCluster := by simp [hm, Mode.isCluster]
  have hmass : (T.S.N k : ℝ) ≤ (400 * Real.exp b) * (PT.tiling.P (D.geom.patchOf v)).M := by
    calc
      _ = (400 * Real.exp b) * ((1 / 400 : ℝ) * T.S.N k * Real.exp (-b)) := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hdata.2.2.1 (by positivity)
  have hprior := uniform_prior_cap D v s hvalid hc (400 * Real.exp b) (by positivity) hmass
  have hcounts := external_count_bounds D v (by rw [hdata.2.2.2.2.1]; omega)
    (internal_late_le_one D.geom v (D.l16_valid.internal_cosets _))
  have hp := remaining_zero_le_classes D v
  have hsplit := Finset.card_filter_add_card_filter_not (s := D.externalEarly v)
    (p := fun a => D.geom.patchOf (flipPos v a) = D.geom.patchOf v)
  have hcrosscard := external_crossing_count D v hell
  have hself : (9 / 10 : ℝ) * T.S.n k ≤
      (((D.externalEarly v).filter fun a => D.geom.patchOf (flipPos v a) = D.geom.patchOf v).card : ℝ) := by
    have ha : T.S.n k ≤ (D.externalEarly v).card + D.geom.r := by
      rw [hdata.2.2.2.2.1] at hcounts
      omega
    have ha' : (T.S.n k : ℝ) ≤ (D.externalEarly v).card + D.geom.r := by exact_mod_cast ha
    have hs' : (((D.externalEarly v).filter fun a => D.geom.patchOf (flipPos v a) = D.geom.patchOf v).card : ℝ) +
        (((D.externalEarly v).filter fun a => D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v).card : ℝ) =
        (D.externalEarly v).card := by exact_mod_cast hsplit
    have hcc : (((D.externalEarly v).filter fun a => D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v).card : ℝ) ≤
      (PT.tiling.P (D.geom.patchOf v)).ℓ := by exact_mod_cast hcrosscard
    linarith
  let e := fun a : Fin (T.S.n k) => if D.geom.patchOf (flipPos v a) = D.geom.patchOf v
    then -g / (4 * T.S.n k) else 12 * bstar T k
  have hCpos : 0 < densityScale T k := by
    unfold densityScale
    have : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    positivity
  intro x
  by_cases hx : D.sigma v s x = 0
  · simp only [LateData.initialWeight, hx, zero_mul]
    exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hCpos.le) (Real.exp_nonneg _))
      (Real.rpow_nonneg (by norm_num) _)
  have hxenv := own_prior_supported D v s hvalid x hx
  have hrow := raw_atom_scalar D v s hvalid x (800 * Real.exp b) (1 - 9 * g / 40)
    (by positivity) e (by convert hprior x using 1 <;> simp [hdata.2.2.2.2.1] <;> ring) ?_ ?_ (by omega)
  · calc
      _ ≤ 2 * (800 * Real.exp b) / densityScale T k * Real.exp (1 - 9 * g / 40) *
          Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) := hrow
      _ = 1600 / densityScale T k * Real.exp (b + 1 - 9 * g / 40) *
          Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) := by
        rw [show b + 1 - 9 * g / 40 = b + (1 - 9 * g / 40) by ring, Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        simp only [Tiling.gain, hm]
        dsimp [g, b] at *
        linarith
  · intro a ha
    dsimp [e]
    split_ifs with hp
    · rw [hp, row_degree_eq]
      have hdeg := hPT.envelope_degree _ x hxenv
      simp only [OwnDegOK, hm] at hdeg
      have hsmall : g / (2 * T.S.n k) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by simpa [g] using hgn)
      have hl : (1 + g / (2 * T.S.n k)) / 2 ≤ deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x := by
        dsimp [g]
        convert hdeg.1 using 1 <;> ring
      convert inverse_degree_gain (deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x) (g / (2 * T.S.n k)) hl (by positivity) hsmall using 1 <;> congr 2 <;> ring
    · exact crossing_degree D v x hxenv hb a hp
  · dsimp [e]
    rw [external_correction_sum]
    have h1 : -g / (4 * T.S.n k) * (((D.externalEarly v).filter fun a =>
      D.geom.patchOf (flipPos v a) = D.geom.patchOf v).card : ℝ) ≤ -9 * g / 40 := by
      calc
        _ ≤ -g / (4 * T.S.n k) * ((9 / 10 : ℝ) * T.S.n k) :=
          mul_le_mul_of_nonpos_left hself (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg) (by positivity))
        _ = _ := by field_simp; ring
    have h2 : 12 * bstar T k * (((D.externalEarly v).filter fun a =>
      D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v).card : ℝ) ≤ 1 := by
      have hc' : (((D.externalEarly v).filter fun a =>
        D.geom.patchOf (flipPos v a) ≠ D.geom.patchOf v).card : ℝ) ≤ (PT.tiling.P (D.geom.patchOf v)).ℓ := by
        exact_mod_cast hcrosscard
      exact (mul_le_mul_of_nonneg_left hc' (by unfold bstar; positivity)).trans hcross
    linarith


theorem admissible_u_one (hκ : κ.Admissible) : (1 : ℝ) ≤ κ.u := by
  have hnat : 1 ≤ κ.u := by have := hκ.u_rng.2; omega
  exact_mod_cast hnat

theorem direct_gain_controls (hκ : κ.Admissible) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .lowDirect) (i : Fin PT.tiling.m) :
    Real.rpow ((PT.tiling.P i).g : ℝ) κ.aB + 1 ≤ ((PT.tiling.P i).g : ℝ) / 40 := by
  have hd := hPT.tiling_valid.direct_data (Or.inl hm) i
  have hM : 0 < κ.M1 := by linarith [hκ.M1_big.1]
  have hqg : ((PT.tiling.P i).q : ℝ) ≤ ((PT.tiling.P i).g : ℝ) := by
    have hq : (0 : ℝ) ≤ (PT.tiling.P i).q := by positivity
    nlinarith [hd.2.1, hκ.M1_big.1]
  have hth : κ.M1 * κ.Q0 ≤ ((PT.tiling.P i).g : ℝ) := by
    simpa only [Nat.cast_max, max_eq_left hqg] using hd.1
  have hq0 : κ.Q0 ≤ ((PT.tiling.P i).g : ℝ) / κ.M1 :=
    (le_div_iff₀ hM).mpr (by nlinarith)
  have hc := (hκ.Q0_large _ hq0).2.2.1
  rw [mul_div_cancel₀ _ hM.ne'] at hc
  have hu := admissible_u_one hκ
  have hsmall : ((PT.tiling.P i).g : ℝ) / (10 ^ 6 * κ.u) ≤ ((PT.tiling.P i).g : ℝ) / 40 := by
    gcongr <;> norm_num <;> linarith
  linarith

theorem cluster_gain_controls (hκ : κ.Admissible) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .lowCluster) (i : Fin PT.tiling.m) :
    40 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb ≤ PT.tiling.gain i ∧
      1 ≤ PT.tiling.gain i := by
  have hd := hPT.tiling_valid.cluster_data (Or.inl hm) i
  have hM : 0 < κ.M1 := by linarith [hκ.M1_big.1]
  have hmax : max ((PT.tiling.P i).g : ℝ) ((PT.tiling.P i).q : ℝ) ≤ κ.M1 * (PT.tiling.P i).q := by
    apply max_le hd.2.1
    nlinarith [(show (0 : ℝ) ≤ (PT.tiling.P i).q by positivity), hκ.M1_big.1]
  have hth : κ.M1 * κ.Q0 ≤ max ((PT.tiling.P i).g : ℝ) ((PT.tiling.P i).q : ℝ) := by
    simpa only [Nat.cast_max] using hd.1
  have hq0 : κ.Q0 ≤ ((PT.tiling.P i).q : ℝ) := by nlinarith [hth.trans hmax]
  rcases hκ.Q0_large _ hq0 with ⟨_, hpow, _, _, _, _, _, hQ, _⟩
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hu := admissible_u_one hκ
  have hheight := hd.2.2.2.2.2.2.2.1
  simp only [hm, ite_true] at hheight
  have hterm : (κ.a / 10 ^ 6) * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mlo ≤ PT.tiling.gain i := by
    have hh := mul_le_mul_of_nonneg_left hheight (show 0 ≤ κ.a / 10 ^ 6 by positivity)
    simp only [Tiling.gain, hm]
    convert hh using 1 <;> ring
  have hg0 : 0 ≤ PT.tiling.gain i := by simp only [Tiling.gain, hm]; positivity
  have hden : 0 < (100 * (κ.u : ℝ)) := by positivity
  have hden' : 0 < (1000 * (κ.u : ℝ)) := by positivity
  have hQ' : 40 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb ≤ PT.tiling.gain i / (100 * κ.u) :=
    hQ.trans (div_le_div_of_nonneg_right hterm hden.le)
  constructor
  · exact hQ'.trans ((div_le_iff₀ hden).mpr (by nlinarith))
  · have hpow' := hpow.trans (div_le_div_of_nonneg_right hterm hden'.le)
    have hr : 0 ≤ Real.rpow ((PT.tiling.P i).q : ℝ) κ.aC := Real.rpow_nonneg (by positivity) _
    have hbig : 10 ≤ PT.tiling.gain i / (1000 * κ.u) := by linarith
    have hbig' := (le_div_iff₀ hden').mp hbig
    nlinarith


theorem raw_initial_atom_cap (hκ : κ.Admissible) (ht : LateThresholds κ) (T : Stage) :
    ∀ᶠ k in Filter.atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT),
      (∀ i, ((PT.tiling.P i).ℓ : ℝ) ≤ Real.sqrt (Real.log (T.S.n k : ℝ))) →
      (∀ i, (PT.tiling.P i).h ≤ T.S.n k) →
      ∀ v s, D.initialValid v s → ∀ x,
        D.initialWeight v s x ≤ κ.KB / densityScale T k *
          Real.exp (-200 * PT.tiling.gain (D.geom.patchOf v)) *
          Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) := by
  have hbd : 1 ≤ κ.Kbd := hκ.bounded.2.2.2.1
  have hA : 0 ≤ κ.A0 := (show (0 : ℝ) ≤ 10 ^ 6 * κ.R by positivity).trans hκ.A0_big
  have hc := cap_constant hκ ht
  have h1600 : (1600 : ℝ) ≤ κ.KB := by
    have he : 1 ≤ Real.exp (8 * κ.Kbd) := Real.one_le_exp_iff.mpr (by linarith)
    linarith
  have hKB : 0 ≤ κ.KB := by linarith
  filter_upwards [late_numeric_cutoff T (1000 * κ.KB + κ.Kbd) κ.A0 (by positivity) hA,
    T.S.n_tendsto.eventually_ge_atTop 1] with k hk hn
  intro PT hPT D hprefix hheight v s hvalid x
  have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hCpos : 0 < densityScale T k := by
    unfold densityScale
    have : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    positivity
  have hrpow : 0 ≤ Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  let L := Real.log (T.S.n k : ℝ)
  let C := 1000 * κ.KB + κ.Kbd + 2 * κ.A0 / Real.log 2 + 1
  have hL : 1 ≤ L := hk.1
  have hL0 : 0 ≤ L := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hcut : 1000 * C * L ≤ T.S.n k := hk.2.1
  have hcl : C * L ≤ (T.S.n k : ℝ) / 1000 := by linarith
  have hterm : 0 ≤ 2 * κ.A0 / Real.log 2 := by positivity
  have hKBC : 1000 * κ.KB ≤ C := by dsimp [C]; linarith
  have hbdC : κ.Kbd ≤ C := by dsimp [C]; linarith
  have hAC : 2 * κ.A0 / Real.log 2 + 1 ≤ C := by dsimp [C]; linarith
  have hKBL : 1000 * κ.KB * L ≤ (T.S.n k : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hKBC hL0
    linarith
  have hbdn : 4 * κ.Kbd ≤ (T.S.n k : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hbdC hL0
    have hh' : κ.Kbd ≤ κ.Kbd * L := by nlinarith
    linarith
  have hsqrt : 1 ≤ Real.sqrt L := by
    have hh := Real.sqrt_le_sqrt hL
    simpa only [Real.sqrt_one] using hh
  have hsqrtL : Real.sqrt L ≤ L := by nlinarith [Real.sq_sqrt hL0, Real.sqrt_nonneg L]
  have hellL : ((PT.tiling.P (D.geom.patchOf v)).ℓ : ℝ) ≤ L :=
    (hprefix _).trans hsqrtL
  have hrl : (D.geom.r : ℝ) ≤ 2 * κ.A0 / Real.log 2 * L := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    exact D.l16_valid.r_upper
  have hbudget : (D.geom.r : ℝ) + (PT.tiling.P (D.geom.patchOf v)).ℓ ≤ (T.S.n k : ℝ) / 10 := by
    have hh := mul_le_mul_of_nonneg_right hAC hL0
    linarith
  have hell : (PT.tiling.P (D.geom.patchOf v)).ℓ ≤ T.S.n k := by
    have hr : (0 : ℝ) ≤ D.geom.r := by positivity
    have hh : ((PT.tiling.P (D.geom.patchOf v)).ℓ : ℝ) ≤ T.S.n k := by linarith
    exact_mod_cast hh
  have hb0 : 0 ≤ bstar T k := by unfold bstar; positivity
  have hb : 3 * bstar T k ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 12 * bstar T k by positivity)
    nlinarith [hk.2.2]
  have hcross : 12 * bstar T k * (PT.tiling.P (D.geom.patchOf v)).ℓ ≤ 1 :=
    (mul_le_mul_of_nonneg_left (hprefix _) (by positivity)).trans hk.2.2
  have hgain := D.l16_valid.gain_upper (D.geom.patchOf v)
  change PT.tiling.gain (D.geom.patchOf v) ≤ κ.KB * L at hgain
  have hgn : PT.tiling.gain (D.geom.patchOf v) ≤ T.S.n k := by
    nlinarith [mul_nonneg hKB hL0]
  cases hm : PT.tiling.mode with
  | bounded =>
    have hsmall : κ.Kbd / T.S.n k ≤ 1 / 4 := (div_le_iff₀ hnpos).mpr (by linarith)
    have hraw := bounded_atom D hm hnpos hsmall hbd v s hvalid x
    have he : 1600 * Real.exp (4 * κ.Kbd) ≤ κ.KB :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : 4 * κ.Kbd ≤ 8 * κ.Kbd)) (by norm_num)).trans hc
    simp only [Tiling.gain, hm, mul_zero, Real.exp_zero, mul_one]
    calc
      _ ≤ 1600 / densityScale T k * Real.exp (4 * κ.Kbd) * _ := hraw
      _ = (1600 * Real.exp (4 * κ.Kbd)) / densityScale T k * _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right he hCpos.le) hrpow
  | lowDirect =>
    have hg : ((PT.tiling.P (D.geom.patchOf v)).g : ℝ) ≤ 2 * T.S.n k := by
      simp only [Tiling.gain, hm] at hgain
      nlinarith
    have hraw := direct_atom D hm hnpos hb v s hvalid hell hcross hbudget hg
      (direct_gain_controls hκ hPT hm _) x
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h1600 hCpos.le) (Real.exp_nonneg _)) hrpow)
  | lowCluster =>
    obtain ⟨hOwn, hg1⟩ := cluster_gain_controls hκ hPT hm (D.geom.patchOf v)
    have hraw := cluster_atom D hm hnpos hb v s hvalid (hheight _) hell hcross hOwn hg1 hgn x
    apply hraw.trans
    apply mul_le_mul_of_nonneg_right _ hrpow
    apply mul_le_mul
    · exact div_le_div_of_nonneg_right (by linarith : (2 : ℝ) ≤ κ.KB) hCpos.le
    · exact Real.exp_le_exp.mpr (by linarith)
    · exact Real.exp_nonneg _
    · positivity
  | highDirect => have := D.low_mode; simp [hm, Mode.isLow] at this
  | highSmall => have := D.low_mode; simp [hm, Mode.isLow] at this
  | highLarge => have := D.low_mode; simp [hm, Mode.isLow] at this

end HypercubeRamsey.S18.Lane_sol_d18l_pal
