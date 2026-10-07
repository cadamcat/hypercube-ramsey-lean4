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

end HypercubeRamsey.S18.Lane_sol_d18l_pal
