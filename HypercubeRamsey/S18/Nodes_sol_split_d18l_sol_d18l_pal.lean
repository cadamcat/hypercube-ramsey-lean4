import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import HypercubeRamsey.Tools.LinearCode
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.S17.Nodes
import HypercubeRamsey.S18.Lists
import HypercubeRamsey.S18.Nodes_sol_s18_dl

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
    (s : Config D.fresh) (hvalid : D.internalValid v s) (x : Fin (T.S.N k))
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
      mul_le_mul_of_nonneg_left hprod (hvalid.1 x)
    _ ≤ B * ((2 : ℝ) ^ (D.externalEarly v).card *
        Real.exp (∑ a ∈ D.externalEarly v, e a)) := mul_le_mul_of_nonneg_right hPrior (by positivity)
    _ = _ := by ring

theorem own_prior_supported {hPT : PT.Valid} (D : LateData hPT) (v : Pos T k)
    (s : Config D.fresh) (hvalid : D.internalValid v s) (x : Fin (T.S.N k))
    (hx : D.sigma v s x ≠ 0) : x ∈ PT.envelope (D.geom.patchOf v) := by
  obtain ⟨q, hq, hSupport⟩ := hvalid.2.2.2.1
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
    (s : Config D.fresh) (hvalid : D.internalValid v s) (hcluster : ¬ PT.tiling.mode.isCluster)
    (R : ℝ) (hR : 0 ≤ R) (hMass : (T.S.N k : ℝ) ≤ R * (PT.tiling.P (D.geom.patchOf v)).M) :
    ∀ x, D.sigma v s x ≤ 2 * R / T.S.N k := by
  have hshape := hvalid.2.2.1
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
    (s : Config D.fresh) (hvalid : D.internalValid v s) (x : Fin (T.S.N k))
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
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.internalValid v s) :
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
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.internalValid v s)
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
  have hshape := hvalid.2.2.1
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
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.internalValid v s)
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
        _ = _ := by field_simp <;> ring
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


theorem raw_internal_atom_cap (hκ : κ.Admissible) (ht : LateThresholds κ) (T : Stage) :
    ∀ᶠ k in Filter.atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT),
      (∀ i, ((PT.tiling.P i).ℓ : ℝ) ≤ Real.sqrt (Real.log (T.S.n k : ℝ))) →
      (∀ i, (PT.tiling.P i).h ≤ T.S.n k) →
      ∀ v s, D.internalValid v s → ∀ x,
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



theorem raw_initial_atom_cap (hκ : κ.Admissible) (ht : LateThresholds κ) (T : Stage) :
    ∀ᶠ k in Filter.atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT),
      (∀ i, ((PT.tiling.P i).ℓ : ℝ) ≤ Real.sqrt (Real.log (T.S.n k : ℝ))) →
      (∀ i, (PT.tiling.P i).h ≤ T.S.n k) →
      ∀ v s, D.initialValid v s → ∀ x,
        D.initialWeight v s x ≤ κ.KB / densityScale T k *
          Real.exp (-200 * PT.tiling.gain (D.geom.patchOf v)) *
          Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ)) := by
  filter_upwards [raw_internal_atom_cap hκ ht T] with k hk
  intro PT hPT D hprefix hheight v s hvalid
  exact hk D hprefix hheight v s hvalid.1

theorem admissible_a_le_one (hκ : κ.Admissible) : κ.a ≤ 1 := by
  have hp : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (by positivity))
  have hξ : κ.ξ ≤ 1 := by nlinarith [hκ.ξ_rng.2, hκ.α_rng.1, hκ.α_rng.2]
  have hpow : (1 : ℝ) ≤ 4 ^ (κ.u + 3) := one_le_pow₀ (by norm_num)
  have hden : (0 : ℝ) < 3 * 4 ^ (κ.u + 3) := by positivity
  have hθ := (lt_div_iff₀ hden).mp hκ.θ_rng.2
  rw [hκ.a_eq]
  nlinarith [hκ.θ_rng.1, hκ.ξ_rng.1]

theorem range_binomial_entropy (h w : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hw : (w : ℝ) ≤ r * h) :
    (∑ j ∈ Finset.range (w + 1), (Nat.choose h j : ℝ)) ≤ Real.exp (Real.binEntropy r * h) := by
  classical
  have wh : w ≤ h := by
    have : (w : ℝ) ≤ h := by nlinarith [(show (0 : ℝ) ≤ h by positivity)]
    exact_mod_cast this
  let A : Finset ℕ := (Finset.range (h + 1)).filter fun j => (j : ℝ) ≤ r * h
  have hsub : Finset.range (w + 1) ⊆ A := by
    intro j hj
    have hjw : j ≤ w := by simpa using Finset.mem_range.mp hj
    have hjr : (j : ℝ) ≤ r * h := (Nat.cast_le.mpr hjw).trans hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjr⟩
  have hsum : (∑ j ∈ Finset.range (w + 1), (Nat.choose h j : ℝ)) ≤
      ∑ j ∈ A, (Nat.choose h j : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro j hj hjA; positivity)
  have hA : (∑ j ∈ A, (Nat.choose h j : ℝ)) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (h + 1) => (j.val : ℝ) ≤ r * h),
        (Nat.choose h j.val : ℝ) := by
    simp only [A, Finset.sum_filter]
    exact (Fin.sum_univ_eq_sum_range (fun j => if (j : ℝ) ≤ r * h then (Nat.choose h j : ℝ) else 0) (h + 1)).symm
  rw [hA] at hsum
  exact hsum.trans (binomialEntropyBound h r hr0 hr)

theorem admissible_entropy (hκ : κ.Admissible) :
    Real.binEntropy (1000 * κ.ρ) < κ.a / 10 ^ 9 := by
  classical
  have hr0 : 0 < 1000 * κ.ρ := by linarith [hκ.ρ_rng.1]
  have hr1 : 1000 * κ.ρ < 1 := by linarith [hκ.ρ_rng.2.1]
  have heq : binEntropy (1000 * κ.ρ) = Real.binEntropy (1000 * κ.ρ) := by
    rw [binEntropy, if_neg hr0.ne', if_neg hr1.ne]
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    ring
  rw [← heq]
  exact hκ.ρ_rng.2.2

theorem separating_kernel (hκ : κ.Admissible) (h : ℕ)
    (hg : 1 ≤ κ.a * h / 10 ^ 6) :
    ∃ m : ℕ, ∃ L : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
      Function.Surjective L ∧
      (∀ z, L z = 0 → z ≠ 0 → (internalWeight z : ℝ) ≤ 500 * κ.ρ * h → False) ∧
      (2 : ℝ) ^ m ≤ Real.exp (κ.a * h / 10 ^ 6) := by
  classical
  let g : ℝ := κ.a * h / 10 ^ 6
  let m := ⌊g / Real.log 2⌋₊
  let w := ⌊500 * κ.ρ * h⌋₊
  have hg0 : 0 ≤ g := by dsimp [g]; linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlu : Real.log 2 < 3 / 4 := by linarith [Real.log_two_lt_d9]
  have ha0 : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have ha1 := admissible_a_le_one hκ
  have hmle : (m : ℝ) ≤ g / Real.log 2 := Nat.floor_le (div_nonneg hg0 hl0.le)
  have hmlo : g / Real.log 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmh : m ≤ h := by
    have hh : g / Real.log 2 ≤ (h : ℝ) := by
      apply (div_le_iff₀ hl0).mpr
      dsimp [g]
      nlinarith [(show (0 : ℝ) ≤ h by positivity)]
    exact_mod_cast hmle.trans hh
  have hrho : 0 < κ.ρ := hκ.ρ_rng.1
  have hw0 : 0 ≤ 500 * κ.ρ * (h : ℝ) := by positivity
  have hwle : (w : ℝ) ≤ 500 * κ.ρ * h := Nat.floor_le hw0
  have hwh : w ≤ h := by
    have hh : (w : ℝ) ≤ h := by nlinarith [hκ.ρ_rng.2.1, (show (0 : ℝ) ≤ h by positivity)]
    exact_mod_cast hh
  have hvolR := range_binomial_entropy h w (1000 * κ.ρ) (by positivity)
    (by linarith [hκ.ρ_rng.2.1]) (by nlinarith)
  have hhpos : (0 : ℝ) < h := by dsimp [g] at hg0; nlinarith [hg]
  have he : Real.binEntropy (1000 * κ.ρ) * h < g / 1000 := by
    have he' := mul_lt_mul_of_pos_right (admissible_entropy hκ) hhpos
    dsimp [g]
    nlinarith
  have hmLog : g / 1000 < (m : ℝ) * Real.log 2 := by
    have hmlo' := (div_lt_iff₀ hl0).mp hmlo
    change 1 ≤ g at hg
    nlinarith
  have hvol : (∑ j ∈ Finset.range (w + 1), Nat.choose h j) < 2 ^ m := by
    have hv : (∑ j ∈ Finset.range (w + 1), (Nat.choose h j : ℝ)) < (2 : ℝ) ^ m := by
      apply lt_of_le_of_lt hvolR
      calc
        _ < Real.exp ((m : ℝ) * Real.log 2) := Real.exp_lt_exp.mpr (he.trans hmLog)
        _ = (2 : ℝ) ^ m := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    exact_mod_cast hv
  obtain ⟨L, honto, hsep⟩ := xVarshamov h m w hmh hwh hvol
  refine ⟨m, L, honto, ?_, ?_⟩
  · intro z hz hnz hwt
    have hzwt : binaryWeight z ≤ w := Nat.le_floor (by simpa only [binaryWeight, internalWeight] using hwt)
    exact (not_lt_of_ge hzwt) (hsep z hz hnz)
  · have hmLog' := (le_div_iff₀ hl0).mp hmle
    calc
      _ = Real.exp ((m : ℝ) * Real.log 2) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr hmLog'


set_option backward.isDefEq.respectTransparency false

theorem binary_of_decide_nonzero (z : ZMod 2) :
    (if decide (z ≠ 0) then (1 : ZMod 2) else 0) = z := by
  classical
  fin_cases z <;> simp
  all_goals split_ifs <;> first | rfl | contradiction | (symm; assumption)

theorem even_internal_fibre (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (hfree : (PT.tiling.P i).ℓ + (PT.tiling.P i).h < T.S.n k)
    (z : Fin (PT.tiling.P i).h → ZMod 2) :
    (Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧
      ListGateContext.internalBits i hle v = z).card =
      2 ^ (T.S.n k - ((PT.tiling.P i).ℓ + (PT.tiling.P i).h) - 1) := by
  classical
  let A := Finset.univ.filter fun a : Fin (T.S.n k) => a.val < (PT.tiling.P i).ℓ
  let I := PT.tiling.Icoord i
  let S := A ∪ I
  have hdisj : Disjoint A I := by
    apply Finset.disjoint_left.mpr
    intro a ha hi
    have ha' := (Finset.mem_filter.mp ha).2
    have hi' : T.S.n k - (PT.tiling.P i).h ≤ a.val := by
      simpa [I, Tiling.Icoord, topCoordinates] using hi
    omega
  have hA : A.card = (PT.tiling.P i).ℓ :=
    HypercubeRamsey.Lane_q_s17_pool.fin_prefix_coord_card (by omega)
  have hI : I.card = (PT.tiling.P i).h :=
    HypercubeRamsey.Lane_q_s17_pool.tiling_internal_coord_card _ _ hle
  have hS : S.card = (PT.tiling.P i).ℓ + (PT.tiling.P i).h := by
    rw [Finset.card_union_of_disjoint hdisj, hA, hI]
  let assignment (a : S) : Bool :=
    if a.1.val < (PT.tiling.P i).ℓ then PT.tiling.w i a.1
    else if hj : a.1.val - (T.S.n k - (PT.tiling.P i).h) < (PT.tiling.P i).h then
      decide (z ⟨a.1.val - (T.S.n k - (PT.tiling.P i).h), hj⟩ ≠ 0) else false
  have hagree (v : Pos T k) : (∀ a : S, v a.1 = assignment a) ↔
      v ∈ PT.tiling.leaf i ∧ ListGateContext.internalBits i hle v = z := by
    constructor
    · intro hv
      constructor
      · intro a ha
        exact (hv ⟨a, Finset.mem_union_left I (by simp [A, ha])⟩).trans (by simp [assignment, ha])
      · funext j
        let a : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P i).h + j.val, by omega⟩
        have haI : a ∈ I := by
          simp only [I, Tiling.Icoord, topCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp [a]
          omega
        have haP : ¬ a.val < (PT.tiling.P i).ℓ := by dsimp [a]; omega
        have haJ : a.val - (T.S.n k - (PT.tiling.P i).h) < (PT.tiling.P i).h := by dsimp [a]; omega
        have heq := hv ⟨a, Finset.mem_union_right A haI⟩
        have hj : (⟨a.val - (T.S.n k - (PT.tiling.P i).h), haJ⟩ : Fin (PT.tiling.P i).h) = j := by
          apply Fin.ext; dsimp [a]; omega
        simp only [assignment, if_neg haP, dif_pos haJ, hj] at heq
        change (if v a then (1 : ZMod 2) else 0) = z j
        rw [heq]
        exact binary_of_decide_nonzero _
    · rintro ⟨hv, hbits⟩ a
      by_cases haP : a.1.val < (PT.tiling.P i).ℓ
      · simpa [assignment, haP] using hv a.1 haP
      · have haI : a.1 ∈ I := (Finset.mem_union.mp a.2).resolve_left (by simp [A, haP])
        have haLow : T.S.n k - (PT.tiling.P i).h ≤ a.1.val := by
          simpa [I, Tiling.Icoord, topCoordinates] using haI
        have haJ : a.1.val - (T.S.n k - (PT.tiling.P i).h) < (PT.tiling.P i).h := by omega
        let j : Fin (PT.tiling.P i).h := ⟨a.1.val - (T.S.n k - (PT.tiling.P i).h), haJ⟩
        have haj : (⟨T.S.n k - (PT.tiling.P i).h + j.val, by omega⟩ : Fin (T.S.n k)) = a.1 := by
          apply Fin.ext; dsimp [j]; omega
        have hb := congrFun hbits j
        change (if v _ then (1 : ZMod 2) else 0) = z j at hb
        rw [haj] at hb
        simp only [assignment, if_neg haP, dif_pos haJ]
        change v a.1 = decide (z j ≠ 0)
        cases hh : v a.1 <;> simp only [hh, Bool.false_eq_true, ite_false, ite_true] at hb
        all_goals rw [← hb]; simp
  have hset : (evenRoleSet (T.S.n k)).filter (fun v => ∀ a : S, v a.1 = assignment a) =
      Finset.univ.filter (fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧
        ListGateContext.internalBits i hle v = z) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, evenRoleSet, true_and, hagree]
    tauto
  have hc := parity_projection_uniform S (by omega) assignment
  rw [hset, hS] at hc
  exact hc

theorem linear_fibre_card {h m : ℕ}
    (L : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (honto : Function.Surjective L)
    (c₁ c₂ : Fin m → ZMod 2) :
    (Finset.univ.filter fun z => L z = c₁).card = (Finset.univ.filter fun z => L z = c₂).card := by
  classical
  obtain ⟨t, ht⟩ := honto (c₂ - c₁)
  apply Finset.card_bij (fun z _ => z + t)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [map_add, hz, ht]
    abel
  · intro z hz z' hz' heq
    exact add_right_cancel heq
  · intro z hz
    refine ⟨z - t, ?_, sub_add_cancel _ _⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [map_sub, hz, ht]
    abel

theorem even_colour_fibres (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (hfree : (PT.tiling.P i).ℓ + (PT.tiling.P i).h < T.S.n k)
    (ψ : S17PaletteCode i hle) (honto : Function.Surjective ψ.map)
    (c₁ c₂ : Fin ψ.dimension → ZMod 2) :
    (Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₁).card =
    (Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₂).card := by
  classical
  have hcard (c : Fin ψ.dimension → ZMod 2) :
      (Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c).card =
      (Finset.univ.filter fun z => ψ.map z = c).card *
        2 ^ (T.S.n k - ((PT.tiling.P i).ℓ + (PT.tiling.P i).h) - 1) := by
    let A := Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c
    let Z := Finset.univ.filter fun z => ψ.map z = c
    have hsum := Finset.card_eq_sum_card_fiberwise (f := ListGateContext.internalBits i hle)
      (s := A) (t := Z) (by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.2.2⟩)
    change A.card = _
    rw [hsum]
    have heq : ∀ z ∈ Z, (A.filter fun v => ListGateContext.internalBits i hle v = z).card =
        2 ^ (T.S.n k - ((PT.tiling.P i).ℓ + (PT.tiling.P i).h) - 1) := by
      intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      have hset : (A.filter fun v => ListGateContext.internalBits i hle v = z) =
          Finset.univ.filter fun v : Pos T k => v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧
            ListGateContext.internalBits i hle v = z := by
        ext v
        constructor
        · intro hv
          obtain ⟨hvA, hzv⟩ := Finset.mem_filter.mp hv
          obtain ⟨_, hleaf, heven, hcolour⟩ := Finset.mem_filter.mp hvA
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hleaf, heven, hzv⟩
        · intro hv
          obtain ⟨_, hleaf, heven, hzv⟩ := Finset.mem_filter.mp hv
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hleaf, heven, ?_⟩, hzv⟩
          change ψ.map (ListGateContext.internalBits i hle v) = c
          rw [hzv]
          exact hz'
      rw [hset]
      exact even_internal_fibre i hle hfree z
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [hcard c₁, hcard c₂, linear_fibre_card ψ.map honto c₁ c₂]


noncomputable def empty_code (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k) :
    S17PaletteCode i hle := { dimension := 0, map := 0 }

theorem empty_code_spec (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (hh : (PT.tiling.P i).h = 0) (hg : 0 ≤ PT.tiling.gain i) :
    PaletteCodeSpec i hle (empty_code i hle) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    refine ⟨0, ?_⟩
    change (0 : Fin 0 → ZMod 2) = c
    exact Subsingleton.elim _ _
  · intro z hz hnz hwt
    apply hnz
    funext j
    have hj := j.isLt
    omega
  · intro c₁ c₂
    have : c₁ = c₂ := @Subsingleton.elim (Fin 0 → ZMod 2) inferInstance c₁ c₂
    rw [this]
  · simpa [empty_code, s17Chi, ListGateContext.PaletteCode.chi] using Real.one_le_exp_iff.mpr hg

theorem palette_code_exists (hκ : κ.Admissible) (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (hfree : (PT.tiling.P i).ℓ + (PT.tiling.P i).h < T.S.n k) :
    ∃ ψ : S17PaletteCode i hle, PaletteCodeSpec i hle ψ := by
  classical
  cases hm : PT.tiling.mode with
  | bounded =>
    refine ⟨empty_code i hle, empty_code_spec i hle ((hPT.tiling_valid.bounded_data hm).2 i).2.1 ?_⟩
    simp [Tiling.gain, hm]
  | lowDirect =>
    refine ⟨empty_code i hle, empty_code_spec i hle (hPT.tiling_valid.direct_data (Or.inl hm) i).2.2.2.2.1 ?_⟩
    simp only [Tiling.gain, hm]
    positivity
  | lowCluster =>
    have hg := (cluster_gain_controls hκ hPT hm i).2
    simp only [Tiling.gain, hm] at hg
    obtain ⟨m, L, honto, hsep, hchi⟩ := separating_kernel hκ (PT.tiling.P i).h hg
    let ψ : S17PaletteCode i hle := { dimension := m, map := L }
    refine ⟨ψ, honto, hsep, even_colour_fibres i hle hfree ψ honto, ?_⟩
    simpa [ψ, s17Chi, ListGateContext.PaletteCode.chi, Tiling.gain, hm] using hchi
  | highDirect => simp [hm, Mode.isLow] at hLow
  | highSmall => simp [hm, Mode.isLow] at hLow
  | highLarge => simp [hm, Mode.isLow] at hLow


theorem empty_retention (D : ListGateContext κ T k PT) (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (hSupport : ∀ (pools : ∀ C : D.G.Cell, D.F.Pool C) (s : Config D.F) (v : Pos T k),
      (∀ C ∈ D.scopeCells v, D.F.typical C (pools C)) →
      (∀ C ∈ D.scopeCells v, D.stateValid C (pools C) (s C)) →
      v ∈ PT.tiling.leaf i → IsEvenRole v →
      ∀ x, x ∉ (PT.tiling.P i).X → D.prior s v x = 0) :
    PaletteRetentionSpec D i hle (empty_code i hle) (fun _ => 0) := by
  classical
  have hχ : (s17Chi (empty_code i hle) : ℝ) = 1 := by
    simp [empty_code, s17Chi, ListGateContext.PaletteCode.chi]
  have hcolour (c : Fin (empty_code i hle).dimension → ZMod 2) : (0 : Fin 0 → ZMod 2) = c :=
    Subsingleton.elim _ _
  have hpal (c : Fin (empty_code i hle).dimension → ZMod 2) :
      (Finset.univ.filter fun x : Fin (T.S.N k) => x ∈ (PT.tiling.P i).X ∧
        (0 : Fin 0 → ZMod 2) = c) = (PT.tiling.P i).X := by
    ext x
    constructor
    · intro hx; exact (Finset.mem_filter.mp hx).2.1
    · intro hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hcolour c⟩
  have hrowpal (v : Pos T k) : s17Palette (empty_code i hle) (fun _ => 0) v = (PT.tiling.P i).X := by
    ext x
    constructor
    · intro hx; exact (Finset.mem_filter.mp hx).2.1
    · intro hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, ?_⟩
      exact @Subsingleton.elim (Fin 0 → ZMod 2) inferInstance _ _
  refine ⟨?_, ?_, ?_⟩
  · intro c
    dsimp only
    rw [hpal, hχ, (PT.tiling.P i).cardX]
    simp only [div_one]
    nlinarith [(show (0 : ℝ) ≤ (PT.tiling.P i).M by positivity)]
  · intro pools s v htyp hstate hleaf heven hmass
    rw [hrowpal, hχ]
    have hsum : (∑ x ∈ (PT.tiling.P i).X, D.row v (D.prior s v) (D.label s) x) =
        D.rowMass v (D.prior s v) (D.label s) := by
      unfold ListGateContext.rowMass
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hx hnot
      unfold ListGateContext.row
      rw [hSupport pools s v htyp hstate hleaf heven x hnot, zero_mul]
    rw [hsum]
    linarith
  · intro v hleaf heven σ hσ c
    dsimp only
    rw [hpal, hχ]
    have hsum : (∑ x ∈ (PT.tiling.P i).X, σ x) ≤ ∑ x, σ x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intro x hx hnot; exact hσ.1.1 x)
    rw [hσ.1.2.1] at hsum
    linarith

theorem physical_empty_retention (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    {G : LowGeom PT} {F : FreshCell G} (physical : PhysicalFreshCertificate G F)
    (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k) :
    PaletteRetentionSpec (Lane_sol_s18_dl.physical_list_context hPT hLow physical)
      i hle (empty_code i hle) (fun _ => 0) := by
  classical
  apply empty_retention
  intro pools s v htyp hstate hleaf heven x hnot
  by_contra hx
  have hown : G.cellOf v ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).scopeCells v := by
    change G.cellOf v ∈ {G.cellOf v} ∪ _
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have hs := hstate (G.cellOf v) hown
  have hen := (hs.1.2 v rfl heven).2 x hx
  have hp : G.patchOf v = i := (hPT.tiling_valid.prefix_complete v).unique (G.patchOf_leaf v) hleaf
  rw [G.cellOf_patch, hp] at hen
  exact hnot (hPT.envelope_subset i hen.1)


theorem finite_union_bound {Ω I : Type} [Fintype Ω] [Fintype I]
    (μ : FinProb Ω) (bad : I → Ω → Prop) :
    μ.pr (fun ω => ∃ i, bad i ω) ≤ ∑ i, μ.pr (bad i) := by
  classical
  have hind (ω : Ω) : (if ∃ i, bad i ω then (1 : ℝ) else 0) ≤
      ∑ i, if bad i ω then (1 : ℝ) else 0 := by
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      have hs := Finset.single_le_sum (f := fun j : I => if bad j ω then (1 : ℝ) else 0)
        (s := Finset.univ) (fun j hj => by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa [hi] using hs
    · apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> norm_num
  have hpoint (ω : Ω) : (if ∃ i, bad i ω then μ.w ω else 0) ≤
      μ.w ω * ∑ i, if bad i ω then (1 : ℝ) else 0 := by
    have hh := mul_le_mul_of_nonneg_left (hind ω) (μ.nonneg ω)
    simpa only [mul_ite, mul_one, mul_zero] using hh
  calc
    μ.pr (fun ω => ∃ i, bad i ω) ≤ ∑ ω, μ.w ω * ∑ i, if bad i ω then (1 : ℝ) else 0 := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro ω hω
      convert hpoint ω using 1
      split_ifs <;> rfl
    _ = ∑ i, μ.pr (bad i) := by
      simp only [Finset.mul_sum, FinProb.pr, mul_ite, mul_one, mul_zero]
      exact Finset.sum_comm


theorem weighted_colouring {N χ : ℕ} {I : Type} [Fintype I]
    (hχ : 0 < χ) (W : I → Fin N → ℝ) (b : ℝ) (hb : 0 < b)
    (hW : ∀ i x, 0 ≤ W i x) (hNorm : ∀ i, ∑ x, W i x = 1)
    (hAtom : ∀ i x, W i x ≤ b)
    (hCount : 2 * (Fintype.card I : ℝ) * χ * Real.exp (-1 / (2 * (χ : ℝ) ^ 2 * b)) < 1) :
    ∃ colours : Fin N → Fin χ, ∀ i c,
      1 / (2 * (χ : ℝ)) ≤ ∑ x ∈ Finset.univ.filter (fun x => colours x = c), W i x ∧
      (∑ x ∈ Finset.univ.filter (fun x => colours x = c), W i x) ≤ 3 / (2 * (χ : ℝ)) := by
  classical
  have hχR : (0 : ℝ) < χ := by exact_mod_cast hχ
  let P : FinProb (Fin χ) := FinProb.uniform Finset.univ ⟨⟨0, hχ⟩, Finset.mem_univ _⟩
  let μ := FinProb.pi fun _ : Fin N => P
  let mass (ω : Fin N → Fin χ) (i : I) (c : Fin χ) :=
    ∑ x ∈ Finset.univ.filter (fun x => ω x = c), W i x
  let bad (q : I × Fin χ) (ω : Fin N → Fin χ) :=
    1 / (2 * (χ : ℝ)) ≤ |mass ω q.1 q.2 - 1 / (χ : ℝ)|
  have htail (q : I × Fin χ) :
      μ.pr (bad q) ≤ 2 * Real.exp (-1 / (2 * (χ : ℝ) ^ 2 * b)) := by
    let X : Fin N → Fin χ → ℝ := fun x c => if c = q.2 then W q.1 x else 0
    have hmean (x : Fin N) : P.expect (X x) = W q.1 x / χ := by
      simp [P, X, FinProb.uniform, FinProb.expect, Finset.sum_ite_eq', div_eq_mul_inv, mul_comm]
    have hmeans : (∑ x, P.expect (X x)) = 1 / (χ : ℝ) := by
      simp only [hmean, ← Finset.sum_div, hNorm]
    have hsquare : 0 < ∑ x, (W q.1 x) ^ 2 := by
      obtain ⟨x, hx, hp⟩ := (Finset.sum_pos_iff_of_nonneg (fun x hx => hW q.1 x)).mp
        (show 0 < ∑ x, W q.1 x by rw [hNorm]; norm_num)
      apply Finset.sum_pos' (fun x hx => sq_nonneg _)
      exact ⟨x, hx, sq_pos_of_pos hp⟩
    have hsquarele : (∑ x, (W q.1 x) ^ 2) ≤ b := by
      calc
        _ ≤ ∑ x, b * W q.1 x := Finset.sum_le_sum (fun x hx => by nlinarith [hW q.1 x, hAtom q.1 x])
        _ = b := by rw [← Finset.mul_sum, hNorm]; ring
    have hX : ∀ x c, (0 : ℝ) ≤ X x c ∧ X x c ≤ W q.1 x := by
      intro x c
      dsimp [X]
      split_ifs <;> constructor <;> first | exact hW q.1 x | exact le_rfl
    have hchern := xChernoff (fun _ : Fin N => P) X (fun _ => 0) (W q.1) hX
      (by simpa using hsquare) (1 / (2 * (χ : ℝ))) (by positivity)
    have hmass (ω : Fin N → Fin χ) : (∑ x, X x (ω x)) = mass ω q.1 q.2 := by
      simp [X, mass, Finset.sum_filter]
    simp only [hmass, hmeans, sub_zero] at hchern
    apply hchern.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hh0 := div_le_div_of_nonneg_left (show 0 ≤ 2 * (1 / (2 * (χ : ℝ))) ^ 2 by positivity)
      hsquare hsquarele
    have hh : -2 * (1 / (2 * (χ : ℝ))) ^ 2 / (∑ x, (W q.1 x) ^ 2) ≤
        -2 * (1 / (2 * (χ : ℝ))) ^ 2 / b := by simpa only [neg_div, neg_mul] using neg_le_neg hh0
    calc
      _ ≤ -2 * (1 / (2 * (χ : ℝ))) ^ 2 / b := hh
      _ = _ := by field_simp <;> ring
  have hbad : μ.pr (fun ω => ∃ q, bad q ω) < 1 := by
    apply lt_of_le_of_lt (finite_union_bound μ bad)
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun q hq => htail q)
    have hs' : (∑ q, μ.pr (bad q)) ≤
        2 * (Fintype.card I : ℝ) * χ * Real.exp (-1 / (2 * (χ : ℝ) ^ 2 * b)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hs
    exact hs'.trans_lt hCount
  have hex : ∃ ω : Fin N → Fin χ, ∀ q, ¬ bad q ω := by
    by_contra hn
    have hall : ∀ ω : Fin N → Fin χ, ∃ q, bad q ω := by simpa using hn
    have hp : μ.pr (fun ω => ∃ q, bad q ω) = 1 := by
      simp only [FinProb.pr, if_pos (hall _)]
      exact μ.sum_eq_one
    linarith
  obtain ⟨colours, hgood⟩ := hex
  refine ⟨colours, ?_⟩
  intro i c
  have hh := abs_lt.mp (lt_of_not_ge (hgood (i, c)))
  have heq : (1 : ℝ) / χ = 2 / (2 * (χ : ℝ)) := by field_simp
  dsimp [bad, mass] at hh
  rw [heq] at hh
  simp only [div_eq_mul_inv] at hh ⊢
  constructor <;> linarith


theorem finite_family_colouring {N : ℕ} {C : Type} [Fintype C] [Nonempty C] [DecidableEq C]
    (family : Finset (Law N)) (b : ℝ) (hb : 0 < b)
    (hAtom : ∀ μ ∈ family, ∀ x, μ.w x ≤ b)
    (hCount : 2 * (family.card : ℝ) * Fintype.card C *
      Real.exp (-1 / (2 * (Fintype.card C : ℝ) ^ 2 * b)) < 1) :
    ∃ colours : Fin N → C, ∀ μ ∈ family, ∀ c,
      1 / (2 * (Fintype.card C : ℝ)) ≤ ∑ x ∈ Finset.univ.filter (fun x => colours x = c), μ.w x ∧
      (∑ x ∈ Finset.univ.filter (fun x => colours x = c), μ.w x) ≤ 3 / (2 * (Fintype.card C : ℝ)) := by
  classical
  let I := {μ : Law N // μ ∈ family}
  obtain ⟨ω, hω⟩ := weighted_colouring (N := N) (χ := Fintype.card C) (I := I) (show 0 < Fintype.card C from Fintype.card_pos) (fun μ => μ.1.w) b hb
    (fun μ x => μ.1.nonneg x) (fun μ => μ.1.sum_eq_one)
    (fun μ x => hAtom μ.1 μ.2 x) (by simpa only [I, Fintype.card_coe] using hCount)
  let e := Fintype.equivFin C
  refine ⟨fun x => e.symm (ω x), ?_⟩
  intro μ hμ c
  have hc := hω ⟨μ, hμ⟩ (e c)
  have heq : (Finset.univ.filter fun x => e.symm (ω x) = c) =
      Finset.univ.filter fun x => ω x = e c := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hh
      have h := congrArg e hh
      simpa only [Equiv.apply_symm_apply] using h
    · intro hh
      rw [hh, Equiv.symm_apply_apply]
  rw [heq]
  exact hc

theorem supported_palette_sum {N : ℕ} {C : Type} [DecidableEq C]
    (X : Finset (Fin N)) (colours : Fin N → C) (c : C) (μ : Law N)
    (hsupp : μ.SupportedIn X) :
    (∑ x ∈ Finset.univ.filter (fun x => x ∈ X ∧ colours x = c), μ.w x) =
      ∑ x ∈ Finset.univ.filter (fun x => colours x = c), μ.w x := by
  classical
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hX : x ∈ X
  · simp [hX]
  · simp [hX, hsupp x hX]

theorem palette_retention_of_family (D : ListGateContext κ T k PT) (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).h ≤ T.S.n k) (ψ : S17PaletteCode i hle)
    (family : Finset (Law (T.S.N k))) (b : ℝ) (hb : 0 < b)
    (hAtom : ∀ μ ∈ family, ∀ x, μ.w x ≤ b)
    (hCount : 2 * (family.card : ℝ) * s17Chi ψ * Real.exp (-1 / (2 * (s17Chi ψ : ℝ) ^ 2 * b)) < 1)
    (hSupported : ∀ μ ∈ family, μ.SupportedIn (PT.tiling.P i).X)
    (hUniform : FinProb.uniform (PT.tiling.P i).X (D.patchXNonempty i) ∈ family)
    (hRows : ∀ (pools : ∀ C : D.G.Cell, D.F.Pool C) (s : Config D.F) (v : Pos T k),
      (∀ C ∈ D.scopeCells v, D.F.typical C (pools C)) →
      (∀ C ∈ D.scopeCells v, D.stateValid C (pools C) (s C)) →
      v ∈ PT.tiling.leaf i → IsEvenRole v →
      (1 / 2 : ℝ) ≤ D.rowMass v (D.prior s v) (D.label s) →
      ∃ μ ∈ family, ∀ x, μ.w x = D.row v (D.prior s v) (D.label s) x /
        D.rowMass v (D.prior s v) (D.label s))
    (hPriors : ∀ v, v ∈ PT.tiling.leaf i → IsEvenRole v → ∀ σ,
      D.ValidInitialPrior v σ → ∃ μ ∈ family, μ.w = σ) :
    ∃ colours : S17PaletteAssignment ψ, PaletteRetentionSpec D i hle ψ colours ∧
      ∀ c, (Finset.univ.filter fun x : Fin (T.S.N k) => x ∈ (PT.tiling.P i).X ∧ colours x = c).Nonempty := by
  classical
  have hcard : Fintype.card (Fin ψ.dimension → ZMod 2) = s17Chi ψ := by
    simp [s17Chi, ListGateContext.PaletteCode.chi, ZMod.card]
  have hχ : (0 : ℝ) < s17Chi ψ := by simp [s17Chi, ListGateContext.PaletteCode.chi]
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (D.patchXNonempty i)
  obtain ⟨colours, hcol⟩ := finite_family_colouring (C := Fin ψ.dimension → ZMod 2) family b hb hAtom
    (by simpa only [hcard] using hCount)
  let palette (c : Fin ψ.dimension → ZMod 2) :=
    Finset.univ.filter fun x : Fin (T.S.N k) => x ∈ (PT.tiling.P i).X ∧ colours x = c
  have hbounds : ∀ μ ∈ family, ∀ c,
      1 / (2 * (s17Chi ψ : ℝ)) ≤ ∑ x ∈ palette c, μ.w x ∧
      (∑ x ∈ palette c, μ.w x) ≤ 3 / (2 * (s17Chi ψ : ℝ)) := by
    intro μ hμ c
    rw [supported_palette_sum _ _ _ μ (hSupported μ hμ)]
    simpa only [hcard] using hcol μ hμ c
  have hunif (c : Fin ψ.dimension → ZMod 2) :
      (∑ x ∈ palette c, (FinProb.uniform (PT.tiling.P i).X (D.patchXNonempty i)).w x) =
      (palette c).card / ((PT.tiling.P i).M : ℝ) := by
    have heq : (∑ x ∈ palette c, (FinProb.uniform (PT.tiling.P i).X (D.patchXNonempty i)).w x) =
        ∑ x ∈ palette c, (1 : ℝ) / (PT.tiling.P i).M := by
      apply Finset.sum_congr rfl
      intro x hx
      have hX := (Finset.mem_filter.mp hx).2.1
      simp [FinProb.uniform, hX, (PT.tiling.P i).cardX, one_div]
    rw [heq]
    simp [div_eq_mul_inv]
  have hsize : ∀ c, ((palette c).card : ℝ) ≤ 2 * (PT.tiling.P i).M / (s17Chi ψ : ℝ) := by
    intro c
    have hh := (hbounds _ hUniform c).2
    rw [hunif] at hh
    have hden : 0 < 2 * (s17Chi ψ : ℝ) := by positivity
    have hh' := (div_le_div_iff₀ hM hden).mp hh
    apply (le_div_iff₀ hχ).mpr
    nlinarith
  have hnonempty : ∀ c, (palette c).Nonempty := by
    intro c
    have hh := (hbounds _ hUniform c).1
    rw [hunif] at hh
    have hp : 0 < ((palette c).card : ℝ) := by
      have hl : 0 < 1 / (2 * (s17Chi ψ : ℝ)) := by positivity
      have hd := (lt_div_iff₀ hM).mp (hl.trans_le hh)
      simpa using hd
    exact Finset.card_pos.mp (by exact_mod_cast hp)
  refine ⟨colours, ⟨hsize, ?_, ?_⟩, hnonempty⟩
  · intro pools s v htyp hstate hleaf heven hmass
    obtain ⟨μ, hμ, hrow⟩ := hRows pools s v htyp hstate hleaf heven hmass
    have hh := (hbounds μ hμ (ψ.roleColour v)).1
    have hm : 0 < D.rowMass v (D.prior s v) (D.label s) := by linarith
    simp_rw [hrow] at hh
    rw [← Finset.sum_div] at hh
    have hh' := (le_div_iff₀ hm).mp hh
    have ht : 1 / (4 * (s17Chi ψ : ℝ)) ≤ 1 / (2 * (s17Chi ψ : ℝ)) * D.rowMass v (D.prior s v) (D.label s) := by
      calc
        _ = 1 / (2 * (s17Chi ψ : ℝ)) * (1 / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
    exact ht.trans hh'
  · intro v hleaf heven σ hσ c
    obtain ⟨μ, hμ, hσeq⟩ := hPriors v hleaf heven σ hσ
    have hh := (hbounds μ hμ c).2
    rw [hσeq] at hh
    apply hh.trans
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (s17Chi ψ : ℝ)) hχ).mpr
    linarith


theorem eventual_palette_codes (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in Filter.atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
      (G : LowGeom PT) (F : FreshCell G) (hL16 : L16QuantitativeValidity G F)
      (hLow : PT.tiling.mode.isLow),
      ∃ hle : ∀ i, (PT.tiling.P i).h ≤ T.S.n k,
        ∀ i, ∃ ψ : S17PaletteCode i (hle i), PaletteCodeSpec i (hle i) ψ := by
  filter_upwards [small_prefix_height T] with k hsmall
  intro PT hPT G F hL16 hLow
  let Q := (Classical.choice hL16.physical).quantitative
  have hn : (2 : ℝ) ≤ T.S.n k := by exact_mod_cast Q.n_large
  have hsqrt : Real.sqrt (T.S.n k : ℝ) ≤ T.S.n k := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ T.S.n k by positivity), Real.sqrt_nonneg (T.S.n k : ℝ)]
  have hfree : ∀ i, (PT.tiling.P i).ℓ + (PT.tiling.P i).h < T.S.n k := by
    intro i
    have hh := (hsmall (PT.tiling.P i).ℓ (PT.tiling.P i).h (Q.prefix_bound i) (Q.height_bound i)).1
    have hh' : ((PT.tiling.P i).ℓ : ℝ) + (PT.tiling.P i).h < T.S.n k := by linarith
    exact_mod_cast hh'
  let hle : ∀ i, (PT.tiling.P i).h ≤ T.S.n k := fun i => by have := hfree i; omega
  exact ⟨hle, fun i => palette_code_exists hκ hPT hLow i (hle i) (hfree i)⟩


theorem conditional_support_source {Ω : Type} [Fintype Ω] (P : FinLaw Ω)
    (A : Finset Ω) (hp : 0 < ∑ x ∈ A, P.w x) (x : Ω)
    (hx : (FinLaw.cond P A hp).w x ≠ 0) : P.w x ≠ 0 := by
  classical
  intro hz
  apply hx
  simp [FinLaw.cond, hz]

theorem charged_fresh_decode {G : LowGeom PT} {F : FreshCell G}
    (physical : PhysicalFreshCertificate G F) (C : G.Cell) (pool : F.Pool C)
    (s : F.State C) (ht : F.typical C pool) (hs : (F.fresh C pool).w s ≠ 0) :
    ∃ W : physical.calibration.Hist C,
      ∃ a : physical.calibration.Group C → Bin PT.tiling (G.cellPatch C),
      ∃ ys : S16.OddCellRole G C → Fin (T.S.N k),
        physical.calibration.encode C (W, a, ys) = s ∧
        (physical.calibration.gatedHistory C pool).w W ≠ 0 ∧
        (physical.calibration.binSampler C pool W).w a ≠ 0 ∧
        (physical.calibration.labelSampler C pool W a).w ys ≠ 0 := by
  classical
  rw [physical.calibration.fresh_eq C pool ht] at hs
  obtain ⟨⟨W, a, ys⟩, hencode, hcharge⟩ := S16.Lane_q_s16_calib.finLaw_map_support _ _ s hs
  change (physical.calibration.gatedHistory C pool).w W *
    ((physical.calibration.binSampler C pool W).w a *
      (physical.calibration.labelSampler C pool W a).w ys) ≠ 0 at hcharge
  obtain ⟨hW, hrest⟩ := mul_ne_zero_iff.mp hcharge
  obtain ⟨ha, hys⟩ := mul_ne_zero_iff.mp hrest
  exact ⟨W, a, ys, hencode, hW, ha, hys⟩

theorem physical_cluster_prior_origin {G : LowGeom PT} {F : FreshCell G}
    (physical : PhysicalFreshCertificate G F) (hm : PT.tiling.mode = .lowCluster)
    (C : G.Cell) (pool : F.Pool C) (s : F.State C) (v : Pos T k)
    (hcell : G.cellOf v = C) (heven : IsEvenRole v)
    (ht : F.typical C pool) (hs : (F.fresh C pool).w s ≠ 0) :
    ∃ S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh,
      PT.solver (G.cellPatch C) = some S ∧
      ∃ w : EvenRole PT.tiling (G.cellPatch C), ∃ W : ∀ r, S.Val r,
      ∃ ys : InternalLabels PT.tiling (G.cellPatch C),
        0 < (S.recLaw PT.parameter).w W ∧ F.prior C s v = S.σ w W ys := by
  classical
  obtain ⟨Wc, a, ys, hencode, hWc, ha, hys⟩ := charged_fresh_decode physical C pool s ht hs
  have hhist : (physical.calibration.history C).w Wc ≠ 0 := by
    apply conditional_support_source _ (physical.calibration.gate C pool)
      (physical.calibration.gate_pos C pool ht) Wc
    rw [← physical.calibration.gated_eq C pool ht]
    exact hWc
  rw [physical.construction.history_eq C] at hhist
  obtain ⟨Wr, hWrCode, hWr⟩ := S16.Lane_q_s16_calib.finLaw_map_support _ _ Wc hhist
  have hrecords : Wr = physical.construction.histories C Wc := by
    have hh := congrArg (physical.construction.histories C) hWrCode
    simpa only [Equiv.apply_symm_apply] using hh
  have hprior := physical.construction.prior_eq C pool Wc a ys v ht hWc ha hys hcell heven
  rw [hencode, ← hrecords] at hprior
  rcases physical.source_valid with hsource | hsource
  · obtain ⟨S, hS, records, groups, hLaws, hPass, hGroups, hQ, hTrim, hU, hPrior⟩ := hsource.2.2 C
    let p := (physical.raw.cellWords C).symm ⟨v, hcell⟩
    have hloc : (physical.raw.cellWords C p).1 = v := by
      exact congrArg Subtype.val ((physical.raw.cellWords C).apply_symm_apply ⟨v, hcell⟩)
    have hw : IsEvenRole p.2 :=
      (physical.raw.word_parity (by simp [hm, Mode.isCluster]) C p.1 p.2).mp (by simpa [hloc] using heven)
    change (∏ l, (FinLaw.cond (physical.raw.sliceLaw C l) (physical.raw.slicePass C l)
      (physical.raw.slice_pos C l)).w (Wr l)) ≠ 0 at hWr
    have hslice := Finset.prod_ne_zero_iff.mp hWr p.1 (Finset.mem_univ _)
    have hbase := conditional_support_source (physical.raw.sliceLaw C p.1)
      (physical.raw.slicePass C p.1) (physical.raw.slice_pos C p.1) (Wr p.1) hslice
    rw [hLaws p.1] at hbase
    obtain ⟨W, hWCode, hW⟩ := S16.Lane_q_s16_calib.finLaw_map_support _ _ (Wr p.1) hbase
    have hrecord : records p.1 (Wr p.1) = W := by
      have hh := congrArg (records p.1) hWCode
      simpa only [Equiv.apply_symm_apply] using hh.symm
    let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
    have hraw := hPrior Wr p.1 ⟨p.2, hw⟩ ys fallback
    change physical.raw.rawPrior C Wr ys (physical.raw.cellWords C p).1 = _ at hraw
    rw [hloc, hrecord] at hraw
    exact ⟨S, hS, ⟨p.2, hw⟩, W, _, lt_of_le_of_ne ((S.recLaw PT.parameter).nonneg W) hW.symm,
      hprior.trans hraw⟩
  · exact (hsource.1 (by simp [hm, Mode.isCluster])).elim


noncomputable def external_coordinates (G : LowGeom PT) (v : Pos T k) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun a => a ∉ PT.tiling.Icoord (G.patchOf v) ∧ G.classOf (flipPos v a) = none

noncomputable def late_coordinates (G : LowGeom PT) (v : Pos T k) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun a => (G.classOf (flipPos v a)).isSome

theorem geometric_count (G : LowGeom PT) (v : Pos T k)
    (hle : (PT.tiling.P (G.patchOf v)).h ≤ T.S.n k)
    (hCosets : ∀ a a', a ∈ PT.tiling.Icoord (G.patchOf v) →
      a' ∈ PT.tiling.Icoord (G.patchOf v) → G.ids a - G.ids a' ∈ G.Lsub → a = a') :
    (PT.tiling.P (G.patchOf v)).h + (external_coordinates G v).card +
      (late_coordinates G v).card ≤ T.S.n k + 1 := by
  classical
  let I := PT.tiling.Icoord (G.patchOf v)
  let L := late_coordinates G v
  have hA : external_coordinates G v = Finset.univ \ (I ∪ L) := by
    ext a
    simp only [external_coordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_union, L, late_coordinates, not_or]
    cases hc : G.classOf (flipPos v a) <;> simp [hc, I]
  have hI : I.card = (PT.tiling.P (G.patchOf v)).h :=
    HypercubeRamsey.Lane_q_s17_pool.tiling_internal_coord_card _ _ hle
  have hIL : (I ∩ L).card ≤ 1 := by
    have heq : I ∩ L = I.filter fun a => (G.classOf (flipPos v a)).isSome := by
      ext a
      simp [L, late_coordinates]
    rw [heq]
    exact internal_late_le_one G v hCosets
  have hu := Finset.card_union_add_card_inter I L
  have hc := Finset.card_sdiff_of_subset (Finset.subset_univ (I ∪ L))
  rw [← hA] at hc
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hub : (I ∪ L).card ≤ T.S.n k := (Finset.card_le_univ _).trans_eq (by simp)
  change (PT.tiling.P (G.patchOf v)).h + (external_coordinates G v).card + L.card ≤ T.S.n k + 1
  omega

theorem geometric_crossing_count (hPT : PT.Valid) (G : LowGeom PT) (v : Pos T k)
    (hell : (PT.tiling.P (G.patchOf v)).ℓ ≤ T.S.n k) :
    ((external_coordinates G v).filter fun a => G.patchOf (flipPos v a) ≠ G.patchOf v).card ≤
      (PT.tiling.P (G.patchOf v)).ℓ := by
  classical
  have hsub : (external_coordinates G v).filter (fun a => G.patchOf (flipPos v a) ≠ G.patchOf v) ⊆
      Finset.univ.filter fun a : Fin (T.S.n k) => a.val < (PT.tiling.P (G.patchOf v)).ℓ := by
    intro a ha
    have hne := (Finset.mem_filter.mp ha).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hn
    exact hne (HypercubeRamsey.Lane_q_s17_pool.lowGeom_patch_flip_of_after_prefix G hPT v a (Nat.le_of_not_gt hn))
  exact (Finset.card_le_card hsub).trans_eq (HypercubeRamsey.Lane_q_s17_pool.fin_prefix_coord_card hell)

theorem weighted_product_bound {A : Type} [Fintype A] [DecidableEq A]
    (S : Finset A) (hits : A → Prop) (d e : A → ℝ) (w B : ℝ)
    (hw : 0 ≤ w) (hB : w ≤ B)
    (hd : ∀ a ∈ S, 0 < d a ∧ 1 / d a ≤ 2 * Real.exp (e a)) :
    w * (∏ a ∈ S, (if hits a then (1 : ℝ) else 0) / d a) ≤
      B * (2 : ℝ) ^ S.card * Real.exp (∑ a ∈ S, e a) := by
  classical
  have hp : (∏ a ∈ S, (if hits a then (1 : ℝ) else 0) / d a) ≤
      (2 : ℝ) ^ S.card * Real.exp (∑ a ∈ S, e a) := by
    calc
      _ ≤ ∏ a ∈ S, 2 * Real.exp (e a) := by
        apply Finset.prod_le_prod₀
        · intro a ha
          exact div_nonneg (by split_ifs <;> norm_num) (hd a ha).1.le
        · intro a ha
          split_ifs
          · exact (hd a ha).2
          · simp [Real.exp_nonneg]
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
  calc
    _ ≤ w * ((2 : ℝ) ^ S.card * Real.exp (∑ a ∈ S, e a)) := mul_le_mul_of_nonneg_left hp hw
    _ ≤ B * ((2 : ℝ) ^ S.card * Real.exp (∑ a ∈ S, e a)) := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = _ := by ring


theorem cluster_coordinate_row_bound (hPT : PT.Valid) (G : LowGeom PT)
    (hm : PT.tiling.mode = .lowCluster) (v : Pos T k)
    (hle : (PT.tiling.P (G.patchOf v)).h ≤ T.S.n k)
    (hell : (PT.tiling.P (G.patchOf v)).ℓ ≤ T.S.n k)
    (hCosets : ∀ a a', a ∈ PT.tiling.Icoord (G.patchOf v) →
      a' ∈ PT.tiling.Icoord (G.patchOf v) → G.ids a - G.ids a' ∈ G.Lsub → a = a')
    (hn : 0 < (T.S.n k : ℝ)) (hb : 3 * bstar T k ≤ 1 / 4)
    (hcross : 12 * bstar T k * (PT.tiling.P (G.patchOf v)).ℓ ≤ 1)
    (hOwn : 40 * Real.rpow ((PT.tiling.P (G.patchOf v)).q : ℝ) κ.Cb ≤ PT.tiling.gain (G.patchOf v))
    (hg1 : 1 ≤ PT.tiling.gain (G.patchOf v)) (hgn : PT.tiling.gain (G.patchOf v) ≤ T.S.n k)
    (σ : Fin (T.S.N k) → ℝ) (ys : Fin (T.S.n k) → Fin (T.S.N k))
    (hσ : ∀ x, 0 ≤ σ x)
    (hSupport : ∀ x, σ x ≠ 0 → x ∈ PT.envelope (G.patchOf v))
    (hCap : ∀ x, (T.S.N k : ℝ) * σ x ≤ (2 : ℝ) ^ (PT.tiling.P (G.patchOf v)).h *
      Real.exp (-500 * PT.tiling.gain (G.patchOf v))) :
    ∀ x, σ x * (∏ a ∈ external_coordinates G v,
      (if Hits (T.S.E k) PT.tiling.c x (ys a) then (1 : ℝ) else 0) /
        deg (T.S.E k) PT.tiling.c (PT.π (G.patchOf (flipPos v a))).w x) ≤
      2 / densityScale T k * Real.exp (-498 * PT.tiling.gain (G.patchOf v)) *
        Real.rpow 2 (-((late_coordinates G v).card : ℝ)) := by
  classical
  let g := PT.tiling.gain (G.patchOf v)
  let Q := Real.rpow ((PT.tiling.P (G.patchOf v)).q : ℝ) κ.Cb
  let A := external_coordinates G v
  let p := (late_coordinates G v).card
  have hQ : 0 ≤ Q := Real.rpow_nonneg (by positivity) _
  change 40 * Q ≤ g at hOwn
  change g ≤ (T.S.n k : ℝ) at hgn
  have hsmall : 10 * Q / T.S.n k ≤ 1 / 4 := (div_le_iff₀ hn).mpr (by linarith)
  have hcount := geometric_count G v hle hCosets
  have hscale := row_scale_factor (T.S.n k) (PT.tiling.P (G.patchOf v)).h A.card p hcount
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hC : 0 < densityScale T k := by unfold densityScale; positivity
  let e := fun a : Fin (T.S.n k) => if G.patchOf (flipPos v a) = G.patchOf v
    then 40 * Q / T.S.n k else 12 * bstar T k
  intro x
  by_cases hx : σ x = 0
  · simp only [hx, zero_mul]
    exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hC.le) (Real.exp_nonneg _))
      (Real.rpow_nonneg (by norm_num) _)
  have hxenv := hSupport x hx
  have hprior : σ x ≤ (2 : ℝ) ^ (PT.tiling.P (G.patchOf v)).h / T.S.N k * Real.exp (-500 * g) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hN).mpr
    simpa only [g, mul_comm] using hCap x
  have hdegree : ∀ a ∈ A, 0 < deg (T.S.E k) PT.tiling.c (PT.π (G.patchOf (flipPos v a))).w x ∧
      1 / deg (T.S.E k) PT.tiling.c (PT.π (G.patchOf (flipPos v a))).w x ≤ 2 * Real.exp (e a) := by
    intro a ha
    dsimp [e]
    split_ifs with hp
    · rw [hp]
      have hdeg := hPT.envelope_degree _ x hxenv
      simp only [OwnDegOK, hm] at hdeg
      change |deg (T.S.E k) PT.tiling.c (PT.π (G.patchOf v)).w x - 1 / 2| ≤ 10 * Q / T.S.n k at hdeg
      have hl : 1 / 2 - 10 * Q / T.S.n k ≤ deg (T.S.E k) PT.tiling.c (PT.π (G.patchOf v)).w x := by
        linarith [(abs_le.mp hdeg).1]
      convert inverse_degree_lower _ (10 * Q / T.S.n k) hl (by positivity) hsmall using 1 <;> congr 2 <;> ring
    · have hdeg := hPT.envelope_other_degree _ _ hp x hxenv
      have hl : 1 / 2 - 3 * bstar T k ≤ deg (T.S.E k) PT.tiling.c (PT.π (G.patchOf (flipPos v a))).w x := by
        linarith [(abs_le.mp hdeg).1]
      convert inverse_degree_lower _ (3 * bstar T k) hl (by unfold bstar; positivity) hb using 1 <;> congr 2 <;> ring
  have he : (∑ a ∈ A, e a) ≤ 2 * g := by
    have hc1 : ((A.filter fun a => G.patchOf (flipPos v a) = G.patchOf v).card : ℝ) ≤ T.S.n k := by
      exact_mod_cast ((Finset.card_le_univ _).trans_eq (by simp) :
        (A.filter fun a => G.patchOf (flipPos v a) = G.patchOf v).card ≤ T.S.n k)
    have hc2 : ((A.filter fun a => G.patchOf (flipPos v a) ≠ G.patchOf v).card : ℝ) ≤ (PT.tiling.P (G.patchOf v)).ℓ := by
      exact_mod_cast geometric_crossing_count hPT G v hell
    have h1 : 40 * Q / T.S.n k * ((A.filter fun a => G.patchOf (flipPos v a) = G.patchOf v).card : ℝ) ≤ g := by
      calc
        _ ≤ 40 * Q / T.S.n k * T.S.n k := by gcongr
        _ = 40 * Q := div_mul_cancel₀ _ hn.ne'
        _ ≤ g := hOwn
    have h2 : 12 * bstar T k * ((A.filter fun a => G.patchOf (flipPos v a) ≠ G.patchOf v).card : ℝ) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hc2 (by unfold bstar; positivity)).trans hcross
    dsimp [e]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change 1 ≤ g at hg1
    nlinarith
  have hrow := weighted_product_bound A (fun a => Hits (T.S.E k) PT.tiling.c x (ys a))
    (fun a => deg (T.S.E k) PT.tiling.c (PT.π (G.patchOf (flipPos v a))).w x) e (σ x)
    ((2 : ℝ) ^ (PT.tiling.P (G.patchOf v)).h / T.S.N k * Real.exp (-500 * g))
    (hσ x) hprior hdegree
  calc
    _ ≤ (2 : ℝ) ^ (PT.tiling.P (G.patchOf v)).h / T.S.N k * Real.exp (-500 * g) *
        (2 : ℝ) ^ A.card * Real.exp (∑ a ∈ A, e a) := hrow
    _ = Real.exp (-500 * g) / T.S.N k * ((2 : ℝ) ^ (PT.tiling.P (G.patchOf v)).h * (2 : ℝ) ^ A.card) *
        Real.exp (∑ a ∈ A, e a) := by ring
    _ ≤ Real.exp (-500 * g) / T.S.N k * (2 * (2 : ℝ) ^ T.S.n k * Real.rpow 2 (-(p : ℝ))) *
        Real.exp (2 * g) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hscale (by positivity)
      · exact Real.exp_le_exp.mpr he
      · exact Real.exp_nonneg _
      · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _))
    _ = _ := by
      rw [show -498 * PT.tiling.gain (G.patchOf v) = -500 * g + 2 * g by dsimp [g]; ring, Real.exp_add]
      unfold densityScale
      field_simp
      ring


noncomputable def posterior_law {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (v : EvenRole PT.tiling i)
    (W : ∀ r, S.Val r) (ys : InternalLabels PT.tiling i) (fallback : Law (T.S.N k)) : Law (T.S.N k) :=
  if hσ : S.σ v W ys ≠ 0 then
    { w := S.σ v W ys, nonneg := S.σ_nonneg v W ys, sum_eq_one := S.σ_prob v W ys hσ }
  else fallback

theorem solver_prior_supported (hPT : PT.Valid) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (v : EvenRole PT.tiling i)
    (W : ∀ r, S.Val r) (ys : InternalLabels PT.tiling i)
    (hW : 0 < (S.recLaw PT.parameter).w W) :
    ∀ x, x ∉ (PT.tiling.P i).X → S.σ v W ys x = 0 := by
  classical
  intro x hx
  by_cases hσ : S.σ v W ys = 0
  · rw [hσ]; rfl
  obtain ⟨q, hq, hsupp⟩ := S.σ_support v W ys hσ
  by_contra hxσ
  have hact : q ∈ PT.activeVertices := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq PT.parameter hW⟩
  exact hx ((hPT.corner_clean i q hact).sub (hsupp x hxσ).1)

theorem posterior_law_supported (hPT : PT.Valid) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (v : EvenRole PT.tiling i)
    (W : ∀ r, S.Val r) (ys : InternalLabels PT.tiling i)
    (hW : 0 < (S.recLaw PT.parameter).w W) :
    (posterior_law S v W ys (FinProb.uniform (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1)).SupportedIn
      (PT.tiling.P i).X := by
  classical
  intro x hx
  unfold posterior_law
  split_ifs with hσ
  · exact solver_prior_supported hPT S v W ys hW x hx
  · simp [FinProb.uniform, hx]

noncomputable def coordinate_row (G : LowGeom PT) (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (ys : Fin (T.S.n k) → Fin (T.S.N k)) (x : Fin (T.S.N k)) : ℝ :=
  σ x * ∏ a ∈ external_coordinates G v,
    (if Hits (T.S.E k) PT.tiling.c x (ys a) then (1 : ℝ) else 0) /
      deg (T.S.E k) PT.tiling.c (PT.π (G.patchOf (flipPos v a))).w x

theorem coordinate_row_nonneg (G : LowGeom PT) (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (ys : Fin (T.S.n k) → Fin (T.S.N k))
    (hσ : ∀ x, 0 ≤ σ x) : ∀ x, 0 ≤ coordinate_row G v σ ys x := by
  classical
  intro x
  apply mul_nonneg (hσ x)
  apply Finset.prod_nonneg
  intro a ha
  apply div_nonneg
  · split_ifs <;> norm_num
  · rw [← row_degree_eq]
    unfold rowDeg
    apply Finset.sum_nonneg
    intro y hy
    split_ifs <;> simp [(PT.π _).nonneg y]

noncomputable def normalize_large_row {N : ℕ} (fallback : Law N) (w : Fin N → ℝ)
    (hw : ∀ x, 0 ≤ w x) : Law N :=
  if hm : (1 / 2 : ℝ) ≤ ∑ x, w x then
    { w := fun x => w x / ∑ x, w x
      nonneg := fun x => div_nonneg (hw x) (by linarith)
      sum_eq_one := by
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt (by linarith : 0 < ∑ x, w x)) }
  else fallback

theorem normalize_large_row_atom {N : ℕ} (fallback : Law N) (w : Fin N → ℝ)
    (hw : ∀ x, 0 ≤ w x) (A : ℝ) (hA : 0 ≤ A) (hAtom : ∀ x, w x ≤ A)
    (hFallback : ∀ x, fallback.w x ≤ 2 * A) :
    ∀ x, (normalize_large_row fallback w hw).w x ≤ 2 * A := by
  classical
  intro x
  unfold normalize_large_row
  split_ifs with hm
  · change w x / (∑ x, w x) ≤ 2 * A
    calc
      _ ≤ w x / (1 / 2 : ℝ) := div_le_div_of_nonneg_left (hw x) (by norm_num) hm
      _ = 2 * w x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hAtom x) (by norm_num)
  · exact hFallback x


theorem flip_coordinate_injective (v : Pos T k) : Function.Injective (flipPos v) := by
  classical
  intro a b hab
  by_contra hne
  have ha := congrFun hab a
  simp only [flipPos, Function.update_self, Function.update_of_ne hne] at ha
  cases hv : v a <;> simp_all

theorem external_positions_eq_image (D : ListGateContext κ T k PT) (v : Pos T k) :
    D.externalEarly v = (external_coordinates D.G v).image (flipPos v) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨_, hc, a, ha, heq⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, ?_⟩, heq.symm⟩
    simpa only [← heq] using hc
  · intro hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨_, haI, haC⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haC, a, haI, rfl⟩

theorem row_eq_coordinate_row (D : ListGateContext κ T k PT) (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (ys : Pos T k → Fin (T.S.N k)) :
    D.row v σ ys = coordinate_row D.G v σ (fun a => ys (flipPos v a)) := by
  classical
  funext x
  unfold ListGateContext.row coordinate_row
  rw [external_positions_eq_image, Finset.prod_image]
  · rfl
  · intro a ha b hb hab
    exact flip_coordinate_injective v hab

theorem polynomial_host_cutoff (T : Stage) (r : ℝ) (hr : 0 ≤ r) :
    ∀ᶠ k in Filter.atTop,
      100 ≤ T.S.n k ∧ 1 ≤ Real.log (T.S.n k : ℝ) ∧
      1 ≤ densityScale T k ∧ Real.rpow (T.S.n k : ℝ) r ≤ T.S.N k ∧
      Real.log (T.S.N k : ℝ) ≤ 2 * T.S.n k := by
  have hn : Filter.Tendsto (fun k => (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he := hn.eventually (Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < Real.log 2 / (r + 1) by positivity))
  filter_upwards [T.S.eventually_large 1 100, (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 1, he]
    with k hlarge hlog he
  change 1 ≤ Real.log (T.S.n k : ℝ) at hlog
  have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hNpos : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hL : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hnpos.le, abs_of_nonneg hL] at he
  have he' : Real.log (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) * Real.log 2 / (r + 1) := by
    convert he using 1 <;> ring
  have hexp : Real.log (T.S.n k : ℝ) * r ≤ (T.S.n k : ℝ) * Real.log 2 := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < r + 1 by positivity)).mp he'
    nlinarith
  have hNlower : (2 : ℝ) ^ T.S.n k ≤ T.S.N k := by simpa using hlarge.2.1
  have hNupper : (T.S.N k : ℝ) ≤ T.S.n k * (2 : ℝ) ^ T.S.n k := by exact_mod_cast hlarge.2.2
  refine ⟨hlarge.1, hlog, ?_, ?_, ?_⟩
  · unfold densityScale
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ T.S.n k)).mpr (by simpa using hNlower)
  · calc
      _ = Real.exp (Real.log (T.S.n k : ℝ) * r) := Real.rpow_def_of_pos hnpos r
      _ ≤ Real.exp ((T.S.n k : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = (2 : ℝ) ^ T.S.n k := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ _ := hNlower
  · have hh := Real.log_le_log hNpos hNupper
    rw [Real.log_mul hnpos.ne' (by positivity : (2 : ℝ) ^ T.S.n k ≠ 0), Real.log_pow] at hh
    have hl := Real.log_le_sub_one_of_pos hnpos
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith


abbrev PriorCandidate {i : Fin PT.tiling.m} (S : SliceSolver κ PT.tiling i PT.mesh) :=
  EvenRole PT.tiling i × {W : ∀ r, S.Val r // 0 < (S.recLaw PT.parameter).w W} × InternalLabels PT.tiling i

abbrev RowCandidate (G : LowGeom PT) {i : Fin PT.tiling.m} (S : SliceSolver κ PT.tiling i PT.mesh) :=
  {v : Pos T k // IsEvenRole v ∧ G.patchOf v = i} × PriorCandidate S × (Fin (T.S.n k) → Fin (T.S.N k))

noncomputable def candidate_prior_law (hPT : PT.Valid) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (q : PriorCandidate S) : Law (T.S.N k) :=
  posterior_law S q.1 q.2.1.1 q.2.2 (FinProb.uniform (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1)

noncomputable def candidate_row_law (hPT : PT.Valid) (G : LowGeom PT) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (q : RowCandidate G S) : Law (T.S.N k) :=
  normalize_large_row (FinProb.uniform (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1)
    (coordinate_row G q.1.1 (S.σ q.2.1.1 q.2.1.2.1.1 q.2.1.2.2) q.2.2)
    (coordinate_row_nonneg G q.1.1 _ q.2.2 (S.σ_nonneg _ _ _))

noncomputable def cluster_family (hPT : PT.Valid) (G : LowGeom PT) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) : Finset (Law (T.S.N k)) :=
  {FinProb.uniform (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1} ∪
    (Finset.univ.image (candidate_prior_law hPT S)) ∪ (Finset.univ.image (candidate_row_law hPT G S))

theorem cluster_family_uniform (hPT : PT.Valid) (G : LowGeom PT) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) :
    FinProb.uniform (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1 ∈ cluster_family hPT G S := by
  classical
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem cluster_family_supported (hPT : PT.Valid) (G : LowGeom PT) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) :
    ∀ μ ∈ cluster_family hPT G S, μ.SupportedIn (PT.tiling.P i).X := by
  classical
  intro μ hμ x hx
  rcases Finset.mem_union.mp hμ with hμ | hμ
  · rcases Finset.mem_union.mp hμ with hμ | hμ
    · rw [Finset.mem_singleton.mp hμ]
      simp [FinProb.uniform, hx]
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hμ
      exact posterior_law_supported hPT S q.1 q.2.1.1 q.2.2 q.2.1.2 x hx
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hμ
    unfold candidate_row_law normalize_large_row
    split_ifs with hm
    · change coordinate_row G q.1.1 (S.σ q.2.1.1 q.2.1.2.1.1 q.2.1.2.2) q.2.2 x / _ = 0
      have hz := solver_prior_supported hPT S q.2.1.1 q.2.1.2.1.1 q.2.1.2.2 q.2.1.2.1.2 x hx
      simp [coordinate_row, hz]
    · simp [FinProb.uniform, hx]


theorem physical_prior_candidate {G : LowGeom PT} {F : FreshCell G}
    (physical : PhysicalFreshCertificate G F) (hm : PT.tiling.mode = .lowCluster)
    {i : Fin PT.tiling.m} (S : SliceSolver κ PT.tiling i PT.mesh) (hS : PT.solver i = some S)
    (v : Pos T k) (heven : IsEvenRole v) (hpatch : G.patchOf v = i)
    (pool : F.Pool (G.cellOf v)) (s : F.State (G.cellOf v))
    (ht : F.typical (G.cellOf v) pool) (hs : (F.fresh (G.cellOf v) pool).w s ≠ 0) :
    ∃ q : PriorCandidate S,
      S.σ q.1 q.2.1.1 q.2.2 = F.prior (G.cellOf v) s v ∧ S.σ q.1 q.2.1.1 q.2.2 ≠ 0 := by
  classical
  have hsource := physical_cluster_prior_origin physical hm (G.cellOf v) pool s v rfl heven ht hs
  have hindex : G.cellPatch (G.cellOf v) = i := (G.cellOf_patch v).trans hpatch
  subst i
  rw [hindex] at hsource
  obtain ⟨S', hS', w, W, ys, hW, hprior⟩ := hsource
  have hEq : S' = S := Option.some.inj (hS'.symm.trans hS)
  subst S'
  have hvalid := physical.fresh_spec.fresh_valid (G.cellOf v) pool s ht
    (lt_of_le_of_ne ((F.fresh (G.cellOf v) pool).nonneg s) hs.symm)
  have hsum := (hvalid.2 v rfl heven).1
  refine ⟨(w, ⟨W, hW⟩, ys), hprior.symm, ?_⟩
  intro hz
  have hzero : F.prior (G.cellOf v) s v = 0 := hprior.trans hz
  rw [hzero] at hsum
  norm_num at hsum

theorem cluster_family_prior_capture (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    {G : LowGeom PT} {F : FreshCell G} (physical : PhysicalFreshCertificate G F)
    (hm : PT.tiling.mode = .lowCluster) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (hS : PT.solver i = some S)
    (v : Pos T k) (hleaf : v ∈ PT.tiling.leaf i) (heven : IsEvenRole v)
    (σ : Fin (T.S.N k) → ℝ)
    (hσ : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).ValidInitialPrior v σ) :
    ∃ μ ∈ cluster_family hPT G S, μ.w = σ := by
  classical
  obtain ⟨pool, s, ht, hstate, hread⟩ := hσ.2
  have hp : G.patchOf v = i := (hPT.tiling_valid.prefix_complete v).unique (G.patchOf_leaf v) hleaf
  obtain ⟨q, hq, hq0⟩ := physical_prior_candidate physical hm S hS v heven hp pool s ht (ne_of_gt hstate.2)
  refine ⟨candidate_prior_law hPT S q, ?_, ?_⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  · unfold candidate_prior_law posterior_law
    rw [dif_pos hq0]
    change S.σ q.1 q.2.1.1 q.2.2 = σ
    exact hq.trans (funext hread).symm

theorem cluster_family_row_capture (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    {G : LowGeom PT} {F : FreshCell G} (physical : PhysicalFreshCertificate G F)
    (hm : PT.tiling.mode = .lowCluster) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (hS : PT.solver i = some S)
    (pools : ∀ C, F.Pool C) (s : Config F) (v : Pos T k)
    (htyp : ∀ C ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).scopeCells v, F.typical C (pools C))
    (hstate : ∀ C ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).scopeCells v,
      (Lane_sol_s18_dl.physical_list_context hPT hLow physical).stateValid C (pools C) (s C))
    (hleaf : v ∈ PT.tiling.leaf i) (heven : IsEvenRole v)
    (hmass : (1 / 2 : ℝ) ≤ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).rowMass v
      ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).prior s v)
      ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).label s)) :
    ∃ μ ∈ cluster_family hPT G S, ∀ x, μ.w x =
      (Lane_sol_s18_dl.physical_list_context hPT hLow physical).row v
        ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).prior s v)
        ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).label s) x /
      (Lane_sol_s18_dl.physical_list_context hPT hLow physical).rowMass v
        ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).prior s v)
        ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).label s) := by
  classical
  let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
  have hown : G.cellOf v ∈ D.scopeCells v :=
    Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have hp : G.patchOf v = i := (hPT.tiling_valid.prefix_complete v).unique (G.patchOf_leaf v) hleaf
  obtain ⟨q, hq, hq0⟩ := physical_prior_candidate physical hm S hS v heven hp
    (pools (G.cellOf v)) (s (G.cellOf v)) (htyp _ hown) (ne_of_gt (hstate _ hown).2)
  let t : RowCandidate G S := (⟨v, heven, hp⟩, q, fun a => D.label s (flipPos v a))
  have hraw : coordinate_row G v (S.σ q.1 q.2.1.1 q.2.2) (fun a => D.label s (flipPos v a)) =
      D.row v (D.prior s v) (D.label s) := by
    rw [hq]
    exact (row_eq_coordinate_row D v (D.prior s v) (D.label s)).symm
  have hgate : (1 / 2 : ℝ) ≤ ∑ x, coordinate_row G v (S.σ q.1 q.2.1.1 q.2.2) (fun a => D.label s (flipPos v a)) x := by
    rw [hraw]
    exact hmass
  refine ⟨candidate_row_law hPT G S t, ?_, ?_⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  · intro x
    unfold candidate_row_law normalize_large_row
    rw [dif_pos hgate]
    change coordinate_row G v (S.σ q.1 q.2.1.1 q.2.2) (fun a => D.label s (flipPos v a)) x / _ = _
    rw [hraw]
    rfl


theorem cluster_family_card_bound (hPT : PT.Valid) (G : LowGeom PT) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (hm : PT.tiling.mode = .lowCluster)
    (hn : (100 : ℝ) ≤ T.S.n k) (hh : ((PT.tiling.P i).h : ℝ) ≤ T.S.n k)
    (hlogN : Real.log (T.S.N k : ℝ) ≤ 2 * T.S.n k) :
    ((cluster_family hPT G S).card : ℝ) ≤ 3 * Real.exp (6 * (T.S.n k : ℝ) ^ 2) := by
  classical
  have hN : (1 : ℝ) ≤ T.S.N k := by exact_mod_cast (T.S.N_pos k)
  have hNpos : (0 : ℝ) < T.S.N k := by linarith
  have hnn : (1 : ℝ) ≤ T.S.n k := by linarith
  have hnpos : (0 : ℝ) < T.S.n k := by linarith
  have hlogN0 : 0 ≤ Real.log (T.S.N k : ℝ) := Real.log_nonneg hN
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hpow : Real.rpow (T.S.n k : ℝ) 1.01 ≤ (T.S.n k : ℝ) ^ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hnn (by norm_num : (1.01 : ℝ) ≤ 2)
    simpa only [Real.rpow_eq_pow, Real.rpow_two] using hh
  have hEven : (Fintype.card (EvenRole PT.tiling i) : ℝ) ≤ (2 : ℝ) ^ (PT.tiling.P i).h := by
    have hc := Fintype.card_le_of_injective (fun w : EvenRole PT.tiling i => w.1) Subtype.val_injective
    exact_mod_cast (by simpa [IWord] using hc : Fintype.card (EvenRole PT.tiling i) ≤ 2 ^ (PT.tiling.P i).h)
  have hRecords : (Fintype.card {W : ∀ r, S.Val r // 0 < (S.recLaw PT.parameter).w W} : ℝ) ≤
      Real.exp (Real.rpow (T.S.n k : ℝ) 1.01) := by
    have hc := S.low_support hm PT.parameter
    simpa only [Fintype.card_subtype, SliceSolver.recLaw, Real.rpow_eq_pow] using hc
  have hLabels : Fintype.card (InternalLabels PT.tiling i) = (T.S.N k) ^ (PT.tiling.P i).h := by
    simp [InternalLabels]
  have hPrior : (Fintype.card (PriorCandidate S) : ℝ) ≤
      (2 : ℝ) ^ (PT.tiling.P i).h * Real.exp (Real.rpow (T.S.n k : ℝ) 1.01) *
        (T.S.N k : ℝ) ^ (PT.tiling.P i).h := by
    simp only [PriorCandidate, Fintype.card_prod, hLabels, Nat.cast_mul, Nat.cast_pow]
    nlinarith [mul_le_mul hEven hRecords (by positivity) (by positivity),
      (show (0 : ℝ) ≤ (T.S.N k : ℝ) ^ (PT.tiling.P i).h by positivity)]
  have hSites : (Fintype.card {v : Pos T k // IsEvenRole v ∧ G.patchOf v = i} : ℝ) ≤ (2 : ℝ) ^ T.S.n k := by
    have hc := Fintype.card_le_of_injective (fun v : {v : Pos T k // IsEvenRole v ∧ G.patchOf v = i} => v.1) Subtype.val_injective
    exact_mod_cast (by simpa using hc : Fintype.card {v : Pos T k // IsEvenRole v ∧ G.patchOf v = i} ≤ 2 ^ T.S.n k)
  have hRows : (Fintype.card (RowCandidate G S) : ℝ) ≤
      (2 : ℝ) ^ T.S.n k * ((2 : ℝ) ^ (PT.tiling.P i).h * Real.exp (Real.rpow (T.S.n k : ℝ) 1.01) *
        (T.S.N k : ℝ) ^ (PT.tiling.P i).h) * (T.S.N k : ℝ) ^ T.S.n k := by
    simp only [RowCandidate, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
    have hp := mul_le_mul hSites hPrior (by positivity) (by positivity)
    have hp' := mul_le_mul_of_nonneg_right hp (show (0 : ℝ) ≤ (T.S.N k : ℝ) ^ T.S.n k by positivity)
    simpa only [PriorCandidate, Fintype.card_prod, hLabels, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hp'
  have hPriorBound : (Fintype.card (PriorCandidate S) : ℝ) ≤ Real.exp (6 * (T.S.n k : ℝ) ^ 2) := by
    apply hPrior.trans
    have heq : (2 : ℝ) ^ (PT.tiling.P i).h * Real.exp (Real.rpow (T.S.n k : ℝ) 1.01) *
        (T.S.N k : ℝ) ^ (PT.tiling.P i).h =
        Real.exp ((PT.tiling.P i).h * Real.log 2 + Real.rpow (T.S.n k : ℝ) 1.01 + (PT.tiling.P i).h * Real.log (T.S.N k : ℝ)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num), Real.exp_log hNpos]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right hh (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have h2 := mul_le_mul hh hlogN hlogN0 (by linarith)
    nlinarith
  have hRowsBound : (Fintype.card (RowCandidate G S) : ℝ) ≤ Real.exp (6 * (T.S.n k : ℝ) ^ 2) := by
    apply hRows.trans
    have heq : (2 : ℝ) ^ T.S.n k * ((2 : ℝ) ^ (PT.tiling.P i).h * Real.exp (Real.rpow (T.S.n k : ℝ) 1.01) *
        (T.S.N k : ℝ) ^ (PT.tiling.P i).h) * (T.S.N k : ℝ) ^ T.S.n k =
        Real.exp (((T.S.n k : ℝ) + (PT.tiling.P i).h) * Real.log 2 + Real.rpow (T.S.n k : ℝ) 1.01 +
          ((PT.tiling.P i).h + (T.S.n k : ℝ)) * Real.log (T.S.N k : ℝ)) := by
      simp only [add_mul, Real.exp_add, Real.exp_nat_mul, Real.exp_log hNpos, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [heq]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right hh (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have h2 := mul_le_mul (show (PT.tiling.P i).h + (T.S.n k : ℝ) ≤ 2 * T.S.n k by linarith) hlogN hlogN0 (by linarith)
    nlinarith
  have hc : (cluster_family hPT G S).card ≤ 1 + Fintype.card (PriorCandidate S) + Fintype.card (RowCandidate G S) := by
    have hp := Finset.card_image_le (s := Finset.univ) (f := candidate_prior_law hPT S)
    have hr := Finset.card_image_le (s := Finset.univ) (f := candidate_row_law hPT G S)
    have h1 := Finset.card_union_le {FinProb.uniform (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1}
      (Finset.univ.image (candidate_prior_law hPT S))
    have h2 := Finset.card_union_le ({FinProb.uniform (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1} ∪
      Finset.univ.image (candidate_prior_law hPT S)) (Finset.univ.image (candidate_row_law hPT G S))
    simp only [Finset.card_univ, Finset.card_singleton] at hp hr h1 h2
    dsimp only [cluster_family]
    omega
  have hcR : ((cluster_family hPT G S).card : ℝ) ≤ 1 + Fintype.card (PriorCandidate S) + Fintype.card (RowCandidate G S) := by
    exact_mod_cast hc
  have he : 1 ≤ Real.exp (6 * (T.S.n k : ℝ) ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  linarith


theorem colour_family_count_condition (n χ m : ℕ) (K : ℝ)
    (hn : (100 : ℝ) ≤ n) (hχ : 0 < χ) (hK : 0 ≤ K) (hKn : K ≤ n)
    (hm : (m : ℝ) ≤ 3 * Real.exp (6 * (n : ℝ) ^ 2))
    (hc : (χ : ℝ) ≤ Real.exp (K * Real.log (n : ℝ))) :
    2 * (m : ℝ) * χ * Real.exp (-1 / (2 * (χ : ℝ) ^ 2 * (1 / ((χ : ℝ) ^ 2 * (n : ℝ) ^ 10)))) < 1 := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hχpos : (0 : ℝ) < χ := by exact_mod_cast hχ
  have hlog : Real.log (n : ℝ) ≤ n := by linarith [Real.log_le_sub_one_of_pos hnpos]
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hKlog : K * Real.log (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hh := mul_le_mul hKn hlog hlog0 (by linarith)
    nlinarith
  have hn8 : (32 : ℝ) ≤ (n : ℝ) ^ 8 := by
    calc
      _ ≤ (2 : ℝ) ^ 8 := by norm_num
      _ ≤ (n : ℝ) ^ 8 := by gcongr; linarith
  have hn10 : 32 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 10 := by
    rw [show (n : ℝ) ^ 10 = (n : ℝ) ^ 2 * (n : ℝ) ^ 8 by ring]
    nlinarith [mul_le_mul_of_nonneg_left hn8 (sq_nonneg (n : ℝ))]
  have hexponent : 6 * (n : ℝ) ^ 2 + K * Real.log (n : ℝ) - (n : ℝ) ^ 10 / 2 ≤ -8 := by
    nlinarith
  have hscalar : -1 / (2 * (χ : ℝ) ^ 2 * (1 / ((χ : ℝ) ^ 2 * (n : ℝ) ^ 10))) = -(n : ℝ) ^ 10 / 2 := by
    field_simp <;> ring
  rw [hscalar]
  calc
    _ ≤ 2 * (3 * Real.exp (6 * (n : ℝ) ^ 2)) * Real.exp (K * Real.log (n : ℝ)) * Real.exp (-(n : ℝ) ^ 10 / 2) := by
      gcongr
    _ = 6 * Real.exp (6 * (n : ℝ) ^ 2 + K * Real.log (n : ℝ) - (n : ℝ) ^ 10 / 2) := by
      rw [show 6 * (n : ℝ) ^ 2 + K * Real.log (n : ℝ) - (n : ℝ) ^ 10 / 2 =
        6 * (n : ℝ) ^ 2 + K * Real.log (n : ℝ) + (-(n : ℝ) ^ 10 / 2) by ring, Real.exp_add, Real.exp_add]
      ring
    _ ≤ 6 * Real.exp (-8) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ < 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      apply (div_lt_iff₀ (Real.exp_pos 8)).mpr
      linarith [Real.add_one_le_exp 8]

theorem exp_gain_cancel (d g c : ℝ) (hd : 2 ≤ d) (hg : 0 ≤ g) (hc : c ≤ Real.exp (2 * g)) :
    Real.exp (-d * g) * c ≤ 1 := by
  calc
    _ ≤ Real.exp (-d * g) * Real.exp (2 * g) := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ = Real.exp ((2 - d) * g) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hg)

theorem uniform_scaled_atom (n N χ : ℕ) (hN : 0 < N) (hχ : 0 < χ) (hn : 0 < n)
    (w : ℝ) (hw : w ≤ (n : ℝ) / N) (hp : (χ : ℝ) ^ 2 * (n : ℝ) ^ 11 ≤ N) :
    w ≤ 1 / ((χ : ℝ) ^ 2 * (n : ℝ) ^ 10) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hχr : (0 : ℝ) < χ := by exact_mod_cast hχ
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  apply hw.trans
  apply (div_le_div_iff₀ hNr (by positivity : (0 : ℝ) < (χ : ℝ) ^ 2 * (n : ℝ) ^ 10)).mpr
  nlinarith [hp]

theorem suppressed_prior_atom (n N χ h : ℕ) (hn : 0 < n) (hN : 0 < N) (hχ : 0 < χ)
    (g w : ℝ) (hg : 0 ≤ g) (hc : (χ : ℝ) ^ 2 ≤ Real.exp (2 * g))
    (hcap : (N : ℝ) * w ≤ (2 : ℝ) ^ h * Real.exp (-500 * g))
    (hh : (2 : ℝ) ^ h ≤ n) (hhost : (n : ℝ) ^ 11 ≤ N) :
    w ≤ 1 / ((χ : ℝ) ^ 2 * (n : ℝ) ^ 10) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hχr : (0 : ℝ) < χ := by exact_mod_cast hχ
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_right hcap (show (0 : ℝ) ≤ (χ : ℝ) ^ 2 by positivity)
  have hgexp := exp_gain_cancel 500 g ((χ : ℝ) ^ 2) (by norm_num) hg hc
  have hp := mul_le_mul_of_nonneg_left hgexp (show (0 : ℝ) ≤ (2 : ℝ) ^ h by positivity)
  have hscale : w * (χ : ℝ) ^ 2 ≤ (n : ℝ) / N := by
    apply (le_div_iff₀ hNr).mpr
    nlinarith
  have hhost' : (n : ℝ) / N ≤ 1 / (n : ℝ) ^ 10 := by
    apply (div_le_div_iff₀ hNr (by positivity : (0 : ℝ) < (n : ℝ) ^ 10)).mpr
    nlinarith
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (χ : ℝ) ^ 2 * (n : ℝ) ^ 10)).mpr
  have hbound := (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 10)).mp (hscale.trans hhost')
  nlinarith

theorem suppressed_row_atom (n χ : ℕ) (hn : (100 : ℝ) ≤ n) (hχ : 0 < χ)
    (C g r w : ℝ) (hC : 1 ≤ C) (hg : 0 ≤ g) (hr : 0 ≤ r)
    (hc : (χ : ℝ) ^ 2 ≤ Real.exp (2 * g))
    (hcap : w ≤ 2 / C * Real.exp (-498 * g) * r) (hp : r ≤ 2 / (n : ℝ) ^ 12) :
    w ≤ (1 / ((χ : ℝ) ^ 2 * (n : ℝ) ^ 10)) / 2 := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hχr : (0 : ℝ) < χ := by exact_mod_cast hχ
  have hCpos : 0 < C := by linarith
  have hgexp := exp_gain_cancel 498 g ((χ : ℝ) ^ 2) (by norm_num) hg hc
  have hmult := mul_le_mul_of_nonneg_right hcap (show (0 : ℝ) ≤ (χ : ℝ) ^ 2 by positivity)
  have he : 2 / C * Real.exp (-498 * g) * r * (χ : ℝ) ^ 2 ≤ 2 * r := by
    have hh := mul_le_mul_of_nonneg_left hgexp (show 0 ≤ 2 / C * r by positivity)
    have h2C : 2 / C ≤ (2 : ℝ) := (div_le_iff₀ hCpos).mpr (by linarith)
    have hh' := mul_le_mul_of_nonneg_right h2C hr
    nlinarith
  have hs : w * (χ : ℝ) ^ 2 ≤ 4 / (n : ℝ) ^ 12 := by
    calc
      _ ≤ 2 * r := hmult.trans he
      _ ≤ 2 * (2 / (n : ℝ) ^ 12) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = _ := by ring
  have hb : 4 / (n : ℝ) ^ 12 ≤ 1 / (2 * (n : ℝ) ^ 10) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 12) (by positivity : (0 : ℝ) < 2 * (n : ℝ) ^ 10)).mpr
    have hh : 8 ≤ (n : ℝ) ^ 2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ (n : ℝ) ^ 10 by positivity)
    nlinarith
  have hb' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ) ^ 10)).mp (hs.trans hb)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2)).mpr
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (χ : ℝ) ^ 2 * (n : ℝ) ^ 10)).mpr
  nlinarith


theorem profile_atom_scales (hPT : PT.Valid) {G : LowGeom PT} {F : FreshCell G}
    (physical : PhysicalFreshCertificate G F) (hlog : 1 ≤ Real.log (T.S.n k : ℝ)) :
    ∀ i, (2 : ℝ) ^ (PT.tiling.P i).h ≤ T.S.n k ∧
      1 / ((PT.tiling.P i).M : ℝ) ≤ (T.S.n k : ℝ) / T.S.N k := by
  intro i
  let L := Real.log (T.S.n k : ℝ)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hn : (0 : ℝ) < T.S.n k := by
    have hh := physical.quantitative.n_large
    exact_mod_cast (show 0 < T.S.n k by omega)
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hp : Real.rpow L (1 / 10 : ℝ) ≤ L := by
    have hh := Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1 / 10 : ℝ) ≤ 1)
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using hh
  have hh : ((PT.tiling.P i).h : ℝ) ≤ L := (physical.quantitative.height_bound i).trans hp
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hsqrt : Real.sqrt L ≤ L := by
    change 1 ≤ L at hlog
    nlinarith [Real.sq_sqrt hL0, Real.sqrt_nonneg L]
  constructor
  · calc
      _ = Real.exp ((PT.tiling.P i).h * Real.log 2) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by nlinarith [(show (0 : ℝ) ≤ (PT.tiling.P i).h by positivity)])
      _ = _ := Real.exp_log hn
  · have hr : Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ L :=
      (physical.quantitative.patch_mass_bound i).trans hsqrt
    have hr' : (T.S.N k : ℝ) / (PT.tiling.P i).M ≤ T.S.n k := by
      have ht := Real.exp_le_exp.mpr hr
      simpa only [L, Real.exp_log (div_pos hN hM), Real.exp_log hn] using ht
    apply (div_le_div_iff₀ hM hN).mpr
    have ht := (div_le_iff₀ hM).mp hr'
    nlinarith

theorem chi_host_product (n N χ : ℕ) (hn : (1 : ℝ) < n) (hχ : 0 < χ)
    (K g : ℝ) (hK : 0 ≤ K) (hg : g ≤ K * Real.log (n : ℝ))
    (hc : (χ : ℝ) ≤ Real.exp g) (hhost : Real.rpow (n : ℝ) (2 * K + 12) ≤ N) :
    (χ : ℝ) ^ 2 * (n : ℝ) ^ 11 ≤ N ∧ (n : ℝ) ^ 11 ≤ N := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hL0 : 0 ≤ Real.log (n : ℝ) := (Real.log_pos hn).le
  have hχ2 : (χ : ℝ) ^ 2 ≤ Real.exp (2 * K * Real.log (n : ℝ)) := by
    calc
      _ ≤ (Real.exp g) ^ 2 := by gcongr
      _ = Real.exp (2 * g) := by rw [← Real.exp_nat_mul]; norm_num only [Nat.cast_ofNat]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hn11 : (n : ℝ) ^ 11 = Real.exp (11 * Real.log (n : ℝ)) := by
    have he := Real.exp_nat_mul (Real.log (n : ℝ)) 11
    norm_num only [Nat.cast_ofNat] at he
    rw [Real.exp_log hnpos] at he
    exact he.symm
  have hp : (χ : ℝ) ^ 2 * (n : ℝ) ^ 11 ≤ N := by
    calc
      _ ≤ Real.exp (2 * K * Real.log (n : ℝ)) * Real.exp (11 * Real.log (n : ℝ)) := by rw [← hn11]; gcongr
      _ = Real.exp ((2 * K + 11) * Real.log (n : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((2 * K + 12) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.rpow (n : ℝ) (2 * K + 12) := by rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hnpos]; congr 1; ring
      _ ≤ _ := hhost
  refine ⟨hp, ?_⟩
  have hχr : (1 : ℝ) ≤ χ := by exact_mod_cast hχ
  have hs : (1 : ℝ) ≤ (χ : ℝ) ^ 2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_right hs (show (0 : ℝ) ≤ (n : ℝ) ^ 11 by positivity)
  nlinarith

theorem admissible_class_exponent (hκ : κ.Admissible) : 24 ≤ κ.A0 * Real.log 2 := by
  have hP : 1 ≤ κ.P := by have := hκ.P_big.2; omega
  have hR : 1 ≤ κ.R := by rw [hκ.R_eq]; exact one_le_pow₀ hP
  have hRr : (1 : ℝ) ≤ κ.R := by exact_mod_cast hR
  have hA : (10 ^ 6 : ℝ) ≤ κ.A0 := by nlinarith [hκ.A0_big]
  have hl : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith

theorem late_count_decay (hκ : κ.Admissible) {G : LowGeom PT} {F : FreshCell G}
    (hL16 : L16QuantitativeValidity G F) (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (v : Pos T k) (heven : IsEvenRole v) :
    Real.rpow 2 (-((late_coordinates G v).card : ℝ)) ≤ 2 / (T.S.n k : ℝ) ^ 12 := by
  classical
  have hnpos : (0 : ℝ) < T.S.n k := by
    have hh := (Classical.choice hL16.physical).quantitative.n_large
    exact_mod_cast (show 0 < T.S.n k by omega)
  have hnat := hL16.remaining_count v heven ⟨0, hL16.r_pos⟩
  simp only [Nat.sub_zero] at hnat
  have heq : (Finset.univ.filter fun a : Fin (T.S.n k) =>
      ∃ s : Fin G.r, 0 ≤ s.val ∧ G.classOf (flipPos v a) = some s) = late_coordinates G v := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, late_coordinates]
    cases hc : G.classOf (flipPos v a) <;> simp [hc]
  change G.r / 2 ≤ (Finset.univ.filter fun a : Fin (T.S.n k) =>
    ∃ s : Fin G.r, 0 ≤ s.val ∧ G.classOf (flipPos v a) = some s).card at hnat
  rw [heq] at hnat
  have hcount : G.r ≤ 2 * (late_coordinates G v).card + 1 := by omega
  have hcountR : (G.r : ℝ) ≤ 2 * (late_coordinates G v).card + 1 := by exact_mod_cast hcount
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith
  have h1 := mul_le_mul_of_nonneg_right (admissible_class_exponent hκ) hL0
  have h2 := mul_le_mul_of_nonneg_right hL16.r_lower hl2.le
  have h3 := mul_le_mul_of_nonneg_right hcountR hl2.le
  have hexp : -((late_coordinates G v).card : ℝ) * Real.log 2 ≤ Real.log 2 - 12 * Real.log (T.S.n k : ℝ) := by
    nlinarith
  calc
    _ = Real.exp (-((late_coordinates G v).card : ℝ) * Real.log 2) := by
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ Real.exp (Real.log 2 - 12 * Real.log (T.S.n k : ℝ)) := Real.exp_le_exp.mpr hexp
    _ = _ := by
      have he := Real.exp_nat_mul (Real.log (T.S.n k : ℝ)) 12
      norm_num only [Nat.cast_ofNat] at he
      rw [Real.exp_log hnpos] at he
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2), he]


theorem solver_prior_envelope (hPT : PT.Valid) {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (v : EvenRole PT.tiling i)
    (W : ∀ r, S.Val r) (ys : InternalLabels PT.tiling i)
    (hW : 0 < (S.recLaw PT.parameter).w W) :
    ∀ x, S.σ v W ys x ≠ 0 → x ∈ PT.envelope i := by
  classical
  intro x hx
  have hσ : S.σ v W ys ≠ 0 := by intro hz; apply hx; rw [hz]; rfl
  obtain ⟨q, hq, hsupp⟩ := S.σ_support v W ys hσ
  have hact : q ∈ PT.activeVertices := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq PT.parameter hW⟩
  rw [hPT.envelope_eq]
  exact Finset.mem_biUnion.mpr ⟨q, hact, (hsupp x hx).1⟩

theorem cluster_palette_colouring_at (hκ : κ.Admissible) (hPT : PT.Valid)
    {G : LowGeom PT} {F : FreshCell G} (hL16 : L16QuantitativeValidity G F)
    (hLow : PT.tiling.mode.isLow) (hm : PT.tiling.mode = .lowCluster)
    (hn : (100 : ℝ) ≤ T.S.n k) (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (hDensity : 1 ≤ densityScale T k) (hKn : κ.KB ≤ T.S.n k)
    (hHost : Real.rpow (T.S.n k : ℝ) (2 * κ.KB + 12) ≤ T.S.N k)
    (hlogN : Real.log (T.S.N k : ℝ) ≤ 2 * T.S.n k)
    (hb : 3 * bstar T k ≤ 1 / 4)
    (hcross : ∀ i, 12 * bstar T k * (PT.tiling.P i).ℓ ≤ 1)
    (hgn : ∀ i, PT.tiling.gain i ≤ T.S.n k)
    (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (ψ : S17PaletteCode i hle) (hCode : PaletteCodeSpec i hle ψ) :
    ∃ colours : S17PaletteAssignment ψ,
      PaletteRetentionSpec (Lane_sol_s18_dl.physical_list_context hPT hLow (Classical.choice hL16.physical))
        i hle ψ colours ∧
      ∀ c, (Finset.univ.filter fun x : Fin (T.S.N k) => x ∈ (PT.tiling.P i).X ∧ colours x = c).Nonempty := by
  classical
  let physical := Classical.choice hL16.physical
  let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
  obtain ⟨S, hS⟩ := hPT.cluster_solver (by simp [hm, Mode.isCluster]) i
  let family := cluster_family hPT G S
  let χ := s17Chi ψ
  let b : ℝ := 1 / ((χ : ℝ) ^ 2 * (T.S.n k : ℝ) ^ 10)
  have hχ : 0 < χ := by dsimp [χ, s17Chi, ListGateContext.PaletteCode.chi]; positivity
  have hχr : (0 : ℝ) < χ := by exact_mod_cast hχ
  have hnpos : (0 : ℝ) < T.S.n k := by linarith
  have hnNat : 0 < T.S.n k := by exact_mod_cast hnpos
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hKB : 0 ≤ κ.KB := (show (0 : ℝ) ≤ 10 ^ 6 * κ.R by positivity).trans hκ.KB_big
  have hchi : (χ : ℝ) ≤ Real.exp (PT.tiling.gain i) := hCode.2.2.2
  have hchi2 : (χ : ℝ) ^ 2 ≤ Real.exp (2 * PT.tiling.gain i) := by
    calc
      _ ≤ (Real.exp (PT.tiling.gain i)) ^ 2 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num only [Nat.cast_ofNat]
  have hChiprod := chi_host_product (T.S.n k) (T.S.N k) χ (by linarith) hχ κ.KB (PT.tiling.gain i)
    hKB (hL16.gain_upper i) hchi hHost
  have hgi : 0 ≤ PT.tiling.gain i := by have := (cluster_gain_controls hκ hPT hm i).2; linarith
  have hscales := profile_atom_scales hPT physical hlog i
  have hUni : ∀ x, (FinProb.uniform (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1).w x ≤ b := by
    intro x
    change (if x ∈ (PT.tiling.P i).X then ((PT.tiling.P i).X.card : ℝ)⁻¹ else 0) ≤ b
    split_ifs
    · rw [(PT.tiling.P i).cardX]
      simpa only [b, one_div] using uniform_scaled_atom (T.S.n k) (T.S.N k) χ (T.S.N_pos k) hχ hnNat _ hscales.2 hChiprod.1
    · exact hbpos.le
  have hell : ∀ j, (PT.tiling.P j).ℓ ≤ T.S.n k := by
    intro j
    have hnlog := Real.log_le_sub_one_of_pos hnpos
    have hL0 : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith
    have hsqrt : Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ Real.log (T.S.n k : ℝ) := by
      nlinarith [Real.sq_sqrt hL0, Real.sqrt_nonneg (Real.log (T.S.n k : ℝ))]
    have hℓ := (physical.quantitative.prefix_bound j).trans hsqrt
    have hh : ((PT.tiling.P j).ℓ : ℝ) ≤ T.S.n k := by linarith
    exact_mod_cast hh
  have hAtom : ∀ μ ∈ family, ∀ x, μ.w x ≤ b := by
    intro μ hμ x
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · rcases Finset.mem_union.mp hμ with hμ | hμ
      · rw [Finset.mem_singleton.mp hμ]; exact hUni x
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hμ
        unfold candidate_prior_law posterior_law
        split_ifs with hσ
        · exact suppressed_prior_atom (T.S.n k) (T.S.N k) χ (PT.tiling.P i).h hnNat (T.S.N_pos k) hχ
            (PT.tiling.gain i) (S.σ q.1 q.2.1.1 q.2.2 x) hgi hchi2 (S.σ_cap _ _ _ x) hscales.1 hChiprod.2
        · exact hUni x
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hμ
      let v := q.1.1
      let σ := S.σ q.2.1.1 q.2.1.2.1.1 q.2.1.2.2
      have hp : G.patchOf v = i := q.1.2.2
      obtain ⟨hOwn, hg1⟩ := cluster_gain_controls hκ hPT hm (G.patchOf v)
      have hraw := cluster_coordinate_row_bound hPT G hm v (by simpa only [hp] using hle) (hell _)
        (hL16.internal_cosets _) hnpos hb (hcross _) hOwn hg1 (hgn _) σ q.2.2
        (S.σ_nonneg _ _ _)
        (by intro y hy; simpa only [hp] using solver_prior_envelope hPT S q.2.1.1 q.2.1.2.1.1 q.2.1.2.2 q.2.1.2.1.2 y hy)
        (by intro y; simpa only [hp] using S.σ_cap q.2.1.1 q.2.1.2.1.1 q.2.1.2.2 y)
      simp only [hp] at hraw
      have hsmall : ∀ y, coordinate_row G v σ q.2.2 y ≤ b / 2 := by
        intro y
        exact suppressed_row_atom (T.S.n k) χ hn hχ (densityScale T k) (PT.tiling.gain i)
          (Real.rpow 2 (-((late_coordinates G v).card : ℝ))) (coordinate_row G v σ q.2.2 y)
          hDensity hgi (Real.rpow_nonneg (by norm_num) _) hchi2 (hraw y)
          (late_count_decay hκ hL16 hlog v q.1.2.1)
      have hnLaw := normalize_large_row_atom (FinProb.uniform (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1)
        (coordinate_row G v σ q.2.2) (coordinate_row_nonneg G v σ q.2.2 (S.σ_nonneg _ _ _))
        (b / 2) (by positivity) hsmall (by intro y; convert hUni y using 1 <;> ring) x
      have heq : 2 * (b / 2) = b := by ring
      rw [heq] at hnLaw
      exact hnLaw
  have hCard := cluster_family_card_bound hPT G S hm hn (by exact_mod_cast hle) hlogN
  have hChiKB : (χ : ℝ) ≤ Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) :=
    hchi.trans (Real.exp_le_exp.mpr (hL16.gain_upper i))
  have hCount := colour_family_count_condition (T.S.n k) χ family.card κ.KB hn hχ hKB hKn hCard hChiKB
  apply palette_retention_of_family D i hle ψ family b hbpos hAtom hCount
  · exact cluster_family_supported hPT G S
  · exact cluster_family_uniform hPT G S
  · exact cluster_family_row_capture hPT hLow physical hm S hS
  · exact cluster_family_prior_capture hPT hLow physical hm S hS


theorem gain_nonneg (hκ : κ.Admissible) (i : Fin PT.tiling.m) : 0 ≤ PT.tiling.gain i := by
  have ha : 0 ≤ κ.a := by rw [hκ.a_eq]; exact div_nonneg hκ.θ_rng.1.le (by norm_num)
  cases hm : PT.tiling.mode <;> simp only [Tiling.gain, hm] <;> positivity

end HypercubeRamsey.S18.Lane_sol_d18l_pal
