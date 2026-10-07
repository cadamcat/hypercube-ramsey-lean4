import HypercubeRamsey.S17.Needs
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Tools.LinearCode
import HypercubeRamsey.Tools.Concentration

namespace HypercubeRamsey.Lane_q_s17_pal

open Classical
open ListGateContext
open scoped BigOperators

private theorem zmodTwo_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hval := ZMod.val_lt x
  by_cases hz : x.val = 0
  · exact Or.inl ((ZMod.val_eq_zero x).mp hz)
  · have hone : x.val = 1 := by omega
    exact Or.inr ((ZMod.val_eq_one (by norm_num : 1 < 2) x).mp hone)

private theorem linearFiberCardEq (h m : ℕ)
    (L : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (hL : Function.Surjective L) (c₁ c₂ : Fin m → ZMod 2) :
    Fintype.card {x : Fin h → ZMod 2 // L x = c₁} =
      Fintype.card {x : Fin h → ZMod 2 // L x = c₂} := by
  classical
  obtain ⟨z, hz⟩ := hL (c₂ - c₁)
  let e : {x : Fin h → ZMod 2 // L x = c₁} ≃
      {x : Fin h → ZMod 2 // L x = c₂} := {
    toFun := fun x => (⟨x.1 + z, by
      rw [map_add, x.2, hz]
      abel⟩ : {x : Fin h → ZMod 2 // L x = c₂})
    invFun := fun x => (⟨x.1 - z, by
      rw [map_sub, x.2, hz]
      abel⟩ : {x : Fin h → ZMod 2 // L x = c₁})
    left_inv := by
      intro x
      apply Subtype.ext
      exact add_sub_cancel_right x.1 z
    right_inv := by
      intro x
      apply Subtype.ext
      exact sub_add_cancel x.1 z
  }
  exact Fintype.card_congr e

theorem weightBall_entropyBound (h w : ℕ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hw : (w : ℝ) ≤ ρ * h) :
    ((LinearCodePToolsCubeR.weightBall h w).card : ℝ) ≤
      Real.exp (Real.binEntropy ρ * h) := by
  classical
  let F : Finset (Fin (h + 1)) := Finset.univ.filter fun j => j.val ≤ w
  let G : Finset (Fin (h + 1)) :=
    Finset.univ.filter fun j => (j.val : ℝ) ≤ ρ * h
  have whR : (w : ℝ) ≤ h := by nlinarith
  have wh : w ≤ h := by exact_mod_cast whR
  have hFG : F ⊆ G := by
    intro j hj
    simp only [F, G, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact le_trans (by exact_mod_cast hj) hw
  have hsumF :
      (∑ j ∈ F, (Nat.choose h j.val : ℝ)) =
        ∑ j ∈ Finset.range (w + 1), (Nat.choose h j : ℝ) := by
    calc
      _ = ∑ j : Fin (h + 1), if j.val ≤ w then
          (Nat.choose h j.val : ℝ) else 0 := by
        simp [F, Finset.sum_filter]
      _ = ∑ j ∈ Finset.range (h + 1),
          if j ≤ w then (Nat.choose h j : ℝ) else 0 := by
        rw [Fin.sum_univ_eq_sum_range
          (fun j : ℕ => if j ≤ w then (Nat.choose h j : ℝ) else 0) (h + 1)]
      _ = ∑ j ∈ (Finset.range (h + 1)).filter (fun j => j ≤ w),
          (Nat.choose h j : ℝ) := by
        rw [Finset.sum_filter]
      _ = ∑ j ∈ Finset.range (w + 1), (Nat.choose h j : ℝ) := by
        have hf : (Finset.range (h + 1)).filter (fun j => j ≤ w) =
            Finset.range (w + 1) := by
          ext j
          simp [Nat.lt_succ_iff]
          omega
        rw [hf]
  have hsumG :
      (∑ j ∈ G, (Nat.choose h j.val : ℝ)) ≤ Real.exp (Real.binEntropy ρ * h) := by
    simpa [G] using binomialEntropyBound h ρ hρ0 hρhalf
  have hsumFG :
      (∑ j ∈ F, (Nat.choose h j.val : ℝ)) ≤
        ∑ j ∈ G, (Nat.choose h j.val : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hFG (by intros; positivity)
  have hcard := LinearCodePToolsCubeR.card_weightBall h w
  have hcardReal : ((LinearCodePToolsCubeR.weightBall h w).card : ℝ) =
      ∑ j ∈ Finset.range (w + 1), (Nat.choose h j : ℝ) := by
    exact_mod_cast hcard
  calc
    ((LinearCodePToolsCubeR.weightBall h w).card : ℝ) =
        ∑ j ∈ Finset.range (w + 1), (Nat.choose h j : ℝ) := hcardReal
    _ = ∑ j ∈ F, (Nat.choose h j.val : ℝ) := hsumF.symm
    _ ≤ ∑ j ∈ G, (Nat.choose h j.val : ℝ) := hsumFG
    _ ≤ Real.exp (Real.binEntropy ρ * h) := hsumG

theorem realBinEntropy_eq_custom (ρ : ℝ) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    Real.binEntropy ρ = HypercubeRamsey.binEntropy ρ := by
  simp only [Real.binEntropy, HypercubeRamsey.binEntropy, if_neg hρ0, if_neg hρ1,
    Real.log_inv]
  ring

theorem internalWordEvenFiberCard
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (hPT : PT.Valid)
    (hfree : ∃ j : Fin (T.S.n k), (PT.tiling.P i).ℓ ≤ j.val ∧
      j.val < T.S.n k - (PT.tiling.P i).h)
    (a : Fin (PT.tiling.P i).h → ZMod 2) :
    (Finset.univ.filter fun v : Pos T k =>
      v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧
        internalBits i hle v = a).card =
      2 ^ (T.S.n k -
        (Finset.univ.filter fun j : Fin (T.S.n k) =>
          j.val < (PT.tiling.P i).ℓ ∨
            T.S.n k - (PT.tiling.P i).h ≤ j.val).card - 1) := by
  classical
  let n := T.S.n k
  let ell := (PT.tiling.P i).ℓ
  let h := (PT.tiling.P i).h
  let S : Finset (Fin n) := Finset.univ.filter fun j => j.val < ell ∨ n - h ≤ j.val
  have hfit : ell + h ≤ n := by
    have hEll : ell ≤ Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ := by
      dsimp [ell]
      exact Finset.le_sup (s := Finset.univ)
        (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) (Finset.mem_univ i)
    have hH : h ≤ Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h := by
      dsimp [h]
      exact Finset.le_sup (s := Finset.univ)
        (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
    have hglobal := hPT.tiling_valid.prefix_internal_length
    change (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) +
        (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h) ≤ n at hglobal
    omega
  obtain ⟨j, hjell, hjtop⟩ := hfree
  have hjnotS : j ∉ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [n, h, ell]
    omega
  have hSproper : S ⊂ (Finset.univ : Finset (Fin n)) := by
    refine ⟨Finset.subset_univ _, ?_⟩
    intro hEq
    have : j ∈ S := hEq (Finset.mem_univ j)
    exact hjnotS this
  have hScard : S.card < n := by
    have hlt := Finset.card_lt_card hSproper
    simpa [Fintype.card_fin] using hlt
  let z : ∀ q : S, Bool := fun q =>
    if hprefix : q.1.val < ell then
      PT.tiling.w i q.1
    else
      if a ⟨q.1.val - (n - h), by
        have hmem := (Finset.mem_filter.mp q.2).2
        dsimp [S, n, h, ell] at hmem
        omega⟩ = 0 then false else true
  have hagree (v : Pos T k) :
      (∀ q : S, v q.1 = z q) ↔
        v ∈ PT.tiling.leaf i ∧ internalBits i hle v = a := by
    constructor
    · intro hv
      constructor
      · simp only [Tiling.leaf, prefixLeaf, Set.mem_setOf_eq]
        intro q hq
        let qS : S := ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hq⟩⟩
        have hqv := hv qS
        have hqpref : qS.1.val < ell := by simpa [qS] using hq
        have hqcolor : z qS = PT.tiling.w i q := by
          dsimp [z]
          rw [dif_pos hqpref]
        change v q = z qS at hqv
        rw [hqcolor] at hqv
        exact hqv
      · funext q
        let r : Fin n := ⟨n - h + q.val, by omega⟩
        have hrS : r ∈ S := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, Or.inr ?_⟩
          dsimp [r]
          omega
        let rS : S := ⟨r, hrS⟩
        have hrnotpre : ¬ r.val < ell := by
          have := hfit
          dsimp [r, n, h, ell] at this ⊢
          omega
        have hrv := hv rS
        have hsub : r.val - (n - h) = q.val := by dsimp [r]; omega
        have hidx : (⟨r.val - (n - h), by omega⟩ : Fin h) = q := by
          apply Fin.ext
          exact hsub
        have hrv' : v r = (if a q = 0 then false else true) := by
          change v r = z rS at hrv
          dsimp [z] at hrv
          rw [dif_neg hrnotpre, hidx] at hrv
          exact hrv
        have hbits : (if v r then 1 else 0) = a q := by
          rcases zmodTwo_eq_zero_or_one (a q) with ha | ha
          · have hv : v r = false := by simpa [ha] using hrv'
            simp [hv, ha]
          · have hv : v r = true := by simpa [ha] using hrv'
            simp [hv, ha]
        simpa [internalBits, r, n, h] using hbits
    · rintro ⟨hvleaf, hbits⟩ q
      have hqmem := (Finset.mem_filter.mp q.2).2
      by_cases hpre : q.1.val < ell
      · have hleaf := hvleaf
        simp only [Tiling.leaf, prefixLeaf, Set.mem_setOf_eq] at hleaf
        have hval := hleaf q.1 hpre
        simp [z, hpre, hval]
      · have htop : n - h ≤ q.1.val := by
          dsimp [S, n, h, ell] at hqmem
          omega
        let r : Fin h := ⟨q.1.val - (n - h), by omega⟩
        have hr : n - h + r.val = q.1.val := by dsimp [r]; omega
        have hbit : (if v ⟨n - h + r.val, by omega⟩ then 1 else 0) = a r := by
          simpa [internalBits] using congrFun hbits r
        have hcoord : q.1 = ⟨n - h + r.val, by omega⟩ := by
          apply Fin.ext
          exact hr.symm
        have hz : v q.1 = (if a r = 0 then false else true) := by
          rw [hcoord]
          cases hv : v ⟨n - h + r.val, by omega⟩
          · have ha : a r = 0 := by simpa [hv] using hbit.symm
            simp [hv, ha]
          · have ha : a r = 1 := by simpa [hv] using hbit.symm
            simp [hv, ha]
        have hsub : q.1.val - (n - h) = r.val := by dsimp [r]
        have hidx : (⟨q.1.val - (n - h), by omega⟩ : Fin h) = r := by
          apply Fin.ext
          exact hsub
        change v q.1 = z q
        rw [hz]
        dsimp [z]
        rw [dif_neg hpre, hidx]
  have hfilter :
      (Finset.univ.filter fun v : Pos T k =>
        v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ internalBits i hle v = a) =
      (evenRoleSet n).filter fun v => ∀ q : S, v q.1 = z q := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, evenRoleSet]
    rw [hagree]
    tauto
  rw [hfilter]
  simpa [n, S] using parity_projection_uniform S hScard z

theorem evenLeafPaletteCardEq
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (hPT : PT.Valid)
    (hfree : ∃ j : Fin (T.S.n k), (PT.tiling.P i).ℓ ≤ j.val ∧
      j.val < T.S.n k - (PT.tiling.P i).h)
    (ψ : PaletteCode i hle) (hψ : Function.Surjective ψ.map) :
    ∀ c₁ c₂ : Fin ψ.dimension → ZMod 2,
      (Finset.univ.filter fun v : Pos T k =>
        v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₁).card =
      (Finset.univ.filter fun v : Pos T k =>
        v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₂).card := by
  classical
  intro c₁ c₂
  let R : Finset (Pos T k) := Finset.univ.filter fun v =>
    v ∈ PT.tiling.leaf i ∧ IsEvenRole v
  let bits : Pos T k → (Fin (PT.tiling.P i).h → ZMod 2) := internalBits i hle
  let colors (c : Fin ψ.dimension → ZMod 2) :=
    Finset.univ.filter fun a : Fin (PT.tiling.P i).h → ZMod 2 => ψ.map a = c
  let fiber (a : Fin (PT.tiling.P i).h → ZMod 2) :=
    R.filter fun v => bits v = a
  have hfiberConst (a b : Fin (PT.tiling.P i).h → ZMod 2) :
      (fiber a).card = (fiber b).card := by
    rw [show (fiber a).card =
      (Finset.univ.filter fun v : Pos T k =>
        v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ bits v = a).card by
          simp [fiber, R, Finset.filter_filter, and_assoc, and_left_comm, and_comm],
      show (fiber b).card =
      (Finset.univ.filter fun v : Pos T k =>
        v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ bits v = b).card by
          simp [fiber, R, Finset.filter_filter, and_assoc, and_left_comm, and_comm]]
    rw [internalWordEvenFiberCard i hle hPT hfree a,
      internalWordEvenFiberCard i hle hPT hfree b]
  have hgroup (c : Fin ψ.dimension → ZMod 2) :
      (R.filter fun v => ψ.map (bits v) = c).card =
        ∑ a ∈ colors c, (fiber a).card := by
    calc
      _ = (R.filter fun v => bits v ∈ colors c).card := by
        congr 1
        ext v
        simp [colors]
      _ = _ := (Finset.sum_card_fiberwise_eq_card_filter R (colors c) bits).symm
  have hcolors (c : Fin ψ.dimension → ZMod 2) :
      (R.filter fun v => ψ.map (bits v) = c).card =
        (colors c).card * (fiber (0 : Fin (PT.tiling.P i).h → ZMod 2)).card := by
    rw [hgroup c]
    calc
      _ = ∑ a ∈ colors c,
          (fiber (0 : Fin (PT.tiling.P i).h → ZMod 2)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hfiberConst a 0
      _ = _ := Finset.sum_const_nat (fun _ _ => rfl)
  have hcard : (colors c₁).card = (colors c₂).card := by
    calc
      _ = Fintype.card {a : Fin (PT.tiling.P i).h → ZMod 2 // ψ.map a = c₁} :=
        (Fintype.card_subtype (fun a : Fin (PT.tiling.P i).h → ZMod 2 => ψ.map a = c₁)).symm
      _ = Fintype.card {a : Fin (PT.tiling.P i).h → ZMod 2 // ψ.map a = c₂} :=
        linearFiberCardEq (PT.tiling.P i).h ψ.dimension ψ.map hψ c₁ c₂
      _ = (colors c₂).card :=
        Fintype.card_subtype (fun a : Fin (PT.tiling.P i).h → ZMod 2 => ψ.map a = c₂)
  have hR₁ : (R.filter fun v => ψ.roleColour v = c₁).card =
      (R.filter fun v => ψ.map (bits v) = c₁).card := by rfl
  have hR₂ : (R.filter fun v => ψ.roleColour v = c₂).card =
      (R.filter fun v => ψ.map (bits v) = c₂).card := by rfl
  rw [show (Finset.univ.filter fun v : Pos T k =>
      v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₁) =
        R.filter fun v => ψ.roleColour v = c₁ by
          ext v; simp [R, Finset.filter_filter, and_assoc, and_left_comm, and_comm],
    show (Finset.univ.filter fun v : Pos T k =>
      v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₂) =
        R.filter fun v => ψ.roleColour v = c₂ by
          ext v; simp [R, Finset.filter_filter, and_assoc, and_left_comm, and_comm]]
  rw [hR₁, hR₂, hcolors c₁, hcolors c₂, hcard]

theorem syndrome_flipPos
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (G : LowGeom PT) (v : Pos T k) (j : Fin (T.S.n k)) :
    G.syndrome (flipPos v j) = G.syndrome v + G.ids j := by
  classical
  unfold LowGeom.syndrome
  have hterms (l : Fin (T.S.n k)) :
      (if flipPos v j l then G.ids l else 0) =
        (if v l then G.ids l else 0) + (if l = j then G.ids j else 0) := by
    by_cases hlj : l = j
    · subst l
      cases hv : v j <;> simp [flipPos, hv, ZModModule.add_self]
    · simp [flipPos, Function.update_of_ne hlj, hlj]
  calc
    (∑ l, if flipPos v j l then G.ids l else 0) =
        ∑ l, ((if v l then G.ids l else 0) +
          (if l = j then G.ids j else 0)) := by
            apply Finset.sum_congr rfl
            intro l hl
            exact hterms l
    _ = (∑ l, if v l then G.ids l else 0) + G.ids j := by
      rw [Finset.sum_add_distrib]
      simp

theorem lateNeighborCount_le_r
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (K : ℝ) (hG : D.S17GeometryValidity K)
    (v : Pos T k) :
    (Finset.univ.filter fun j : Fin (T.S.n k) =>
      (D.G.classOf (flipPos v j)).isSome).card ≤ D.G.r := by
  classical
  let Late : Finset (Fin (T.S.n k)) := Finset.univ.filter fun j =>
    (D.G.classOf (flipPos v j)).isSome
  let f : {j // j ∈ Late} → Fin D.G.r := fun j =>
    (D.G.classOf (flipPos v j.1)).get (by
      simpa [Late] using (Finset.mem_filter.mp j.2).2)
  have hf : Function.Injective f := by
    intro j j' hfj
    have hjlate : (D.G.classOf (flipPos v j.1)).isSome := by
      simpa [Late] using (Finset.mem_filter.mp j.2).2
    have hj'late : (D.G.classOf (flipPos v j'.1)).isSome := by
      simpa [Late] using (Finset.mem_filter.mp j'.2).2
    have hget : D.G.classOf (flipPos v j.1) = some (f j) :=
      (Option.coe_get hjlate).symm
    have hget' : D.G.classOf (flipPos v j'.1) = some (f j') :=
      (Option.coe_get hj'late).symm
    have hcond : ¬ IsEvenRole (flipPos v j.1) ∧
        D.G.syndrome (flipPos v j.1) ∈ D.G.Lsub := by
      by_contra hn
      have hnone : D.G.classOf (flipPos v j.1) = none := by
        simp [LowGeom.classOf, hn]
      rw [hnone] at hget
      cases hget
    have hcond' : ¬ IsEvenRole (flipPos v j'.1) ∧
        D.G.syndrome (flipPos v j'.1) ∈ D.G.Lsub := by
      by_contra hn
      have hnone : D.G.classOf (flipPos v j'.1) = none := by
        simp [LowGeom.classOf, hn]
      rw [hnone] at hget'
      cases hget'
    have hidx : D.G.classEnum.symm ⟨D.G.syndrome (flipPos v j.1), hcond.2⟩ = f j :=
      Option.some.inj (by simpa [LowGeom.classOf, hcond] using hget)
    have hidx' : D.G.classEnum.symm ⟨D.G.syndrome (flipPos v j'.1), hcond'.2⟩ = f j' :=
      Option.some.inj (by simpa [LowGeom.classOf, hcond'] using hget')
    have hmap : (D.G.classEnum (f j)).1 = D.G.syndrome (flipPos v j.1) := by
      rw [← hidx]
      simp
    have hmap' : (D.G.classEnum (f j')).1 = D.G.syndrome (flipPos v j'.1) := by
      rw [← hidx']
      simp
    have hsynd : D.G.syndrome (flipPos v j.1) = D.G.syndrome (flipPos v j'.1) := by
      calc
        _ = (D.G.classEnum (f j)).1 := hmap.symm
        _ = (D.G.classEnum (f j')).1 := congrArg (fun t => (D.G.classEnum t).1) hfj
        _ = _ := hmap'
    rw [syndrome_flipPos D.G v j.1, syndrome_flipPos D.G v j'.1] at hsynd
    have hids : D.G.ids j.1 = D.G.ids j'.1 := add_left_cancel hsynd
    exact Subtype.ext (hG.ids_injective hids)
  have hcard : Fintype.card {j // j ∈ Late} ≤ Fintype.card (Fin D.G.r) :=
    Fintype.card_le_of_injective f hf
  have hlate : Late.card = Fintype.card {j // j ∈ Late} := by simp
  change Late.card ≤ D.G.r
  rw [hlate]
  simpa using hcard

theorem externalEarlyCoordCount
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (K : ℝ)
    (hPT : PT.Valid) (hG : D.S17GeometryValidity K)
    (v : Pos T k) (heven : IsEvenRole v) :
    (D.externalEarly v).card + (PT.tiling.P (D.G.patchOf v)).h +
      (Finset.univ.filter fun j : Fin (T.S.n k) =>
        (D.G.classOf (flipPos v j)).isSome).card ≤ T.S.n k + 1 := by
  classical
  let n := T.S.n k
  let i := D.G.patchOf v
  let h := (PT.tiling.P i).h
  let I : Finset (Fin n) := PT.tiling.Icoord i
  let Late : Finset (Fin n) := Finset.univ.filter fun j =>
    (D.G.classOf (flipPos v j)).isSome
  let EarlyCoords : Finset (Fin n) := Finset.univ.filter fun j =>
    j ∉ I ∧ D.G.classOf (flipPos v j) = none
  let flip : Fin n → Pos T k := fun j => flipPos v j
  have hEll : (PT.tiling.P i).ℓ ≤
      Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ := by
    exact Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) (Finset.mem_univ i)
  have hHsup : h ≤ Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h := by
    dsimp [h]
    exact Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
  have hglobal := hPT.tiling_valid.prefix_internal_length
  change (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) +
      (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h) ≤ n at hglobal
  have hfit : h ≤ n := by dsimp [h]; omega
  let topMap : Fin h → Fin n := fun j => ⟨n - h + j.val, by omega⟩
  have htopEq : I = Finset.univ.image topMap := by
    ext j
    dsimp [I, Tiling.Icoord, topCoordinates]
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hj
      let a : Fin h := ⟨j.val - (n - h), by omega⟩
      refine ⟨a, ?_⟩
      apply Fin.ext
      dsimp [topMap, a]
      omega
    · rintro ⟨a, haEq⟩
      have hv := congrArg Fin.val haEq
      dsimp [topMap] at hv
      omega
  have htopInj : Function.Injective topMap := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp [topMap] at hv
    omega
  have hIcard : I.card = h := by
    rw [htopEq, Finset.card_image_of_injective _ htopInj]
    simp [Fintype.card_fin]
  have hflipInj : Function.Injective flip := by
    intro j j' hjj'
    by_contra hne
    have hcoord := congrFun hjj' j
    change flipPos v j j = flipPos v j' j at hcoord
    have hleft : flipPos v j j = !v j := by simp [flipPos]
    have hright : flipPos v j' j = v j := by
      change Function.update v j' (!v j') j = v j
      exact Function.update_of_ne hne _ _
    rw [hleft, hright] at hcoord
    cases hv : v j <;> simp [hv] at hcoord
  have hImage : D.externalEarly v = EarlyCoords.image flip := by
    ext w
    simp only [ListGateContext.externalEarly, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_image, EarlyCoords, flip, I, Tiling.Icoord, topCoordinates]
    constructor
    · rintro ⟨hclass, j, hjnotI, rfl⟩
      exact ⟨j, ⟨hjnotI, hclass⟩, rfl⟩
    · rintro ⟨j, ⟨hjnotI, hclass⟩, rfl⟩
      exact ⟨hclass, j, hjnotI, rfl⟩
  have hEarlySubset : EarlyCoords ⊆ Finset.univ \ (I ∪ Late) := by
    intro j hj
    rcases (Finset.mem_filter.mp hj).2 with ⟨hjnotI, hjclass⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hjUnion
    rcases Finset.mem_union.mp hjUnion with hjI | hjLate
    · exact hjnotI hjI
    · have hsome : (D.G.classOf (flipPos v j)).isSome :=
        (Finset.mem_filter.mp hjLate).2
      rw [hjclass] at hsome
      simp at hsome
  have hComplement : EarlyCoords.card ≤ n - (I ∪ Late).card := by
    calc
      _ ≤ (Finset.univ \ (I ∪ Late)).card := Finset.card_le_card hEarlySubset
      _ = n - (I ∪ Late).card := by
        simp [Finset.card_sdiff_of_subset (Finset.subset_univ _), Fintype.card_fin]
  have hIntSet : I.filter (fun j => (D.G.classOf (flipPos v j)).isSome) = I ∩ Late := by
    ext j
    simp [Late]
  have hIntLate : (I ∩ Late).card ≤ 1 := by
    rw [← hIntSet]
    simpa [I] using hG.internal_late_count v heven
  have hUnion : I.card + Late.card ≤ (I ∪ Late).card + 1 := by
    have hcard := Finset.card_union_add_card_inter I Late
    omega
  have hExtCard : (D.externalEarly v).card = EarlyCoords.card := by
    rw [hImage, Finset.card_image_of_injective _ hflipInj]
  rw [hExtCard]
  change EarlyCoords.card + h + Late.card ≤ n + 1
  rw [← hIcard]
  calc
    EarlyCoords.card + I.card + Late.card = EarlyCoords.card + (I.card + Late.card) := by omega
    _ ≤ EarlyCoords.card + ((I ∪ Late).card + 1) :=
      Nat.add_le_add_left hUnion EarlyCoords.card
    _ ≤ (n - (I ∪ Late).card) + ((I ∪ Late).card + 1) :=
      Nat.add_le_add_right hComplement ((I ∪ Late).card + 1)
    _ = n + 1 := by
      have hUle : (I ∪ Late).card ≤ n := by
        have h := Finset.card_le_card (Finset.subset_univ (I ∪ Late))
        simpa [Finset.card_univ, Fintype.card_fin] using h
      omega

theorem externalEarly_crossPatch_card_le_prefix
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (hPT : PT.Valid)
    (v : Pos T k) :
    ((D.externalEarly v).filter fun w =>
      D.G.patchOf w ≠ D.G.patchOf v).card ≤
        (PT.tiling.P (D.G.patchOf v)).ℓ := by
  classical
  let i := D.G.patchOf v
  let ell := (PT.tiling.P i).ℓ
  let Prefix : Finset (Fin (T.S.n k)) := Finset.univ.filter fun j => j.val < ell
  let Cross : Finset (Pos T k) := (D.externalEarly v).filter fun w => D.G.patchOf w ≠ i
  have hsub : Cross ⊆ Prefix.image (flipPos v) := by
    intro w hw
    rcases (Finset.mem_filter.mp hw) with ⟨hwext, hcross⟩
    rcases (Finset.mem_filter.mp hwext).2 with ⟨hclass, j, hjnotI, rfl⟩
    have hjlt : j.val < ell := by
      by_contra hjnot
      have hvleaf : v ∈ PT.tiling.leaf i := by
        dsimp [i]
        exact D.G.patchOf_leaf v
      have hwleaf : flipPos v j ∈ PT.tiling.leaf i := by
        simp only [Tiling.leaf, prefixLeaf, Set.mem_setOf_eq] at hvleaf ⊢
        intro l hl
        have hne : l ≠ j := by
          intro heq
          subst l
          omega
        simpa [flipPos, hne] using hvleaf l hl
      obtain ⟨p, hp, huniq⟩ := hPT.tiling_valid.prefix_complete (flipPos v j)
      have hi : i = p := huniq i hwleaf
      have hpatch : D.G.patchOf (flipPos v j) = p :=
        huniq _ (D.G.patchOf_leaf (flipPos v j))
      have hsame : D.G.patchOf (flipPos v j) = i := hpatch.trans hi.symm
      exact hcross hsame
    apply Finset.mem_image.mpr
    exact ⟨j, by simp [Prefix, hjlt], rfl⟩
  have hPrefix : Prefix.card ≤ ell := by
    let f : {j // j ∈ Prefix} → Fin ell := fun j =>
      ⟨j.1.val, (Finset.mem_filter.mp j.2).2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Fin.ext
      simpa [f] using congrArg Fin.val hab
    have hcard : Fintype.card {j // j ∈ Prefix} = Prefix.card := by simp
    calc
      Prefix.card = Fintype.card {j // j ∈ Prefix} := hcard.symm
      _ ≤ Fintype.card (Fin ell) := Fintype.card_le_of_injective f hf
      _ = ell := Fintype.card_fin ell
  change Cross.card ≤ ell
  calc
    Cross.card ≤ (Prefix.image (flipPos v)).card := Finset.card_le_card hsub
    _ ≤ Prefix.card := Finset.card_image_le
    _ ≤ ell := hPrefix

theorem patchOf_flip_eq_of_prefix
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (hPT : PT.Valid)
    (v : Pos T k) (i : Fin PT.tiling.m) (hleaf : v ∈ PT.tiling.leaf i)
    (j : Fin (T.S.n k))
    (hj : (PT.tiling.P i).ℓ ≤ j.val) :
    D.G.patchOf (flipPos v j) = i := by
  have hflipLeaf : flipPos v j ∈ PT.tiling.leaf i := by
    simp only [Tiling.leaf, prefixLeaf, Set.mem_setOf_eq] at hleaf ⊢
    intro l hl
    have hne : l ≠ j := by
      intro heq
      subst l
      omega
    simpa [flipPos, hne] using hleaf l hl
  obtain ⟨p, hp, huniq⟩ := hPT.tiling_valid.prefix_complete (flipPos v j)
  have hi : i = p := huniq i hflipLeaf
  have hpatch : D.G.patchOf (flipPos v j) = p :=
    huniq _ (D.G.patchOf_leaf (flipPos v j))
  exact hpatch.trans hi.symm

theorem samePatchExternalEarly_card_lower
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (hPT : PT.Valid)
    (v : Pos T k) :
    T.S.n k - (PT.tiling.P (D.G.patchOf v)).h -
        (PT.tiling.P (D.G.patchOf v)).ℓ -
        (Finset.univ.filter fun j : Fin (T.S.n k) =>
          (D.G.classOf (flipPos v j)).isSome).card ≤
      ((D.externalEarly v).filter fun w =>
        D.G.patchOf w = D.G.patchOf v).card := by
  classical
  let n := T.S.n k
  let i := D.G.patchOf v
  let ell := (PT.tiling.P i).ℓ
  let h := (PT.tiling.P i).h
  let Late : Finset (Fin n) := Finset.univ.filter fun j =>
    (D.G.classOf (flipPos v j)).isSome
  let Middle : Finset (Fin n) := Finset.univ.filter fun j =>
    ell ≤ j.val ∧ j.val < n - h
  let OwnCoords : Finset (Fin n) := Middle.filter fun j =>
    (D.G.classOf (flipPos v j)).isNone
  let OwnPos : Finset (Pos T k) := (D.externalEarly v).filter fun w =>
    D.G.patchOf w = i
  have hEll : ell ≤ Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ := by
    dsimp [ell]
    exact Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) (Finset.mem_univ i)
  have hH : h ≤ Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h := by
    dsimp [h]
    exact Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
  have hglobal := hPT.tiling_valid.prefix_internal_length
  change (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) +
      (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h) ≤ n at hglobal
  have hfit : ell + h ≤ n := by omega
  let A : Fin (n - h - ell) → Fin n := fun q => ⟨ell + q.val, by
    have hq := q.isLt
    omega⟩
  have hAinj : Function.Injective A := by
    intro q q' hqq'
    apply Fin.ext
    have hv := congrArg Fin.val hqq'
    dsimp [A] at hv
    omega
  have hAimage : (Finset.univ.image A) ⊆ Middle := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨a, ha, rfl⟩
    simp only [Middle, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · simp [A]
    · have hlt := a.isLt
      dsimp [A]
      omega
  have hMiddle : n - h - ell ≤ Middle.card := by
    have hAcard : (Finset.univ.image A).card = n - h - ell := by
      rw [Finset.card_image_of_injective _ hAinj]
      simp
    calc
      n - h - ell = (Finset.univ.image A).card := hAcard.symm
      _ ≤ Middle.card := Finset.card_le_card hAimage
  have hpartition :
      (Middle.filter fun j => (D.G.classOf (flipPos v j)).isSome).card +
        (Middle.filter fun j => ¬ (D.G.classOf (flipPos v j)).isSome).card =
          Middle.card := by
    exact Finset.card_filter_add_card_filter_not
      (s := Middle) (fun j => (D.G.classOf (flipPos v j)).isSome)
  have hownEq : (Middle.filter fun j => ¬ (D.G.classOf (flipPos v j)).isSome) =
      OwnCoords := by
    ext j
    simp [OwnCoords]
  have hlateSubset :
      Middle.filter (fun j => (D.G.classOf (flipPos v j)).isSome) ⊆ Late := by
    intro j hj
    simpa [Late] using (Finset.mem_filter.mp hj).2
  have hlateCard :
      (Middle.filter fun j => (D.G.classOf (flipPos v j)).isSome).card ≤ Late.card :=
    Finset.card_le_card hlateSubset
  have hownLower : n - h - ell - Late.card ≤ OwnCoords.card := by
    have hsum : n - h - ell ≤
        (Middle.filter fun j => (D.G.classOf (flipPos v j)).isSome).card +
          OwnCoords.card := by
      rw [← hownEq, hpartition]
      exact hMiddle
    omega
  have hflipInj : Function.Injective (flipPos v) := by
    intro j j' hjj'
    by_contra hne
    have hcoord := congrFun hjj' j
    change flipPos v j j = flipPos v j' j at hcoord
    have hleft : flipPos v j j = !v j := by simp [flipPos]
    have hright : flipPos v j' j = v j := by
      change Function.update v j' (!v j') j = v j
      exact Function.update_of_ne hne _ _
    rw [hleft, hright] at hcoord
    cases hv : v j <;> simp [hv] at hcoord
  have himage : OwnCoords.image (flipPos v) ⊆ OwnPos := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
    have hjMiddle := (Finset.mem_filter.mp hj).1
    have hjcoords : ell ≤ j.val ∧ j.val < n - h :=
      (Finset.mem_filter.mp hjMiddle).2
    have hjNone := (Finset.mem_filter.mp hj).2
    have hjNone' : D.G.classOf (flipPos v j) = none :=
      Option.isNone_iff_eq_none.mp hjNone
    have hjnotI : j ∉ PT.tiling.Icoord i := by
      simp only [Tiling.Icoord, topCoordinates, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega
    have hpatch := patchOf_flip_eq_of_prefix D hPT v i
      (D.G.patchOf_leaf v) j hjcoords.1
    apply Finset.mem_filter.mpr
    refine ⟨?_, hpatch⟩
    change flipPos v j ∈ Finset.univ.filter fun w =>
      D.G.classOf w = none ∧ ∃ l : Fin n,
        l ∉ PT.tiling.Icoord (D.G.patchOf v) ∧ w = flipPos v l
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hjNone', ?_⟩
    exact ⟨j, hjnotI, rfl⟩
  have hflipCard : (OwnCoords.image (flipPos v)).card = OwnCoords.card := by
    rw [Finset.card_image_of_injective _ hflipInj]
  change n - h - ell - Late.card ≤ OwnPos.card
  calc
    n - h - ell - Late.card ≤ OwnCoords.card := hownLower
    _ = (OwnCoords.image (flipPos v)).card := hflipCard.symm
    _ ≤ OwnPos.card := Finset.card_le_card himage

theorem hitRatio_nonneg
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (w : Pos T k)
    (x y : Fin (T.S.N k))
    (hdeg : 0 ≤ deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x) :
    0 ≤ D.hitRatio w x y := by
  unfold ListGateContext.hitRatio hit
  split_ifs
  · exact div_nonneg (by norm_num) hdeg
  · norm_num

theorem hitRatio_le_of_inv
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (w : Pos T k)
    (x y : Fin (T.S.N k)) (B : ℝ)
    (hdeg : 0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x)
    (hinv : 1 / deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ≤ B) :
    D.hitRatio w x y ≤ B := by
  unfold ListGateContext.hitRatio
  have hB : 0 ≤ B := le_trans (by positivity) hinv
  by_cases hy : Hits (T.S.E k) PT.tiling.c x y
  · simpa [hit, hy] using hinv
  · simp [hit, hy, hB]

theorem cleanInitialPrior_cluster_cap
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (hcluster : PT.tiling.mode.isCluster) (x : Fin (T.S.N k)) :
    (T.S.N k : ℝ) * σ x ≤
      2 ^ (PT.tiling.P (D.G.patchOf v)).h *
        Real.exp (-500 * PT.tiling.gain (D.G.patchOf v)) := by
  rcases hσ with ⟨_, _, a, _, _, hcap, _⟩
  exact hcap hcluster x

theorem activeCorner_subset_envelope
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (hPT : PT.Valid) (i : Fin PT.tiling.m) (a : PT.mesh.V)
    (ha : a ∈ PT.activeVertices) :
    PT.mesh.corner a i ⊆ PT.envelope i := by
  rw [hPT.envelope_eq]
  intro x hx
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨a, ha, hx⟩

theorem cleanInitialPrior_support_envelope
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (hPT : PT.Valid) (D : ListGateContext κ T k PT) (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (x : Fin (T.S.N k)) (hx : σ x ≠ 0) :
    x ∈ PT.envelope (D.G.patchOf v) := by
  rcases hσ with ⟨_, _, a, ha, hsupport, _, _⟩
  exact activeCorner_subset_envelope hPT (D.G.patchOf v) a ha (hsupport x hx)

theorem cleanInitialPrior_noncluster_cap
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (ha : κ.a < 1) (hM : 0 < (PT.tiling.P (D.G.patchOf v)).M)
    (hnoncluster : ¬ PT.tiling.mode.isCluster) (x : Fin (T.S.N k)) :
    σ x ≤ 1 / ((1 - κ.a) * (PT.tiling.P (D.G.patchOf v)).M) := by
  rcases hσ with ⟨_, _, a, haActive, _, _, huniform⟩
  rcases huniform hnoncluster with ⟨hsize, hpoint⟩
  have hfactor : 0 < (1 - κ.a) * (PT.tiling.P (D.G.patchOf v)).M := by
    positivity
  by_cases hx : x ∈ PT.mesh.corner a (D.G.patchOf v)
  · rw [hpoint x, if_pos hx]
    have hcardLower :
        (1 - κ.a) * (PT.tiling.P (D.G.patchOf v)).M ≤
          (PT.mesh.corner a (D.G.patchOf v)).card := hsize
    have hcard : 0 < ((PT.mesh.corner a (D.G.patchOf v)).card : ℝ) :=
      lt_of_lt_of_le hfactor hcardLower
    exact (one_div_le_one_div_of_le hfactor hcardLower)
  · rw [hpoint x, if_neg hx]
    positivity

theorem a_lt_one (κ : CConsts) (hκ : κ.Admissible) : κ.a < 1 := by
  have huNeg : -(10 * (κ.u : ℝ) + 100) < 0 := by
    have huNonneg : 0 ≤ (κ.u : ℝ) := Nat.cast_nonneg _
    linarith
  have hrpow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) huNeg
  have hxiLt : κ.ξ < 1 := by
    have hprodXi : κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < κ.α :=
      by simpa using mul_lt_mul_of_pos_left hrpow hκ.α_rng.1
    linarith [hκ.ξ_rng.2, hκ.α_rng.2]
  have hfour : 1 ≤ (4 : ℝ) ^ (κ.u + 3) :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
  have hden : 1 < 3 * (4 : ℝ) ^ (κ.u + 3) := by nlinarith [hfour]
  have hxiSq : κ.ξ ^ 2 < 1 := by nlinarith [hκ.ξ_rng.1, hxiLt]
  have hquot : κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3)) < 1 := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [hxiSq, hden]
  have hθ : κ.θ < 1 := lt_trans hκ.θ_rng.2 hquot
  rw [hκ.a_eq]
  linarith

theorem finsetProdTwoExpBound {α : Type*} [DecidableEq α]
    (S : Finset α) (f ε : α → ℝ)
    (hf0 : ∀ x ∈ S, 0 ≤ f x)
    (hf : ∀ x ∈ S, f x ≤ 2 * Real.exp (ε x)) :
    (∏ x ∈ S, f x) ≤ (2 : ℝ) ^ S.card * Real.exp (∑ x ∈ S, ε x) := by
  classical
  calc
    _ ≤ ∏ x ∈ S, 2 * Real.exp (ε x) := by
      apply Finset.prod_le_prod₀
      · intro x hx
        exact hf0 x hx
      · intro x hx
        exact hf x hx
    _ = (2 : ℝ) ^ S.card * Real.exp (∑ x ∈ S, ε x) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]

theorem finsetProdExpBound {α : Type*} [DecidableEq α]
    (S : Finset α) (f ε : α → ℝ)
    (hf0 : ∀ x ∈ S, 0 ≤ f x)
    (hf : ∀ x ∈ S, f x ≤ Real.exp (ε x)) :
    (∏ x ∈ S, f x) ≤ Real.exp (∑ x ∈ S, ε x) := by
  classical
  calc
    _ ≤ ∏ x ∈ S, Real.exp (ε x) := by
      apply Finset.prod_le_prod₀
      · intro x hx
        exact hf0 x hx
      · intro x hx
        exact hf x hx
    _ = Real.exp (∑ x ∈ S, ε x) := by rw [← Real.exp_sum]

theorem invHalfSubBound {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 4) :
    (1 / 2 - ε)⁻¹ ≤ 2 * Real.exp (4 * ε) := by
  have hden : 0 < 1 - 2 * ε := by linarith
  have hsmall : (1 - 2 * ε)⁻¹ ≤ 1 + 4 * ε := by
    rw [inv_le_iff_one_le_mul₀ hden]
    nlinarith [hε0, hε1]
  have hexp : 1 + 4 * ε ≤ Real.exp (4 * ε) := by
    simpa [add_comm] using Real.add_one_le_exp (4 * ε)
  have hEq : (1 / 2 - ε)⁻¹ = 2 * (1 - 2 * ε)⁻¹ := by
    field_simp [ne_of_gt hden]
  rw [hEq]
  exact mul_le_mul_of_nonneg_left (hsmall.trans hexp) (by norm_num)

theorem invOneAddBound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x)⁻¹ ≤ Real.exp (-x / 2) := by
  have hsmall : (1 + x)⁻¹ ≤ 1 - x / 2 := by
    apply (inv_le_iff_one_le_mul₀ (by positivity)).2
    nlinarith [hx0, hx1]
  exact hsmall.trans (by simpa [div_eq_mul_inv] using Real.one_sub_le_exp_neg (x / 2))

theorem hitRatio_le_of_degreeNearHalf
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (w : Pos T k)
    (x y : Fin (T.S.N k)) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 4)
    (hdeg : 1 / 2 - ε ≤
      deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x) :
    D.hitRatio w x y ≤ 2 * Real.exp (4 * ε) := by
  have hbase : 0 < 1 / 2 - ε := by linarith
  have hdegpos : 0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x :=
    lt_of_lt_of_le hbase hdeg
  have hinv : 1 / deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ≤
      (1 / 2 - ε)⁻¹ := by simpa [one_div] using one_div_le_one_div_of_le hbase hdeg
  exact hitRatio_le_of_inv D w x y _ hdegpos
    (hinv.trans (invHalfSubBound hε0 hε1))

theorem hitRatio_le_of_degreeAboveHalf
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (w : Pos T k)
    (x y : Fin (T.S.N k)) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (hdeg : 1 / 2 + δ ≤
      deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x) :
    D.hitRatio w x y ≤ 2 * Real.exp (-δ) := by
  have hbase : 0 < 1 / 2 + δ := by positivity
  have hdegpos : 0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x :=
    lt_of_lt_of_le hbase hdeg
  have hinv : 1 / deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ≤
      (1 / 2 + δ)⁻¹ := by simpa [one_div] using one_div_le_one_div_of_le hbase hdeg
  have hform : (1 / 2 + δ)⁻¹ = 2 * (1 + 2 * δ)⁻¹ := by
    field_simp
  have hsmall : (1 + 2 * δ)⁻¹ ≤ Real.exp (-δ) := by
    convert invOneAddBound (x := 2 * δ) (by positivity) (by linarith) using 1 <;> congr 1 <;> ring
  have hbound : (1 / 2 + δ)⁻¹ ≤ 2 * Real.exp (-δ) := by
    rw [hform]
    exact mul_le_mul_of_nonneg_left hsmall (by norm_num)
  exact hitRatio_le_of_inv D w x y _ hdegpos (hinv.trans hbound)

theorem dimNegBstar_le_oneSixteenth {n : ℕ} (hn : 256 ≤ n) :
    Real.rpow (n : ℝ) (-1 + (0.04 : ℝ)) ≤ 1 / 16 := by
  have hnReal : 256 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnOne : 1 ≤ (n : ℝ) := by linarith
  have hExponent : -1 + (0.04 : ℝ) ≤ -(1 / 2 : ℝ) := by norm_num
  have hpow := Real.rpow_le_rpow_of_exponent_le hnOne hExponent
  have hsqrt : (16 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
    change (16 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ)
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    nlinarith [hnReal]
  have hinv : (Real.rpow (n : ℝ) (1 / 2 : ℝ))⁻¹ ≤ (16 : ℝ)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by norm_num : (0 : ℝ) < 16)).2 hsqrt
  have hneg : Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) =
      (Real.rpow (n : ℝ) (1 / 2 : ℝ))⁻¹ :=
    Real.rpow_neg (by positivity) _
  have hsmall : Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) ≤ 1 / 16 := by
    rw [hneg]
    simpa using hinv
  exact le_trans hpow hsmall

theorem log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hpowEq : Real.rpow x (1 / 2 : ℝ) = Real.sqrt x := by
    change x ^ (1 / 2 : ℝ) = Real.sqrt x
    rw [Real.sqrt_eq_rpow]
  calc
    Real.log x ≤ Real.rpow x (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
      Real.log_le_rpow_div hx (by norm_num)
    _ = 2 * Real.sqrt x := by rw [hpowEq]; ring

theorem natPow_two_withLate
    (m n late : ℕ) (h : m + late ≤ n + 1) :
    (2 : ℝ) ^ m ≤ 2 * (2 : ℝ) ^ n * Real.rpow 2 (-(late : ℝ)) := by
  have hcast : (m : ℝ) + late ≤ (n : ℝ) + 1 := by exact_mod_cast h
  have hexp : (m : ℝ) ≤ (n : ℝ) + 1 - late := by linarith
  calc
    (2 : ℝ) ^ m = Real.rpow 2 (m : ℝ) := (Real.rpow_natCast 2 m).symm
    _ ≤ Real.rpow 2 ((n : ℝ) + 1 - late) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 2 * (2 : ℝ) ^ n * Real.rpow 2 (-(late : ℝ)) := by
      change (2 : ℝ) ^ ((n : ℝ) + 1 - late) =
        2 * (2 : ℝ) ^ n * (2 : ℝ) ^ (-(late : ℝ))
      rw [sub_eq_add_neg, Real.rpow_add (x := (2 : ℝ)) (by norm_num),
        Real.rpow_add (x := (2 : ℝ)) (by norm_num),
        Real.rpow_natCast, Real.rpow_one]
      ring

theorem row_le_of_factorBounds
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (ys : Pos T k → Fin (T.S.N k)) (x : Fin (T.S.N k))
    (ε : Pos T k → ℝ) (hσ : 0 ≤ σ x)
    (hFactor0 : ∀ w ∈ D.externalEarly v, 0 ≤ D.hitRatio w x (ys w))
    (hFactor : ∀ w ∈ D.externalEarly v,
      D.hitRatio w x (ys w) ≤ 2 * Real.exp (ε w)) :
    D.row v σ ys x ≤ σ x * (2 : ℝ) ^ (D.externalEarly v).card *
      Real.exp (∑ w ∈ D.externalEarly v, ε w) := by
  rw [ListGateContext.row]
  have hprod := finsetProdTwoExpBound (D.externalEarly v)
    (fun w => D.hitRatio w x (ys w)) ε hFactor0 hFactor
  calc
    _ ≤ σ x * ((2 : ℝ) ^ (D.externalEarly v).card *
        Real.exp (∑ w ∈ D.externalEarly v, ε w)) := mul_le_mul_of_nonneg_left hprod hσ
    _ = σ x * (2 : ℝ) ^ (D.externalEarly v).card *
        Real.exp (∑ w ∈ D.externalEarly v, ε w) := by ring

theorem row_le_scaled_of_factors
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (ys : Pos T k → Fin (T.S.N k))
    (x : Fin (T.S.N k)) (ε : Pos T k → ℝ)
    (A B gain E : ℝ) (hInternal late : ℕ)
    (hA : 0 ≤ A) (hσ0 : 0 ≤ σ x)
    (hσ : σ x ≤ A * (2 : ℝ) ^ hInternal *
      Real.exp (-B * gain) / T.S.N k)
    (hFactor0 : ∀ w ∈ D.externalEarly v,
      0 ≤ D.hitRatio w x (ys w))
    (hFactor : ∀ w ∈ D.externalEarly v,
      D.hitRatio w x (ys w) ≤ 2 * Real.exp (ε w))
    (hE : (∑ w ∈ D.externalEarly v, ε w) ≤ E)
    (hcount : (D.externalEarly v).card + hInternal + late ≤ T.S.n k + 1) :
    D.row v σ ys x ≤
      2 * A * (2 : ℝ) ^ T.S.n k / T.S.N k *
        Real.exp (E - B * gain) * Real.rpow 2 (-(late : ℝ)) := by
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hrow := row_le_of_factorBounds D v σ ys x ε hσ0 hFactor0 hFactor
  have hsum :
      σ x * (2 : ℝ) ^ (D.externalEarly v).card *
        Real.exp (∑ w ∈ D.externalEarly v, ε w) ≤
      σ x * (2 : ℝ) ^ (D.externalEarly v).card * Real.exp E := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE)
    positivity
  have hbase :
      σ x * (2 : ℝ) ^ (D.externalEarly v).card ≤
        (A * (2 : ℝ) ^ hInternal * Real.exp (-B * gain) / T.S.N k) *
          (2 : ℝ) ^ (D.externalEarly v).card :=
    mul_le_mul_of_nonneg_right hσ (by positivity)
  have hpowEq : (2 : ℝ) ^ hInternal * (2 : ℝ) ^ (D.externalEarly v).card =
      (2 : ℝ) ^ ((D.externalEarly v).card + hInternal) := by
    calc
      _ = (2 : ℝ) ^ (D.externalEarly v).card * (2 : ℝ) ^ hInternal := by ring
      _ = (2 : ℝ) ^ ((D.externalEarly v).card + hInternal) := (pow_add _ _ _).symm
  have hexpEq : Real.exp (-B * gain) * Real.exp E = Real.exp (E - B * gain) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow := natPow_two_withLate ((D.externalEarly v).card + hInternal)
    (T.S.n k) late hcount
  have hnum :
      A * (2 : ℝ) ^ ((D.externalEarly v).card + hInternal) *
        Real.exp (E - B * gain) ≤
      A * (2 * (2 : ℝ) ^ T.S.n k * Real.rpow 2 (-(late : ℝ))) *
        Real.exp (E - B * gain) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hA) (Real.exp_pos _).le
  calc
    D.row v σ ys x ≤
        σ x * (2 : ℝ) ^ (D.externalEarly v).card *
          Real.exp (∑ w ∈ D.externalEarly v, ε w) := hrow
    _ ≤ σ x * (2 : ℝ) ^ (D.externalEarly v).card * Real.exp E := hsum
    _ ≤ (A * (2 : ℝ) ^ hInternal * Real.exp (-B * gain) / T.S.N k) *
          (2 : ℝ) ^ (D.externalEarly v).card * Real.exp E := by
      exact mul_le_mul_of_nonneg_right hbase (Real.exp_pos E).le
    _ = A * (2 : ℝ) ^ ((D.externalEarly v).card + hInternal) *
          Real.exp (E - B * gain) / T.S.N k := by
      rw [← hpowEq, ← hexpEq]
      ring
    _ ≤ A * (2 * (2 : ℝ) ^ T.S.n k * Real.rpow 2 (-(late : ℝ))) *
          Real.exp (E - B * gain) / T.S.N k := by
      apply (div_le_div_iff₀ hN hN).2
      exact mul_le_mul_of_nonneg_right hnum hN.le
    _ = 2 * A * (2 : ℝ) ^ T.S.n k / T.S.N k *
          Real.exp (E - B * gain) * Real.rpow 2 (-(late : ℝ)) := by ring

theorem finProb_pr_finiteUnion_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FinProb Ω) (s : Finset ι) (bad : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ s, bad i ω) ≤ ∑ i ∈ s, P.pr (bad i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert a s ha ih =>
      have hpred : (fun ω => ∃ i ∈ insert a s, bad i ω) =
          (fun ω => bad a ω ∨ ∃ i ∈ s, bad i ω) := by
        funext ω
        simp [ha]
      rw [hpred]
      calc
        _ ≤ P.pr (bad a) + P.pr (fun ω => ∃ i ∈ s, bad i ω) :=
          FinProb.pr_union_le P (bad a) (fun ω => ∃ i ∈ s, bad i ω)
        _ ≤ P.pr (bad a) + ∑ i ∈ s, P.pr (bad i) :=
          add_le_add le_rfl ih
        _ = ∑ i ∈ insert a s, P.pr (bad i) := by simp [ha]

theorem finProb_exists_avoiding_finiteUnion {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FinProb Ω) (s : Finset ι) (bad : ι → Ω → Prop)
    (hbad : (∑ i ∈ s, P.pr (bad i)) < 1) :
    ∃ ω, ∀ i ∈ s, ¬ bad i ω := by
  classical
  by_contra hnone
  have hall : ∀ ω, ∃ i ∈ s, bad i ω := by
    intro ω
    by_contra hω
    have hgood : ∀ i ∈ s, ¬ bad i ω := by
      simpa only [not_exists, not_and] using hω
    exact hnone ⟨ω, hgood⟩
  have hprob : P.pr (fun ω => ∃ i ∈ s, bad i ω) = 1 := by
    unfold FinProb.pr
    simp_rw [hall]
    exact P.sum_eq_one
  have hle := finProb_pr_finiteUnion_le P s bad
  linarith

theorem finProb_exists_avoiding_tests {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FinProb Ω) (tests : Finset ι) (bad : ι → Ω → Prop) (ε : ℝ)
    (htail : ∀ i ∈ tests, P.pr (bad i) ≤ ε)
    (hcount : (tests.card : ℝ) * ε < 1) :
    ∃ ω, ∀ i ∈ tests, ¬ bad i ω := by
  apply finProb_exists_avoiding_finiteUnion P tests bad
  apply lt_of_le_of_lt ?_ hcount
  calc
    (∑ i ∈ tests, P.pr (bad i)) ≤ ∑ i ∈ tests, ε := by
      apply Finset.sum_le_sum
      intro i hi
      exact htail i hi
    _ = (tests.card : ℝ) * ε := by simp [Finset.sum_const, nsmul_eq_mul]

theorem finProb_uniform_singleton_expect {Color : Type*} [Fintype Color]
    [DecidableEq Color] [Nonempty Color] (c : Color) :
    (FinProb.uniform (Finset.univ : Finset Color) Finset.univ_nonempty).expect
      (fun d => if d = c then (1 : ℝ) else 0) = 1 / (Fintype.card Color : ℝ) := by
  classical
  simp [FinProb.expect, FinProb.uniform]

theorem four_hit_corr_identity {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (π : FinProb (Fin N)) (x z : Fin N) :
    4 * (∑ y, π.w y * hit E c x y * hit E c z y) =
      2 * deg E c π.w x + 2 * deg E c π.w z - 1 + corr E c π.w x z := by
  have hpoint (y : Fin N) :
      4 * π.w y * hit E c x y * hit E c z y =
        2 * π.w y * hit E c x y + 2 * π.w y * hit E c z y - π.w y +
          π.w y * fv E c x y * fv E c z y := by
    simp only [fv]
    ring
  calc
    4 * (∑ y, π.w y * hit E c x y * hit E c z y) =
        ∑ y, 4 * π.w y * hit E c x y * hit E c z y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ y, (2 * π.w y * hit E c x y + 2 * π.w y * hit E c z y -
          π.w y + π.w y * fv E c x y * fv E c z y) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hpoint y
    _ = 2 * deg E c π.w x + 2 * deg E c π.w z - 1 + corr E c π.w x z := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp [deg, corr, π.sum_eq_one, Finset.mul_sum]
      <;> ring

theorem pairRatio_formula {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (π : FinProb (Fin N)) (x z : Fin N)
    (hDx : 0 < deg E c π.w x) (hDz : 0 < deg E c π.w z) :
    (∑ y, π.w y * hit E c x y * hit E c z y) /
        (deg E c π.w x * deg E c π.w z) =
      1 + (corr E c π.w x z -
        (2 * deg E c π.w x - 1) * (2 * deg E c π.w z - 1)) /
        (4 * deg E c π.w x * deg E c π.w z) := by
  have hid := four_hit_corr_identity E c π x z
  field_simp [ne_of_gt hDx, ne_of_gt hDz]
  nlinarith [hid]

theorem uniform_pair_expect {N : ℕ} (X : Finset (Fin N)) (hX : X.Nonempty)
    (g : Fin N → Fin N → ℝ) :
    (FinLaw.pi fun _ : Fin 2 => FinLaw.uniform X hX).E
        (fun ω => g (ω 0) (ω 1)) =
      (∑ x ∈ X, ∑ z ∈ X, g x z) / (X.card : ℝ) ^ 2 := by
  classical
  let e : (Fin 2 → Fin N) ≃ (Fin N × Fin N) := {
    toFun := fun ω => (ω 0, ω 1)
    invFun := fun p i => if i.val = 0 then p.1 else p.2
    left_inv := by
      intro ω
      funext i
      fin_cases i <;> rfl
    right_inv := by
      intro p
      cases p
      rfl
  }
  change (∑ ω : Fin 2 → Fin N,
      (∏ i, (FinLaw.uniform X hX).w (ω i)) * g (ω 0) (ω 1)) = _
  rw [← Equiv.sum_comp e.symm
    (fun ω : Fin 2 → Fin N =>
      (∏ i, (FinLaw.uniform X hX).w (ω i)) * g (ω 0) (ω 1))]
  rw [Fintype.sum_prod_type]
  simp [FinLaw.uniform, Finset.sum_mul, e, Finset.mul_sum]
  have hcard : (X.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hX).ne'
  have hcoef : (X.card : ℝ)⁻¹ * (X.card : ℝ)⁻¹ =
      ((X.card : ℝ) ^ 2)⁻¹ := by
    field_simp [hcard]
    <;> ring
  calc
    _ = ∑ x ∈ X, ((X.card : ℝ) ^ 2)⁻¹ * ∑ z ∈ X, g x z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hcoef, ← Finset.mul_sum]
    _ = ((X.card : ℝ) ^ 2)⁻¹ * ∑ x ∈ X, ∑ z ∈ X, g x z := by
      rw [← Finset.mul_sum]
    _ = (∑ x ∈ X, ∑ z ∈ X, g x z) / (X.card : ℝ) ^ 2 := by
      rw [div_eq_mul_inv]
      ring

theorem uniform_colour_weight_lower_tail {I Color : Type*} [Fintype I]
    [DecidableEq I] [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (w : I → ℝ) (W : ℝ) (c : Color)
    (hw0 : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) (hW : 0 < W) :
    (FinProb.pi (fun _ : I =>
      FinProb.uniform (Finset.univ : Finset Color) Finset.univ_nonempty)).pr
      (fun ω => (∑ i, if ω i = c then w i else 0) ≤
        (∑ i, w i) / (2 * (Fintype.card Color : ℝ))) ≤
      Real.exp (-((∑ i, w i) / (8 * W * (Fintype.card Color : ℝ)))) := by
  classical
  let U : I → FinProb Color := fun _ =>
    FinProb.uniform (Finset.univ : Finset Color) Finset.univ_nonempty
  let X : ∀ i : I, Color → ℝ := fun i d => if d = c then w i / W else 0
  have hX : ∀ i d, 0 ≤ X i d ∧ X i d ≤ 1 := by
    intro i d
    by_cases h : d = c
    · simp [X, h]
      exact ⟨div_nonneg (hw0 i) hW.le,
        (div_le_one₀ hW).2 (hwW i)⟩
    · simp [X, h]
  have hlocal (i : I) : (U i).expect (X i) = w i / (W * (Fintype.card Color : ℝ)) := by
    have hpoint : (fun d : Color => X i d) =
        (fun d => (w i / W) * (if d = c then (1 : ℝ) else 0)) := by
      funext d
      by_cases h : d = c <;> simp [X, h]
    change (U i).expect (fun d => X i d) = _
    rw [hpoint]
    simp [FinProb.expect, U, FinProb.uniform, Finset.sum_ite_eq', eq_comm]
    have hcard : (Fintype.card Color : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty Color›).ne'
    field_simp [ne_of_gt hW, hcard]
    <;> ring
  have hmean : (∑ i, (U i).expect (X i)) =
      (∑ i, w i) / (W * (Fintype.card Color : ℝ)) := by
    simp_rw [hlocal]
    rw [← Finset.sum_div]
  have hsum (ω : I → Color) :
      (∑ i, if ω i = c then w i else 0) / W = ∑ i, X i (ω i) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : ω i = c <;> simp [X, h]
  have hinclude (ω : I → Color)
      (hbad : (∑ i, if ω i = c then w i else 0) ≤
        (∑ i, w i) / (2 * (Fintype.card Color : ℝ))) :
      (∑ i, X i (ω i)) ≤ (1 - (1 / 2 : ℝ)) *
        (∑ i, (U i).expect (X i)) := by
    rw [← hsum ω, hmean]
    have hdiv := div_le_div_of_nonneg_right hbad hW.le
    have hcard : 0 < (Fintype.card Color : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Color›
    have hden : 0 < 2 * (Fintype.card Color : ℝ) := by positivity
    have halg : ((∑ i, w i) / (2 * (Fintype.card Color : ℝ))) / W =
        (1 - (1 / 2 : ℝ)) * ((∑ i, w i) / (W * (Fintype.card Color : ℝ))) := by
      field_simp
      <;> ring
    rw [halg] at hdiv
    exact hdiv
  let P := FinProb.pi U
  have htail := xChernoff_lower U X hX (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hprob : P.pr (fun ω => (∑ i, if ω i = c then w i else 0) ≤
      (∑ i, w i) / (2 * (Fintype.card Color : ℝ))) ≤
      P.pr (fun ω => ∑ i, X i (ω i) ≤
        (1 - (1 / 2 : ℝ)) * (∑ i, (U i).expect (X i))) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro ω hω
    by_cases hbad : (∑ i, if ω i = c then w i else 0) ≤
        (∑ i, w i) / (2 * (Fintype.card Color : ℝ))
    · have htailω := hinclude ω hbad
      simp only [if_pos hbad, if_pos htailω]
      exact le_rfl
    · simp only [if_neg hbad]
      by_cases htailω : ∑ i, X i (ω i) ≤
          (1 - (1 / 2 : ℝ)) * (∑ i, (U i).expect (X i))
      · rw [if_pos htailω]
        exact (P.nonneg ω)
      · rw [if_neg htailω]
  have htail' : P.pr (fun ω => ∑ i, X i (ω i) ≤
        (1 - (1 / 2 : ℝ)) * (∑ i, (U i).expect (X i))) ≤
      Real.exp (-((∑ i, w i) / (8 * W * (Fintype.card Color : ℝ)))) := by
    have htail0 : (FinProb.pi U).pr (fun ω => ∑ i, X i (ω i) ≤
        (1 - (1 / 2 : ℝ)) * (∑ i, (U i).expect (X i))) ≤
        Real.exp (-(∑ i, (U i).expect (X i)) * (1 / 2 : ℝ) ^ 2 / 2) := by
      change (FinProb.pi U).pr (fun ω => ∑ i, X i (ω i) ≤
        (1 - (1 / 2 : ℝ)) * (∑ i, (U i).expect (X i))) ≤ _ at htail
      simpa using htail
    rw [hmean] at htail0
    have hcard : 0 < (Fintype.card Color : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Color›
    have hexp : -((∑ i, w i) / (W * (Fintype.card Color : ℝ))) *
          (1 / 2 : ℝ) ^ 2 / 2 =
        -((∑ i, w i) / (8 * W * (Fintype.card Color : ℝ))) := by
      field_simp [ne_of_gt hW, ne_of_gt hcard]
      <;> ring
    rw [hexp] at htail0
    simpa [P, hmean] using htail0
  exact le_trans hprob htail'

theorem uniform_colour_weight_upper_tail {I Color : Type*} [Fintype I]
    [DecidableEq I] [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (w : I → ℝ) (W : ℝ) (c : Color)
    (hw0 : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) (hW : 0 < W) :
    (FinProb.pi (fun _ : I =>
      FinProb.uniform (Finset.univ : Finset Color) Finset.univ_nonempty)).pr
      (fun ω => 2 * (∑ i, w i) / (Fintype.card Color : ℝ) ≤
        ∑ i, if ω i = c then w i else 0) ≤
      Real.exp (-((∑ i, w i) / (3 * W * (Fintype.card Color : ℝ)))) := by
  classical
  let U : I → FinProb Color := fun _ =>
    FinProb.uniform (Finset.univ : Finset Color) Finset.univ_nonempty
  let X : ∀ i : I, Color → ℝ := fun i d => if d = c then w i / W else 0
  have hX : ∀ i d, 0 ≤ X i d ∧ X i d ≤ 1 := by
    intro i d
    by_cases h : d = c
    · simp [X, h]
      exact ⟨div_nonneg (hw0 i) hW.le, (div_le_one₀ hW).2 (hwW i)⟩
    · simp [X, h]
  have hlocal (i : I) : (U i).expect (X i) = w i / (W * (Fintype.card Color : ℝ)) := by
    have hpoint : (fun d : Color => X i d) =
        (fun d => (w i / W) * (if d = c then (1 : ℝ) else 0)) := by
      funext d
      by_cases h : d = c <;> simp [X, h]
    change (U i).expect (fun d => X i d) = _
    rw [hpoint]
    simp [FinProb.expect, U, FinProb.uniform, Finset.sum_ite_eq', eq_comm]
    have hcard : (Fintype.card Color : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty Color›).ne'
    field_simp [ne_of_gt hW, hcard]
    <;> ring
  have hmean : (∑ i, (U i).expect (X i)) =
      (∑ i, w i) / (W * (Fintype.card Color : ℝ)) := by
    simp_rw [hlocal]
    rw [← Finset.sum_div]
  have hsum (ω : I → Color) :
      (∑ i, if ω i = c then w i else 0) / W = ∑ i, X i (ω i) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : ω i = c <;> simp [X, h]
  have hinclude (ω : I → Color)
      (hbad : 2 * (∑ i, w i) / (Fintype.card Color : ℝ) ≤
        ∑ i, if ω i = c then w i else 0) :
      (1 + (1 : ℝ)) * (∑ i, (U i).expect (X i)) ≤ ∑ i, X i (ω i) := by
    rw [← hsum ω, hmean]
    have hdiv := div_le_div_of_nonneg_right hbad hW.le
    have hcard : 0 < (Fintype.card Color : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Color›
    have halg : (2 * (∑ i, w i) / (Fintype.card Color : ℝ)) / W =
        (1 + (1 : ℝ)) * ((∑ i, w i) / (W * (Fintype.card Color : ℝ))) := by
      field_simp
      <;> ring
    exact halg ▸ hdiv
  let P := FinProb.pi U
  have htail := xChernoff_upper U X hX (1 : ℝ) (by norm_num)
  have hprob : P.pr (fun ω => 2 * (∑ i, w i) / (Fintype.card Color : ℝ) ≤
      ∑ i, if ω i = c then w i else 0) ≤
      P.pr (fun ω => (1 + (1 : ℝ)) * (∑ i, (U i).expect (X i)) ≤
        ∑ i, X i (ω i)) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro ω hω
    by_cases hbad : 2 * (∑ i, w i) / (Fintype.card Color : ℝ) ≤
        ∑ i, if ω i = c then w i else 0
    · have htailω := hinclude ω hbad
      simp only [if_pos hbad, if_pos htailω]
      exact le_rfl
    · simp only [if_neg hbad]
      by_cases htailω : (1 + (1 : ℝ)) * (∑ i, (U i).expect (X i)) ≤
          ∑ i, X i (ω i)
      · rw [if_pos htailω]
        exact (P.nonneg ω)
      · rw [if_neg htailω]
  have htail' : P.pr (fun ω => (1 + (1 : ℝ)) *
        (∑ i, (U i).expect (X i)) ≤ ∑ i, X i (ω i)) ≤
      Real.exp (-((∑ i, w i) / (3 * W * (Fintype.card Color : ℝ)))) := by
    have htail0 : (FinProb.pi U).pr (fun ω => (1 + (1 : ℝ)) *
        (∑ i, (U i).expect (X i)) ≤ ∑ i, X i (ω i)) ≤
        Real.exp (-(∑ i, (U i).expect (X i)) / (2 + 1)) := by
      change (FinProb.pi U).pr (fun ω => (1 + (1 : ℝ)) *
        (∑ i, (U i).expect (X i)) ≤ ∑ i, X i (ω i)) ≤ _ at htail
      simpa using htail
    rw [hmean] at htail0
    have hcard : 0 < (Fintype.card Color : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Color›
    have hexp : -((∑ i, w i) / (W * (Fintype.card Color : ℝ))) / (2 + 1) =
        -((∑ i, w i) / (3 * W * (Fintype.card Color : ℝ))) := by
      field_simp [ne_of_gt hW, ne_of_gt hcard]
      <;> ring
    rw [hexp] at htail0
    simpa [P, hmean] using htail0
  exact le_trans hprob htail'

end HypercubeRamsey.Lane_q_s17_pal
