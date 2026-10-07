import HypercubeRamsey.S18.ProducerInputs
import HypercubeRamsey.Tools.Mesh

namespace HypercubeRamsey.S18.Lane_q_s18_bridge

open Classical
open scoped BigOperators

abbrev Slot {κ : CConsts} {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) :=
  Σ i : Fin 𝒯.m, {y : Fin (T.S.N k) // y ∈ (𝒯.P i).Y}

noncomputable def slotFinEquiv {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Slot 𝒯 ≃ Fin (Fintype.card (Slot 𝒯)) :=
  Fintype.equivFin _

def dim {κ : CConsts} {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) : ℕ :=
  2 * Fintype.card (Slot 𝒯)

noncomputable def lawSlot {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (s : Slot 𝒯) : Fin (dim 𝒯) :=
  finProdFinEquiv (⟨0, by omega⟩, slotFinEquiv 𝒯 s)

noncomputable def priceSlot {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (s : Slot 𝒯) : Fin (dim 𝒯) :=
  finProdFinEquiv (⟨1, by omega⟩, slotFinEquiv 𝒯 s)

noncomputable def profileCoords {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (P : S14.ParameterProfile 𝒯) : Fin (dim 𝒯) → ℝ :=
  fun j =>
    let z := finProdFinEquiv.symm j
    let s := (slotFinEquiv 𝒯).symm z.2
    if z.1.val = 0 then (P.law s.1).w s.2.1 else P.price s.1 s.2.1

private noncomputable def decodedSlot {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (j : Fin (dim 𝒯)) : Slot 𝒯 :=
  (slotFinEquiv 𝒯).symm (finProdFinEquiv.symm j).2

private theorem lawSlot_decoded {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (j : Fin (dim 𝒯))
    (h : (finProdFinEquiv.symm j).1.val = 0) :
    lawSlot 𝒯 (decodedSlot 𝒯 j) = j := by
  let z := finProdFinEquiv.symm j
  let e : Fin 2 × Fin (Fintype.card (Slot 𝒯)) ≃ Fin (dim 𝒯) := finProdFinEquiv
  have hj : finProdFinEquiv (z.1, z.2) = j := finProdFinEquiv.apply_symm_apply j
  have hch : z.1 = ⟨0, by omega⟩ := Fin.ext h
  calc
    lawSlot 𝒯 (decodedSlot 𝒯 j) =
        e (⟨0, by omega⟩, z.2) := by
          simp [lawSlot, decodedSlot, z, e, Equiv.apply_symm_apply]
          rfl
    _ = e (z.1, z.2) := congrArg e (Prod.ext hch.symm rfl)
    _ = j := hj

private theorem priceSlot_decoded {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (j : Fin (dim 𝒯))
    (h : (finProdFinEquiv.symm j).1.val = 1) :
    priceSlot 𝒯 (decodedSlot 𝒯 j) = j := by
  let z := finProdFinEquiv.symm j
  let e : Fin 2 × Fin (Fintype.card (Slot 𝒯)) ≃ Fin (dim 𝒯) := finProdFinEquiv
  have hj : finProdFinEquiv (z.1, z.2) = j := finProdFinEquiv.apply_symm_apply j
  have hch : z.1 = ⟨1, by omega⟩ := Fin.ext h
  calc
    priceSlot 𝒯 (decodedSlot 𝒯 j) =
        e (⟨1, by omega⟩, z.2) := by
          simp [priceSlot, decodedSlot, z, e, Equiv.apply_symm_apply]
          rfl
    _ = e (z.1, z.2) := congrArg e (Prod.ext hch.symm rfl)
    _ = j := hj

theorem profileCoords_law {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (P : S14.ParameterProfile 𝒯) (s : Slot 𝒯) :
    profileCoords 𝒯 P (lawSlot 𝒯 s) = (P.law s.1).w s.2.1 := by
  dsimp [profileCoords, lawSlot]
  rw [Equiv.symm_apply_apply]
  rw [Equiv.symm_apply_apply]
  simp

theorem profileCoords_price {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (P : S14.ParameterProfile 𝒯) (s : Slot 𝒯) :
    profileCoords 𝒯 P (priceSlot 𝒯 s) = P.price s.1 s.2.1 := by
  dsimp [profileCoords, priceSlot]
  rw [Equiv.symm_apply_apply]
  rw [Equiv.symm_apply_apply]
  simp

noncomputable def lawCoordSum {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (x : Fin (dim 𝒯) → ℝ) (i : Fin 𝒯.m) : ℝ :=
  ∑ y : Fin (T.S.N k), if hy : y ∈ (𝒯.P i).Y then
    x (lawSlot 𝒯 ⟨i, ⟨y, hy⟩⟩) else 0

noncomputable def priceCoordSum {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (x : Fin (dim 𝒯) → ℝ) (i : Fin 𝒯.m) : ℝ :=
  ∑ y : Fin (T.S.N k), if hy : y ∈ (𝒯.P i).Y then
    x (priceSlot 𝒯 ⟨i, ⟨y, hy⟩⟩) else 0

noncomputable def ProfileCoordsValid {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (x : Fin (dim 𝒯) → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧
  (∀ i : Fin 𝒯.m, lawCoordSum 𝒯 x i = 1) ∧
  (∀ i : Fin 𝒯.m, priceCoordSum 𝒯 x i = 1) ∧
  (∀ s : Slot 𝒯,
    ((𝒯.P s.1).M : ℝ) * x (lawSlot 𝒯 s) ≤
      Real.exp (10 * (𝒯.kScale s.1 : ℝ) * 𝒯.tScale s.1))

noncomputable def profileCoordsCarrier {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Set (Fin (dim 𝒯) → ℝ) :=
  {x | ProfileCoordsValid 𝒯 x}

theorem profileCoords_valid {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (P : S14.ParameterProfile 𝒯) :
    ProfileCoordsValid 𝒯 (profileCoords 𝒯 P) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    let z := finProdFinEquiv.symm j
    let s := decodedSlot 𝒯 j
    by_cases hz : z.1.val = 0
    · rw [← lawSlot_decoded 𝒯 j hz, profileCoords_law]
      exact (P.law s.1).nonneg s.2.1
    · have hp : z.1.val = 1 := by omega
      rw [← priceSlot_decoded 𝒯 j hp, profileCoords_price]
      exact (P.price_simplex s.1).1 s.2.1
  · intro i
    unfold lawCoordSum
    calc
      (∑ y : Fin (T.S.N k), if hy : y ∈ (𝒯.P i).Y then
          profileCoords 𝒯 P (lawSlot 𝒯 ⟨i, ⟨y, hy⟩⟩) else 0) =
          ∑ y, (P.law i).w y := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ (𝒯.P i).Y
        · simp [hy, profileCoords_law]
        · simp [hy, P.law_supported i y hy]
      _ = 1 := (P.law i).sum_eq_one
  · intro i
    unfold priceCoordSum
    calc
      (∑ y : Fin (T.S.N k), if hy : y ∈ (𝒯.P i).Y then
          profileCoords 𝒯 P (priceSlot 𝒯 ⟨i, ⟨y, hy⟩⟩) else 0) =
          ∑ y, P.price i y := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ (𝒯.P i).Y
        · simp [hy, profileCoords_price]
        · simp [hy, (P.price_simplex i).2.1 y hy]
      _ = 1 := (P.price_simplex i).2.2
  · intro s
    rw [profileCoords_law]
    exact P.law_cap s.1 s.2.1

noncomputable def profileOfCoords {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (x : Fin (dim 𝒯) → ℝ)
    (hx : ProfileCoordsValid 𝒯 x) : S14.ParameterProfile 𝒯 := by
  classical
  refine {
    law := fun i => {
      w := fun y => if hy : y ∈ (𝒯.P i).Y then
        x (lawSlot 𝒯 ⟨i, ⟨y, hy⟩⟩) else 0
      nonneg := ?_
      sum_eq_one := ?_ }
    price := fun i y => if hy : y ∈ (𝒯.P i).Y then
      x (priceSlot 𝒯 ⟨i, ⟨y, hy⟩⟩) else 0
    law_supported := ?_
    law_cap := ?_
    price_simplex := ?_ }
  · intro y
    by_cases hy : y ∈ (𝒯.P i).Y
    · simpa only [dif_pos hy] using hx.1 (lawSlot 𝒯 ⟨i, ⟨y, hy⟩⟩)
    · simp only [dif_neg hy]
      norm_num
  · exact hx.2.1 i
  · intro i y hy
    simp [hy]
  · intro i y
    by_cases hy : y ∈ (𝒯.P i).Y
    · simpa only [dif_pos hy] using hx.2.2.2 ⟨i, ⟨y, hy⟩⟩
    · simp [hy]
      positivity
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · intro y
      by_cases hy : y ∈ (𝒯.P i).Y
      · simpa only [dif_pos hy] using hx.1 (priceSlot 𝒯 ⟨i, ⟨y, hy⟩⟩)
      · simp only [dif_neg hy]
        norm_num
    · intro y hy
      simp [hy]
    · exact hx.2.2.1 i

private theorem law_eq_of_weights {N : ℕ} {μ ν : Law N}
    (h : ∀ y, μ.w y = ν.w y) : μ = ν := by
  cases μ
  cases ν
  congr 1
  exact funext h

private theorem parameterProfile_ext {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {P Q : S14.ParameterProfile 𝒯}
    (hlaw : ∀ i y, (P.law i).w y = (Q.law i).w y)
    (hprice : ∀ i y, P.price i y = Q.price i y) : P = Q := by
  cases P with
  | mk lawP priceP supportP capP simplexP =>
    cases Q with
    | mk lawQ priceQ supportQ capQ simplexQ =>
      have hlaw' : lawP = lawQ := by
        funext i
        exact law_eq_of_weights (fun y => hlaw i y)
      have hprice' : priceP = priceQ := by
        funext i y
        exact hprice i y
      cases hlaw'
      cases hprice'
      have hs : supportP = supportQ := Subsingleton.elim _ _
      have hc : capP = capQ := Subsingleton.elim _ _
      have hp : simplexP = simplexQ := Subsingleton.elim _ _
      cases hs
      cases hc
      cases hp
      rfl

theorem profileCoords_profileOfCoords {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (x : Fin (dim 𝒯) → ℝ)
    (hx : ProfileCoordsValid 𝒯 x) :
    profileCoords 𝒯 (profileOfCoords x hx) = x := by
  funext j
  let z := finProdFinEquiv.symm j
  let s := decodedSlot 𝒯 j
  by_cases hzero : z.1.val = 0
  · have hidx : lawSlot 𝒯 s = j := lawSlot_decoded 𝒯 j hzero
    rw [← hidx, profileCoords_law]
    simp [profileOfCoords, s]
  · have hone : z.1.val = 1 := by omega
    have hidx : priceSlot 𝒯 s = j := priceSlot_decoded 𝒯 j hone
    rw [← hidx, profileCoords_price]
    simp [profileOfCoords, s]

theorem profileOfCoords_profileCoords {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (P : S14.ParameterProfile 𝒯) :
    profileOfCoords (profileCoords 𝒯 P) (profileCoords_valid 𝒯 P) = P := by
  apply parameterProfile_ext
  · intro i y
    by_cases hy : y ∈ (𝒯.P i).Y
    · simp [profileOfCoords, hy, profileCoords_law]
    · simp [profileOfCoords, hy, P.law_supported i y hy]
  · intro i y
    by_cases hy : y ∈ (𝒯.P i).Y
    · simp [profileOfCoords, hy, profileCoords_price]
    · simp [profileOfCoords, hy, (P.price_simplex i).2.1 y hy]

private theorem lawCoordSum_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) :
    Continuous (fun x => lawCoordSum 𝒯 x i) := by
  classical
  unfold lawCoordSum
  apply continuous_finsetSum _
  intro y hy
  by_cases h : y ∈ (𝒯.P i).Y
  · simpa [h] using (continuous_apply (lawSlot 𝒯 ⟨i, ⟨y, h⟩⟩))
  · simpa [h] using (continuous_const : Continuous fun _ : Fin (dim 𝒯) → ℝ => (0 : ℝ))

private theorem priceCoordSum_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) :
    Continuous (fun x => priceCoordSum 𝒯 x i) := by
  classical
  unfold priceCoordSum
  apply continuous_finsetSum _
  intro y hy
  by_cases h : y ∈ (𝒯.P i).Y
  · simpa [h] using (continuous_apply (priceSlot 𝒯 ⟨i, ⟨y, h⟩⟩))
  · simpa [h] using (continuous_const : Continuous fun _ : Fin (dim 𝒯) → ℝ => (0 : ℝ))

private theorem profileCoordsCarrier_closed {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : IsClosed (profileCoordsCarrier 𝒯) := by
  classical
  have hnonneg : IsClosed {x : Fin (dim 𝒯) → ℝ | ∀ j, 0 ≤ x j} := by
    convert isClosed_iInter (fun j : Fin (dim 𝒯) =>
      (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).preimage
        (continuous_apply j)) using 1
    ext x
    simp
  have hlaw : IsClosed {x : Fin (dim 𝒯) → ℝ | ∀ i, lawCoordSum 𝒯 x i = 1} := by
    convert isClosed_iInter (fun i : Fin 𝒯.m =>
      (isClosed_singleton : IsClosed ({(1 : ℝ)} : Set ℝ)).preimage
        (lawCoordSum_continuous 𝒯 i)) using 1
    ext x
    simp
  have hprice : IsClosed {x : Fin (dim 𝒯) → ℝ | ∀ i, priceCoordSum 𝒯 x i = 1} := by
    convert isClosed_iInter (fun i : Fin 𝒯.m =>
      (isClosed_singleton : IsClosed ({(1 : ℝ)} : Set ℝ)).preimage
        (priceCoordSum_continuous 𝒯 i)) using 1
    ext x
    simp
  have hcap : IsClosed {x : Fin (dim 𝒯) → ℝ |
      ∀ s : Slot 𝒯, ((𝒯.P s.1).M : ℝ) * x (lawSlot 𝒯 s) ≤
        Real.exp (10 * (𝒯.kScale s.1 : ℝ) * 𝒯.tScale s.1)} := by
    rw [show {x : Fin (dim 𝒯) → ℝ | ∀ s : Slot 𝒯,
        ((𝒯.P s.1).M : ℝ) * x (lawSlot 𝒯 s) ≤
          Real.exp (10 * (𝒯.kScale s.1 : ℝ) * 𝒯.tScale s.1)} =
      ⋂ s : Slot 𝒯, {x : Fin (dim 𝒯) → ℝ |
        ((𝒯.P s.1).M : ℝ) * x (lawSlot 𝒯 s) ≤
          Real.exp (10 * (𝒯.kScale s.1 : ℝ) * 𝒯.tScale s.1)} by
        ext x
        simp]
    exact isClosed_iInter fun s => isClosed_le
      ((continuous_const : Continuous fun _ : Fin (dim 𝒯) → ℝ =>
        ((𝒯.P s.1).M : ℝ)).mul (continuous_apply (lawSlot 𝒯 s)))
      (continuous_const : Continuous fun _ : Fin (dim 𝒯) → ℝ =>
        Real.exp (10 * (𝒯.kScale s.1 : ℝ) * 𝒯.tScale s.1))
  change IsClosed {x | (∀ j, 0 ≤ x j) ∧ (∀ i, lawCoordSum 𝒯 x i = 1) ∧
    (∀ i, priceCoordSum 𝒯 x i = 1) ∧
    (∀ s : Slot 𝒯, ((𝒯.P s.1).M : ℝ) * x (lawSlot 𝒯 s) ≤
      Real.exp (10 * (𝒯.kScale s.1 : ℝ) * 𝒯.tScale s.1))}
  simpa only [Set.setOf_and] using hnonneg.inter (hlaw.inter (hprice.inter hcap))

private theorem profileCoordsCarrier_convex {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Convex ℝ (profileCoordsCarrier 𝒯) := by
  classical
  intro x hx y hy a b ha hb hab
  change ProfileCoordsValid 𝒯 (fun j => a * x j + b * y j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · intro i
    have hlin : lawCoordSum 𝒯 (fun j => a * x j + b * y j) i =
        a * lawCoordSum 𝒯 x i + b * lawCoordSum 𝒯 y i := by
      unfold lawCoordSum
      calc
        (∑ y_1, if hy_1 : y_1 ∈ (𝒯.P i).Y then
            a * x (lawSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) +
              b * y (lawSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0) =
            ∑ y_1, (a * (if hy_1 : y_1 ∈ (𝒯.P i).Y then
              x (lawSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0) +
              b * (if hy_1 : y_1 ∈ (𝒯.P i).Y then
              y (lawSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0)) := by
                apply Finset.sum_congr rfl
                intro y_1 _
                by_cases h : y_1 ∈ (𝒯.P i).Y <;> simp [h]
        _ = a * (∑ y_1, if hy_1 : y_1 ∈ (𝒯.P i).Y then
              x (lawSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0) +
            b * (∑ y_1, if hy_1 : y_1 ∈ (𝒯.P i).Y then
              y (lawSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hlin, hx.2.1 i, hy.2.1 i]
    nlinarith
  · intro i
    have hlin : priceCoordSum 𝒯 (fun j => a * x j + b * y j) i =
        a * priceCoordSum 𝒯 x i + b * priceCoordSum 𝒯 y i := by
      unfold priceCoordSum
      calc
        (∑ y_1, if hy_1 : y_1 ∈ (𝒯.P i).Y then
            a * x (priceSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) +
              b * y (priceSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0) =
            ∑ y_1, (a * (if hy_1 : y_1 ∈ (𝒯.P i).Y then
              x (priceSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0) +
              b * (if hy_1 : y_1 ∈ (𝒯.P i).Y then
              y (priceSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0)) := by
                apply Finset.sum_congr rfl
                intro y_1 _
                by_cases h : y_1 ∈ (𝒯.P i).Y <;> simp [h]
        _ = a * (∑ y_1, if hy_1 : y_1 ∈ (𝒯.P i).Y then
              x (priceSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0) +
            b * (∑ y_1, if hy_1 : y_1 ∈ (𝒯.P i).Y then
              y (priceSlot 𝒯 ⟨i, ⟨y_1, hy_1⟩⟩) else 0) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hlin, hx.2.2.1 i, hy.2.2.1 i]
    nlinarith
  · intro s
    have hxcap := hx.2.2.2 s
    have hycap := hy.2.2.2 s
    calc
      ((𝒯.P s.1).M : ℝ) * (a * x (lawSlot 𝒯 s) + b * y (lawSlot 𝒯 s)) =
          a * (((𝒯.P s.1).M : ℝ) * x (lawSlot 𝒯 s)) +
            b * (((𝒯.P s.1).M : ℝ) * y (lawSlot 𝒯 s)) := by ring
      _ ≤ a * Real.exp (10 * (𝒯.kScale s.1 : ℝ) * 𝒯.tScale s.1) +
          b * Real.exp (10 * (𝒯.kScale s.1 : ℝ) * 𝒯.tScale s.1) :=
        add_le_add (mul_le_mul_of_nonneg_left hxcap ha)
          (mul_le_mul_of_nonneg_left hycap hb)
      _ = Real.exp (10 * (𝒯.kScale s.1 : ℝ) * 𝒯.tScale s.1) := by rw [← add_mul, hab, one_mul]

private theorem profileCoords_le_one {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) {x : Fin (dim 𝒯) → ℝ}
    (hx : ProfileCoordsValid 𝒯 x) (j : Fin (dim 𝒯)) : x j ≤ 1 := by
  classical
  let z := finProdFinEquiv.symm j
  let s := decodedSlot 𝒯 j
  by_cases hz : z.1.val = 0
  · have hidx := lawSlot_decoded 𝒯 j hz
    have hsingle : x (lawSlot 𝒯 s) ≤ lawCoordSum 𝒯 x s.1 := by
      have hle := Finset.single_le_sum
        (f := fun y : Fin (T.S.N k) => if hy : y ∈ (𝒯.P s.1).Y then
          x (lawSlot 𝒯 ⟨s.1, ⟨y, hy⟩⟩) else 0)
        (a := s.2.1)
        (fun y _ => by
          by_cases hy : y ∈ (𝒯.P s.1).Y
          · simpa only [dif_pos hy] using hx.1 (lawSlot 𝒯 ⟨s.1, ⟨y, hy⟩⟩)
          · simp only [dif_neg hy]
            norm_num)
        (Finset.mem_univ s.2.1)
      simpa [lawCoordSum, s.2.2] using hle
    have := hsingle.trans_eq (hx.2.1 s.1)
    change x (lawSlot 𝒯 (decodedSlot 𝒯 j)) ≤ 1 at this
    rw [hidx] at this
    exact this
  · have hp : z.1.val = 1 := by omega
    have hidx := priceSlot_decoded 𝒯 j hp
    have hsingle : x (priceSlot 𝒯 s) ≤ priceCoordSum 𝒯 x s.1 := by
      have hle := Finset.single_le_sum
        (f := fun y : Fin (T.S.N k) => if hy : y ∈ (𝒯.P s.1).Y then
          x (priceSlot 𝒯 ⟨s.1, ⟨y, hy⟩⟩) else 0)
        (a := s.2.1)
        (fun y _ => by
          by_cases hy : y ∈ (𝒯.P s.1).Y
          · simpa only [dif_pos hy] using hx.1 (priceSlot 𝒯 ⟨s.1, ⟨y, hy⟩⟩)
          · simp only [dif_neg hy]
            norm_num)
        (Finset.mem_univ s.2.1)
      simpa [priceCoordSum, s.2.2] using hle
    have := hsingle.trans_eq (hx.2.2.1 s.1)
    change x (priceSlot 𝒯 (decodedSlot 𝒯 j)) ≤ 1 at this
    rw [hidx] at this
    exact this

private theorem profileCoordsCarrier_compact {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : IsCompact (profileCoordsCarrier 𝒯) := by
  have hbox : IsCompact (Set.pi (Set.univ : Set (Fin (dim 𝒯)))
      (fun _ => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : profileCoordsCarrier 𝒯 ⊆
      Set.pi (Set.univ : Set (Fin (dim 𝒯))) (fun _ => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Set.mem_pi]
    intro j hj
    exact ⟨hx.1 j, profileCoords_le_one 𝒯 hx j⟩
  exact hbox.of_isClosed_subset (profileCoordsCarrier_closed 𝒯) hsub

private theorem slot_label_injective {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : 𝒯.Valid) :
    Function.Injective (fun s : Slot 𝒯 => s.2.1) := by
  classical
  intro s₁ s₂ h
  rcases s₁ with ⟨i, a⟩
  rcases s₂ with ⟨j, b⟩
  change a.1 = b.1 at h
  have hij : i = j := by
    by_contra hne
    have hdis := h𝒯.patch_Y_disjoint i j hne
    have hb : a.1 ∈ (𝒯.P j).Y := by simpa [h] using b.2
    exact (Finset.disjoint_left.mp hdis) a.2 hb
  subst j
  exact congrArg (fun q : {y : Fin (T.S.N k) // y ∈ (𝒯.P i).Y} =>
    (⟨i, q⟩ : Slot 𝒯)) (Subtype.ext h)

private theorem meshDimension_le {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : 𝒯.Valid) :
    dim 𝒯 ≤ 2 * T.S.N k := by
  have hcard : Fintype.card (Slot 𝒯) ≤ T.S.N k := by
    simpa using Fintype.card_le_of_injective
      (fun s : Slot 𝒯 => s.2.1) (slot_label_injective h𝒯)
  unfold dim
  exact Nat.mul_le_mul_left 2 hcard

private noncomputable def uniformParameterProfile {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : 𝒯.Valid) : S14.ParameterProfile 𝒯 where
  law i := Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2
  price i y := (Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2).w y
  law_supported i := by
    intro y hy
    simp [Law.unifCore, hy]
  law_cap i y := by
    have he : 1 ≤ Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
      apply Real.one_le_exp_iff.mpr
      positivity
    by_cases hy : y ∈ (𝒯.P i).Y
    · have hM : ((𝒯.P i).M : ℝ) ≠ 0 := by
        have hpos : 0 < (𝒯.P i).M := by
          have hcard := Finset.card_pos.mpr (h𝒯.patch_nonempty i).2
          rw [(𝒯.P i).cardY] at hcard
          exact hcard
        exact_mod_cast hpos.ne'
      have hw : (Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2).w y =
          ((𝒯.P i).Y.card : ℝ)⁻¹ := by simp [Law.unifCore, hy]
      rw [hw, (𝒯.P i).cardY, mul_inv_cancel₀ hM]
      exact he
    · simp [Law.unifCore, hy]
      positivity
  price_simplex i := by
    refine ⟨(Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2).nonneg, ?_,
      (Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2).sum_eq_one⟩
    intro y hy
    simp [Law.unifCore, hy]

private theorem profileCoordsCarrier_nonempty {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : 𝒯.Valid) : (profileCoordsCarrier 𝒯).Nonempty := by
  refine ⟨profileCoords 𝒯 (uniformParameterProfile h𝒯), profileCoords_valid 𝒯 _⟩

private theorem profileCoords_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Continuous (profileCoords 𝒯) := by
  classical
  let compress :
      ((Fin 𝒯.m → Fin (T.S.N k) → ℝ) ×
        (Fin 𝒯.m → Fin (T.S.N k) → ℝ)) → Fin (dim 𝒯) → ℝ :=
    fun v j =>
      let z := finProdFinEquiv.symm j
      let s := decodedSlot 𝒯 j
      if z.1.val = 0 then v.1 s.1 s.2.1 else v.2 s.1 s.2.1
  have hcompress : Continuous compress := by
    apply continuous_pi
    intro j
    dsimp [compress]
    let z := finProdFinEquiv.symm j
    let s := decodedSlot 𝒯 j
    by_cases hz : z.1.val = 0 <;> simp [z, s, hz] <;> fun_prop
  rw [S14.instParameterProfileTop]
  change Continuous (fun P : S14.ParameterProfile 𝒯 => compress P.coordinates)
  exact hcompress.comp continuous_induced_dom

private theorem profileOfCoords_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) :
    Continuous (fun x : profileCoordsCarrier 𝒯 => profileOfCoords x.1 x.2) := by
  classical
  rw [S14.instParameterProfileTop]
  apply continuous_induced_rng.mpr
  change Continuous (fun x : profileCoordsCarrier 𝒯 =>
    ((fun i y => ((profileOfCoords x.1 x.2).law i).w y),
      (fun i y => (profileOfCoords x.1 x.2).price i y)))
  have hval : Continuous (fun x : profileCoordsCarrier 𝒯 => x.1) := continuous_subtype_val
  apply (continuous_pi fun i => continuous_pi fun y => ?_).prodMk
    (continuous_pi fun i => continuous_pi fun y => ?_)
  · by_cases hy : y ∈ (𝒯.P i).Y
    · have heval : Continuous
          (fun f : Fin (dim 𝒯) → ℝ => f (lawSlot 𝒯 ⟨i, ⟨y, hy⟩⟩)) := continuous_apply _
      convert heval.comp hval using 1
      funext x
      simp [profileOfCoords, hy]
    · simpa [profileOfCoords, hy] using
        (continuous_const : Continuous fun _ : profileCoordsCarrier 𝒯 => (0 : ℝ))
  · by_cases hy : y ∈ (𝒯.P i).Y
    · have heval : Continuous
          (fun f : Fin (dim 𝒯) → ℝ => f (priceSlot 𝒯 ⟨i, ⟨y, hy⟩⟩)) := continuous_apply _
      convert heval.comp hval using 1
      funext x
      simp [profileOfCoords, hy]
    · simpa [profileOfCoords, hy] using
        (continuous_const : Continuous fun _ : profileCoordsCarrier 𝒯 => (0 : ℝ))

private noncomputable def decodedProfile {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (p : profileCoordsCarrier 𝒯) : S14.ParameterProfile 𝒯 :=
  profileOfCoords p.1 p.2

private theorem inputOK_of_decodedProfile {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : 𝒯.Valid) (hc : 𝒯.mode.isCluster)
    (p : profileCoordsCarrier 𝒯) :
    InputOK 𝒯 h𝒯 (fun i => (decodedProfile p).law i) := by
  intro i
  refine ⟨(decodedProfile p).law_supported i, ?_⟩
  change (if 𝒯.mode.isCluster then _ else _)
  rw [if_pos hc]
  exact (decodedProfile p).law_cap i

private noncomputable def chosenCleanCorner {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : 𝒯.Valid) (hc : 𝒯.mode.isCluster)
    (hclean : ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
      ∃ C : Finset (Fin (T.S.N k)),
        ((𝒯.P i).X \ C).card < κ.a * (𝒯.P i).M ∧ CleanProps 𝒯 i π C ∧
        (𝒯.mode.isCluster → ∀ π',
          NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) → CleanProps 𝒯 i π' C))
    (p : profileCoordsCarrier 𝒯) (i : Fin 𝒯.m) :
    Finset (Fin (T.S.N k)) :=
  Classical.choose (hclean i (fun j => (decodedProfile p).law j)
    (inputOK_of_decodedProfile h𝒯 hc p))

private theorem chosenCleanCorner_spec {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : 𝒯.Valid) (hc : 𝒯.mode.isCluster)
    (hclean : ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
      ∃ C : Finset (Fin (T.S.N k)),
        ((𝒯.P i).X \ C).card < κ.a * (𝒯.P i).M ∧ CleanProps 𝒯 i π C ∧
        (𝒯.mode.isCluster → ∀ π',
          NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) → CleanProps 𝒯 i π' C))
    (p : profileCoordsCarrier 𝒯) (i : Fin 𝒯.m) :
    ((𝒯.P i).X \ chosenCleanCorner h𝒯 hc hclean p i).card < κ.a * (𝒯.P i).M ∧
      CleanProps 𝒯 i (fun j => (decodedProfile p).law j)
        (chosenCleanCorner h𝒯 hc hclean p i) ∧
      (𝒯.mode.isCluster → ∀ π',
        NearInput (fun j => (decodedProfile p).law j) π'
          ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
          CleanProps 𝒯 i π' (chosenCleanCorner h𝒯 hc hclean p i)) :=
  Classical.choose_spec (hclean i (fun j => (decodedProfile p).law j)
    (inputOK_of_decodedProfile h𝒯 hc p))

theorem cleaned_profile_mesh_exists_helper {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (h𝒯 : 𝒯.Valid) (hcluster : 𝒯.mode.isCluster)
    (hclean : ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
      ∃ C : Finset (Fin (T.S.N k)),
        ((𝒯.P i).X \ C).card < κ.a * (𝒯.P i).M ∧ CleanProps 𝒯 i π C ∧
        (𝒯.mode.isCluster → ∀ π',
          NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) → CleanProps 𝒯 i π' C)) :
    ∃ mesh : Mesh 𝒯, S14.MeshCleaned mesh ∧
      Nonempty (S14.MeshProfileDomain mesh) ∧ S14.MeshReady mesh := by
  classical
  let K := profileCoordsCarrier 𝒯
  have hKne : K.Nonempty := profileCoordsCarrier_nonempty h𝒯
  have hKcompact : IsCompact K := profileCoordsCarrier_compact 𝒯
  have hKconvex : Convex ℝ K := profileCoordsCarrier_convex 𝒯
  have hdim : dim 𝒯 ≤ 2 * T.S.N k := meshDimension_le h𝒯
  have hnNat : 0 < T.S.n k := by
    by_contra hn
    have hn0 : T.S.n k = 0 := by omega
    have hN := T.S.N_pos k
    have hle := T.S.N_le k
    rw [hn0] at hle
    simp at hle
    omega
  have hn : 0 < (T.S.n k : ℝ) := by exact_mod_cast hnNat
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  let radius : ℝ := min
    (Real.rpow (T.S.n k : ℝ) (-3 : ℝ) / (T.S.N k : ℝ))
    (1 / ((T.S.n k : ℝ) * (T.S.N k : ℝ)))
  have hradius : 0 < radius := by
    dsimp [radius]
    apply lt_min
    · exact div_pos (Real.rpow_pos_of_pos hn _) hN
    · exact one_div_pos.mpr (mul_pos hn hN)
  obtain ⟨m, base, weight, hweight_cont, hweight_nonneg, hweight_sum,
    hlocal, hactive⟩ :=
      HypercubeRamsey.exists_finite_mesh (dim 𝒯) K hKne hKcompact hKconvex radius hradius
  let Param := {x : Fin (dim 𝒯) → ℝ // x ∈ K}
  let Profile := fun p : Param => decodedProfile (𝒯 := 𝒯) p
  let Corner := fun v i => chosenCleanCorner h𝒯 hcluster hclean (base v) i
  have hNmul : (T.S.N k : ℝ) * radius ≤ Real.rpow (T.S.n k : ℝ) (-3 : ℝ) := by
    have hr := min_le_left
      (Real.rpow (T.S.n k : ℝ) (-3 : ℝ) / (T.S.N k : ℝ))
      (1 / ((T.S.n k : ℝ) * (T.S.N k : ℝ)))
    calc
      (T.S.N k : ℝ) * radius ≤
          (T.S.N k : ℝ) *
            (Real.rpow (T.S.n k : ℝ) (-3 : ℝ) / (T.S.N k : ℝ)) :=
        mul_le_mul_of_nonneg_left hr hN.le
      _ = Real.rpow (T.S.n k : ℝ) (-3 : ℝ) := by field_simp [ne_of_gt hN]
  have hNMle : ∀ i : Fin 𝒯.m, (𝒯.P i).M ≤ T.S.N k := by
    intro i
    rw [← (𝒯.P i).cardX]
    simpa only [Fintype.card_fin] using Finset.card_le_univ (𝒯.P i).X
  have hMpos : ∀ i : Fin 𝒯.m, 0 < (𝒯.P i).M := by
    intro i
    have hY := Finset.card_pos.mpr (h𝒯.patch_nonempty i).2
    rw [(𝒯.P i).cardY] at hY
    exact hY
  let mesh : Mesh 𝒯 := {
    V := Fin m
    Param := Param
    paramLaw := fun p i => (Profile p).law i
    paramPrice := fun p i y => (Profile p).price i y
    paramLaw_supp := fun p i => (Profile p).law_supported i
    paramLaw_cap := fun p i y => (Profile p).law_cap i y
    paramPrice_simplex := fun p i => (Profile p).price_simplex i
    base := base
    wt := weight
    corner := Corner
    wt_cont := hweight_cont
    wt_nonneg := hweight_nonneg
    wt_sum_one := hweight_sum
    local_law := by
      intro v p hv i
      have hpoint : ∀ y, |((Profile p).law i).w y - ((Profile (base v)).law i).w y| ≤ radius := by
        intro y
        by_cases hy : y ∈ (𝒯.P i).Y
        · have hcoord := hlocal v p hv (lawSlot 𝒯 ⟨i, ⟨y, hy⟩⟩)
          simpa [Profile, decodedProfile, profileOfCoords, hy] using hcoord
        · simpa [Profile, decodedProfile, profileOfCoords, hy] using hradius.le
      calc
        (∑ y, |((Profile p).law i).w y - ((Profile (base v)).law i).w y|) ≤
            ∑ y : Fin (T.S.N k), radius :=
          Finset.sum_le_sum fun y _ => hpoint y
        _ = (T.S.N k : ℝ) * radius := by simp
        _ ≤ Real.rpow (T.S.n k : ℝ) (-3 : ℝ) := hNmul
    local_price := by
      intro v p hv i y
      have hpoint : |(Profile p).price i y - (Profile (base v)).price i y| ≤ radius := by
        by_cases hy : y ∈ (𝒯.P i).Y
        · have hcoord := hlocal v p hv (priceSlot 𝒯 ⟨i, ⟨y, hy⟩⟩)
          simpa [Profile, decodedProfile, profileOfCoords, hy] using hcoord
        · simpa [Profile, decodedProfile, profileOfCoords, hy] using hradius.le
      have hr := min_le_right
        (Real.rpow (T.S.n k : ℝ) (-3 : ℝ) / (T.S.N k : ℝ))
        (1 / ((T.S.n k : ℝ) * (T.S.N k : ℝ)))
      have hMi : 0 < ((𝒯.P i).M : ℝ) := by exact_mod_cast hMpos i
      have hden : (T.S.n k : ℝ) * (𝒯.P i).M ≤
          (T.S.n k : ℝ) * (T.S.N k : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hNMle i) hn.le
      have hinv : 1 / ((T.S.N k : ℝ) * (T.S.n k : ℝ)) ≤
          1 / ((𝒯.P i).M * (T.S.n k : ℝ)) := by
        have hp : 0 < (𝒯.P i).M * (T.S.n k : ℝ) := mul_pos hMi hn
        have hle : (𝒯.P i).M * (T.S.n k : ℝ) ≤
            (T.S.N k : ℝ) * (T.S.n k : ℝ) := by nlinarith [hden]
        exact one_div_le_one_div_of_le hp hle
      calc
        |(Profile p).price i y - (Profile (base v)).price i y| ≤ radius := hpoint
        _ ≤ 1 / ((T.S.n k : ℝ) * (T.S.N k : ℝ)) := hr
        _ = 1 / ((T.S.N k : ℝ) * (T.S.n k : ℝ)) := by ring
        _ ≤ 1 / ((𝒯.P i).M * (T.S.n k : ℝ)) := hinv
        _ = 1 / ((T.S.n k : ℝ) * (𝒯.P i).M) := by ring
    active_bound := by
      intro p
      exact (hactive p).trans (Nat.add_le_add_right hdim 1) }
  have hcleaned : S14.MeshCleaned mesh := by
    intro v p i hv
    have hspec := chosenCleanCorner_spec h𝒯 hcluster hclean (base v) i
    have hnear : NearInput (fun j => (Profile (base v)).law j) (fun j => (Profile p).law j)
        ((T.S.n k : ℝ) ^ (-3 : ℝ)) := by
      intro j
      simpa [mesh, Profile, abs_sub_comm] using mesh.local_law v p hv j
    simpa [mesh, Corner, Profile] using hspec.2.2 hcluster
      (fun j => (Profile p).law j) hnear
  let domain : S14.MeshProfileDomain mesh := {
    dim := dim 𝒯
    carrier := K
    encode := Equiv.refl _
    encode_continuous := continuous_subtype_val
    decode_continuous := continuous_id
    domain := ⟨hKne, hKcompact, hKconvex⟩
    dimension_bound := hdim
    coordinates := profileCoords 𝒯
    coordinates_mem := fun p => profileCoords_valid 𝒯 p
    coordinates_continuous := profileCoords_continuous 𝒯
    profileOf := Profile
    profileOf_law := fun p i => rfl
    profileOf_price := fun p i y => rfl
    profileOf_coordinates := by
      intro p
      apply Subtype.ext
      exact (profileCoords_profileOfCoords p.1 p.2).symm
    profileOf_continuous := profileOfCoords_continuous 𝒯
    realize := fun P => ⟨profileCoords 𝒯 P, profileCoords_valid 𝒯 P⟩
    realize_law := by
      intro P i
      have he := congrArg (fun Q : S14.ParameterProfile 𝒯 => Q.law i)
        (profileOfCoords_profileCoords P)
      exact he
    realize_price := by
      intro P i y
      have he := congrArg (fun Q : S14.ParameterProfile 𝒯 => Q.price i y)
        (profileOfCoords_profileCoords P)
      exact he
    realize_coordinates := by
      intro P
      apply Subtype.ext
      rfl
    realize_profileOf := by
      intro p
      apply Subtype.ext
      exact profileCoords_profileOfCoords p.1 p.2
    profileOf_realize := by
      intro P
      exact profileOfCoords_profileCoords P
    realize_continuous := by
      exact (profileCoords_continuous 𝒯).subtype_mk
        (fun P => profileCoords_valid 𝒯 P) }
  have hready : S14.MeshReady mesh := by
    have hparam : Nonempty Param := by
      rcases hKne with ⟨x, hx⟩
      exact ⟨⟨x, hx⟩⟩
    refine ⟨hparam, ?_⟩
    intro v p i hv
    simpa [mesh, Corner] using
      ((chosenCleanCorner_spec h𝒯 hcluster hclean (base v) i).2.1).card_lower
  exact ⟨mesh, hcleaned, ⟨domain⟩, hready⟩
end HypercubeRamsey.S18.Lane_q_s18_bridge
