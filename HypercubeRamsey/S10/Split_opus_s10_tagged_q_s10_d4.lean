import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.StdSimplex
import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k

namespace HypercubeRamsey.Lane_q_s10_d4

open scoped BigOperators

open OAI.HypercubeRamsey HypercubeRamsey HypercubeRamsey.S10

theorem parity_flip_of_hammingDist_one {n : ℕ} (u v : CubeVertex n)
    (h : _root_.hammingDist u v = 1) :
    IsEvenRole v ↔ ¬ IsEvenRole u := by
  classical
  let D := Finset.univ.filter fun i : Fin n => u i ≠ v i
  have hD : D.card = 1 := by simpa [D, _root_.hammingDist] using h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hD
  let U := Finset.univ.filter fun k : Fin n => u k = true
  let V := Finset.univ.filter fun k : Fin n => v k = true
  change Even V.card ↔ ¬ Even U.card
  by_cases hui : u i = true
  · have hvi : v i = false := by
      cases h : v i
      · rfl
      · have himem : i ∈ D := by rw [hi]; simp
        simp [D, h, hui] at himem
    have hset : U = insert i V := by
      ext k
      by_cases hki : k = i
      · subst k
        simp [U, V, hui, hvi]
      · have hsame : u k = v k := by
          by_contra hne
          have hmem : k ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          rw [hi] at hmem
          simp at hmem
          exact hki hmem
        simp [U, V, hki, hsame]
    have hiV : i ∉ V := by simp [V, hvi]
    have hcard : U.card = V.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hiV]
    rw [hcard]
    constructor
    · intro he hsucc
      exact (Nat.even_add_one.mp hsucc) he
    · intro hnot
      by_contra hodd
      exact hnot (Nat.even_add_one.mpr hodd)
  · have hui' : u i = false := Bool.eq_false_iff.mpr hui
    have hvi : v i = true := by
      cases h : v i
      · have himem : i ∈ D := by rw [hi]; simp
        simp [D, h, hui'] at himem
      · rfl
    have hset : V = insert i U := by
      ext k
      by_cases hki : k = i
      · subst k
        simp [U, V, hui', hvi]
      · have hsame : u k = v k := by
          by_contra hne
          have hmem : k ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          rw [hi] at hmem
          simp at hmem
          exact hki hmem
        simp [U, V, hki, hsame]
    have hiU : i ∉ U := by simp [U, hui']
    have hcard : V.card = U.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hiU]
    rw [hcard]
    exact Nat.even_add_one

open Classical in
theorem parity_subtype_card {n : ℕ} (hn : 0 < n) :
    Fintype.card {v : CubeVertex n // IsEvenRole v} = 2 ^ (n - 1) ∧
    Fintype.card {v : CubeVertex n // ¬ IsEvenRole v} = 2 ^ (n - 1) := by
  classical
  let i₀ : Fin n := ⟨0, by omega⟩
  let flip (v : CubeVertex n) := p10_1kFlipCoordinate v i₀
  let Ev := {v : CubeVertex n // IsEvenRole v}
  let Od := {v : CubeVertex n // ¬ IsEvenRole v}
  have hflip (v : CubeVertex n) : IsEvenRole (flip v) ↔ ¬ IsEvenRole v := by
    apply parity_flip_of_hammingDist_one
    change _root_.hammingDist v (p10_1kFlipCoordinate v i₀) = 1
    exact p10_1kFlipCoordinate_hammingDist n v i₀
  let e : Ev ≃ Od := {
    toFun := fun v => ⟨flip v.1, by
      intro hEven
      exact (hflip v.1).mp hEven v.2⟩
    invFun := fun v => ⟨flip v.1, (hflip v.1).mpr v.2⟩
    left_inv := by
      intro v
      apply Subtype.ext
      funext k
      by_cases hk : k = i₀ <;> simp [flip, p10_1kFlipCoordinate, hk]
    right_inv := by
      intro v
      apply Subtype.ext
      funext k
      by_cases hk : k = i₀ <;> simp [flip, p10_1kFlipCoordinate, hk]
  }
  have hEO : Fintype.card Ev = Fintype.card Od := Fintype.card_congr e
  have hO : Fintype.card Od = Fintype.card (CubeVertex n) - Fintype.card Ev := by
    simp [Od, Ev]
  have hCube : Fintype.card (CubeVertex n) = 2 ^ n := by simp [CubeVertex]
  have hpow : (2 : ℕ) ^ n = (2 : ℕ) ^ (n - 1) * 2 := by
    calc
      (2 : ℕ) ^ n = (2 : ℕ) ^ ((n - 1) + 1) := by congr 1 <;> omega
      _ = (2 : ℕ) ^ (n - 1) * 2 := by rw [pow_succ]
  have hE : Fintype.card Ev = 2 ^ (n - 1) := by
    rw [← hEO] at hO
    rw [hCube, hpow] at hO
    omega
  exact ⟨hE, hEO.symm.trans hE⟩

theorem slice_parity_fiber_card_le {n m : ℕ} (hm : m ≤ n) (hmstrict : m < n)
    (s : Fin m → Bool) (P : CubeVertex n → Prop) [DecidablePred P]
    (hflip : ∀ u v : CubeVertex n, _root_.hammingDist u v = 1 → (P v ↔ ¬ P u)) :
    Fintype.card {v : CubeVertex n // P v ∧ p10_1kSpecialSlice hm v = s} ≤
      2 ^ (n - m - 1) := by
  classical
  let d := n - m
  have hd : 0 < d := by dsimp [d]; omega
  let i₀ : Fin d := ⟨0, hd⟩
  let e := p10_1kSliceWordEquiv hm
  let res (v : CubeVertex n) : Fin d → Bool := p10_1kResidualWord hm v
  let flip (w : Fin d → Bool) : Fin d → Bool := p10_1kFlipCoordinate w i₀
  let Fiber := {v : CubeVertex n // P v ∧ p10_1kSpecialSlice hm v = s}
  have hinv : Function.Involutive flip := by
    intro w
    funext i
    by_cases hi : i = i₀
    · subst i
      simp [flip, p10_1kFlipCoordinate]
    · simp [flip, p10_1kFlipCoordinate, hi]
  have sameVertex {v w : Fiber} (h : res v.1 = res w.1) : v = w := by
    apply Subtype.ext
    apply e.injective
    exact Prod.ext (v.2.2.trans w.2.2.symm) h
  have crossImpossible {v w : Fiber} (h : res v.1 = flip (res w.1)) : False := by
    have hslice : p10_1kSpecialSlice hm (p10_1kResidualFlipVertex hm w.1 i₀) = s := by
      rw [p10_1kResidualFlipVertex_specialSlice, w.2.2]
    have hres : p10_1kResidualWord hm (p10_1kResidualFlipVertex hm w.1 i₀) = res v.1 := by
      rw [p10_1kResidualFlipVertex_residualWord]
      change flip (res w.1) = res v.1
      exact h.symm
    have hv : v.1 = p10_1kResidualFlipVertex hm w.1 i₀ := by
      apply e.injective
      exact Prod.ext (v.2.2.trans hslice.symm) hres.symm
    have hadj := p10_1kResidualFlipVertex_adjacent hm w.1 i₀
    have hdist : _root_.hammingDist w.1 (p10_1kResidualFlipVertex hm w.1 i₀) = 1 := by
      exact hadj
    have hpar := hflip w.1 (p10_1kResidualFlipVertex hm w.1 i₀) hdist
    have hPv : P v.1 := v.2.1
    rw [hv] at hPv
    have hnot : ¬ P (p10_1kResidualFlipVertex hm w.1 i₀) := by
      intro hP
      exact hpar.mp hP w.2.1
    exact hnot hPv
  let f : Fiber × Bool → Fin d → Bool := fun z =>
    if z.2 then flip (res z.1.1) else res z.1.1
  have hf : Function.Injective f := by
    rintro ⟨v, b⟩ ⟨w, c⟩ h
    cases b <;> cases c
    · exact Prod.ext (sameVertex h) rfl
    · exact (crossImpossible h).elim
    · exact (crossImpossible h.symm).elim
    · exact Prod.ext (sameVertex (hinv.injective h)) rfl
  have hcard : Fintype.card Fiber * 2 ≤ 2 ^ d := by
    calc
      Fintype.card Fiber * 2 = Fintype.card (Fiber × Bool) := by simp
      _ ≤ Fintype.card (Fin d → Bool) := Fintype.card_le_of_injective f hf
      _ = 2 ^ d := by simp
  have hpow : 2 ^ (n - m) = 2 ^ (n - m - 1) * 2 := by
    calc
      2 ^ (n - m) = 2 ^ ((n - m - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (n - m - 1) * 2 := by rw [pow_succ]
  rw [show d = n - m from rfl, hpow] at hcard
  have hresult : Fintype.card Fiber ≤ 2 ^ (n - m - 1) := by omega
  simpa [Fiber] using hresult

theorem product_update_weight_mixture {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] (q : J → A → ℝ) (j : J) (r : A → ℝ)
    (t : J → A) :
    (∏ i, Function.update q j r i (t i)) =
      ∑ a, r a * ∏ i, Function.update q j (fun b => if b = a then 1 else 0) i (t i) := by
  classical
  let R : ℝ := ∏ i ∈ Finset.univ.erase j, q i (t i)
  have hbase :
      (∏ i, Function.update q j r i (t i)) = r (t j) * R := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => (Function.update q j r i (t i))) (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Function.update_of_ne hij]
  have hpure (a : A) :
      (∏ i, Function.update q j (fun b => if b = a then 1 else 0) i (t i)) =
        (if t j = a then 1 else 0) * R := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => Function.update q j (fun b => if b = a then 1 else 0) i (t i))
      (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Function.update_of_ne hij]
  calc
    (∏ i, Function.update q j r i (t i)) = r (t j) * R := hbase
    _ = ∑ a, r a * (if t j = a then 1 else 0) * R := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_eq_single (t j)]
      · simp
      · intro a ha hne
        simp [Ne.symm hne]
      · simp
    _ = ∑ a, r a * ((if t j = a then 1 else 0) * R) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = ∑ a, r a *
        (∏ i, Function.update q j (fun b => if b = a then 1 else 0) i (t i)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hpure]

theorem expect_vector_mass_le {A : Type*} [Fintype A] {N : ℕ}
    (P : FinProb A) (f : A → Fin N → ℝ) (hf : ∀ a, ∑ x, f a x ≤ 1) :
    ∑ x, P.expect (fun a => f a x) ≤ 1 := by
  classical
  have heq : (∑ x, P.expect (fun a => f a x)) = ∑ a, P.w a * ∑ x, f a x := by
    unfold FinProb.expect
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_sum]
  rw [heq]
  calc
    (∑ a, P.w a * ∑ x, f a x) ≤ ∑ a, P.w a * 1 := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hf a) (P.nonneg a)
    _ = 1 := by simp [P.sum_eq_one]

theorem expect_vector_mass_le_of_bound {A : Type*} [Fintype A] {N : ℕ}
    (P : FinProb A) (f : A → Fin N → ℝ) (B : ℝ)
    (hf : ∀ a, ∑ x, f a x ≤ B) : ∑ x, P.expect (fun a => f a x) ≤ B := by
  classical
  have heq : (∑ x, P.expect (fun a => f a x)) = ∑ a, P.w a * ∑ x, f a x := by
    unfold FinProb.expect
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_sum]
  rw [heq]
  calc
    (∑ a, P.w a * ∑ x, f a x) ≤ ∑ a, P.w a * B := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hf a) (P.nonneg a)
    _ = B := by rw [← Finset.sum_mul, P.sum_eq_one]; ring

theorem expect_nonneg {A : Type*} [Fintype A]
    (P : FinProb A) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) : 0 ≤ P.expect f := by
  unfold FinProb.expect
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (P.nonneg a) (hf a)

/-- A finite price response gives a mixture whose coordinates are bounded by
the target vector. -/
theorem finite_mixture_le_of_price_bound {A K : Type*} [Fintype A] [Fintype K]
    (v : A → K → ℝ) (b : K → ℝ)
    (hprice : ∀ c : K → ℝ, (∀ k, 0 ≤ c k) →
      ∃ a : A, ∑ k, c k * v a k ≤ ∑ k, c k * b k) :
    ∃ w : A → ℝ, (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 ∧
      ∀ k, ∑ a, w a * v a k ≤ b k := by
  classical
  by_contra hNo
  let V := K → ℝ
  let L : (A → ℝ) →ₗ[ℝ] V := {
    toFun := fun w k => ∑ a, w a * v a k
    map_add' := by
      intro w₁ w₂
      ext k
      change (∑ a, (w₁ a + w₂ a) * v a k) =
        (∑ a, w₁ a * v a k) + ∑ a, w₂ a * v a k
      calc
        (∑ a, (w₁ a + w₂ a) * v a k) =
            ∑ a, (w₁ a * v a k + w₂ a * v a k) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = (∑ a, w₁ a * v a k) + ∑ a, w₂ a * v a k := by
          rw [Finset.sum_add_distrib]
    map_smul' := by
      intro r w
      ext k
      change (∑ a, (r * w a) * v a k) = r * (∑ a, w a * v a k)
      calc
        (∑ a, (r * w a) * v a k) = ∑ a, r * (w a * v a k) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = r * ∑ a, w a * v a k := by rw [Finset.mul_sum]
  }
  let C : Set V := L '' stdSimplex ℝ A
  let D : Set V := {z | ∀ k, z k ≤ b k}
  have hCconv : Convex ℝ C := (convex_stdSimplex ℝ A).linear_image L
  have hCcompact : IsCompact C :=
    (isCompact_stdSimplex ℝ A).image L.continuous_of_finiteDimensional
  have hDconv : Convex ℝ D := by
    intro x hx y hy r s hr hs hrs k
    change r * x k + s * y k ≤ b k
    calc
      r * x k + s * y k ≤ r * b k + s * b k := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hx k) hr)
          (mul_le_mul_of_nonneg_left (hy k) hs)
      _ = b k := by rw [← add_mul, hrs, one_mul]
  have hDclosed : IsClosed D := by
    rw [show D = ⋂ k : K, {z : V | z k ≤ b k} by ext z; simp [D]]
    exact isClosed_iInter fun k => isClosed_le (continuous_apply k) continuous_const
  have hno : ¬ ∃ w : A → ℝ, (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 ∧
      ∀ k, ∑ a, w a * v a k ≤ b k := by
    rintro ⟨w, hw0, hw1, hw⟩
    apply hNo
    refine ⟨w, hw0, hw1, ?_⟩
    intro k
    exact hw k
  have hdisj : Disjoint C D := by
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    rcases hzC with ⟨w, hw, rfl⟩
    apply hno
    refine ⟨w, hw.1, hw.2, ?_⟩
    intro k
    exact hzD k
  obtain ⟨f, u, v₀, hfC, huv, hfD⟩ :=
    geometric_hahn_banach_compact_closed hCconv hCcompact hDconv hDclosed hdisj
  let lam : K → ℝ := fun k => f (Pi.single (M := fun _ : K => ℝ) k (1 : ℝ))
  have frepr (z : V) : f z = ∑ k, z k * lam k := by
    have hdecomp : z = ∑ k, z k • Pi.single k (1 : ℝ) := by
      exact pi_eq_sum_univ' z
    calc
      f z = f (∑ k, z k • (Pi.single k (1 : ℝ))) := by rw [← hdecomp]
      _ = ∑ k, z k * lam k := by
        simp [lam, smul_eq_mul]
  have hlamnonpos (k : K) : lam k ≤ 0 := by
    by_contra hnot
    have hlampos : 0 < lam k := lt_of_not_ge hnot
    let q : ℝ := (f b - v₀) / lam k
    obtain ⟨m, hm⟩ := exists_nat_gt q
    let z : V := b - (m : ℝ) • Pi.single (M := fun _ : K => ℝ) k (1 : ℝ)
    have hzD : z ∈ D := by
      intro j
      by_cases hkj : k = j
      · subst j
        simp [z, Pi.single_eq_same]
      · have hjk : j ≠ k := Ne.symm hkj
        simp [z, Pi.single_eq_of_ne hjk]
    have hfz : f z = f b - (m : ℝ) * lam k := by
      change f (b - (m : ℝ) • Pi.single (M := fun _ : K => ℝ) k 1) = _
      rw [map_sub, map_smul]
      simp [lam, smul_eq_mul]
    have hmul : f b - v₀ < (m : ℝ) * lam k := by
      have h := (div_lt_iff₀ hlampos).mp hm
      simpa [q] using h
    have hvz := hfD z hzD
    rw [hfz] at hvz
    linarith
  let price : K → ℝ := fun k => -lam k
  have hprice' : ∀ k, 0 ≤ price k := by
    intro k
    exact neg_nonneg.mpr (hlamnonpos k)
  obtain ⟨a, ha⟩ := hprice price hprice'
  have haC : L (Pi.single a (1 : ℝ)) ∈ C := by
    exact ⟨Pi.single a (1 : ℝ), single_mem_stdSimplex ℝ a, rfl⟩
  have hfLa : f (L (Pi.single a (1 : ℝ))) < u := hfC _ haC
  have hLsingle : L (Pi.single a (1 : ℝ)) = v a := by
    funext k
    simp [L, Pi.single_apply]
  have hfLa' : f (L (Pi.single a (1 : ℝ))) =
      -∑ k, price k * v a k := by
    rw [frepr, hLsingle]
    simp [price, mul_comm]
  have hfB : v₀ < f b := hfD b (by intro k; exact le_rfl)
  have hfB' : f b = -∑ k, price k * b k := by
    rw [frepr]
    simp [price, mul_comm]
  have hstrict : f (L (Pi.single a (1 : ℝ))) < f b :=
    lt_trans hfLa (lt_trans huv hfB)
  rw [hfLa', hfB'] at hstrict
  linarith

end HypercubeRamsey.Lane_q_s10_d4
