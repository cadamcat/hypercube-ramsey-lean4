import HypercubeRamsey.Framework.Law
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.StdSimplex
import FixedPointTheorems.kakutani

/-!
# Lemma 3.3: balanced mixtures and simultaneous profiles

Source: `sections/03-…tex`, Lemma 3.3 and its proof (separation for the first assertion, Kakutani's theorem for
the second).
-/

namespace HypercubeRamsey

/-- Lemma 3.3, first assertion, at one dimension: a finite menu of law pairs that survives every removal of at
most `κ N` labels per side has a mixture with all expected atoms at most `4 / (κ N)`. -/
theorem balanced_mixture {N : ℕ} (hN : 0 < N) {ι : Type*} [Fintype ι]
    (μ ν : ι → Law N) (κ : ℝ) (hκ : 0 < κ)
    (havail : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
      ∃ i, (∀ x ∈ RX, (μ i).w x = 0) ∧ (∀ y ∈ RY, (ν i).w y = 0)) :
    ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧
      (∀ x, ∑ i, t i * (μ i).w x ≤ 4 / (κ * N)) ∧
      (∀ y, ∑ i, t i * (ν i).w y ≤ 4 / (κ * N)) := by
  classical
  let M : ℝ := κ * (N : ℝ)
  have hM : 0 < M := mul_pos hκ (by exact_mod_cast hN)
  let C : ℝ := 4 / M
  have hC : 0 < C := div_pos (by norm_num) hM
  by_contra hNo
  let S := Sum (Fin N) (Fin N)
  let V := S → ℝ
  let p : ι → V := fun i => Sum.elim (μ i).w (ν i).w
  let L : (ι → ℝ) →ₗ[ℝ] V := {
    toFun := fun t s => ∑ i, t i * p i s
    map_add' := by
      intro a b
      ext s
      change (∑ i, (a i + b i) * p i s) =
        (∑ i, a i * p i s) + ∑ i, b i * p i s
      calc
        (∑ i, (a i + b i) * p i s) = ∑ i, (a i * p i s + b i * p i s) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i, a i * p i s) + ∑ i, b i * p i s := by rw [Finset.sum_add_distrib]
    map_smul' := by
      intro c a
      ext s
      change (∑ i, c * a i * p i s) = c * (∑ i, a i * p i s)
      calc
        (∑ i, c * a i * p i s) = ∑ i, c * (a i * p i s) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = c * ∑ i, a i * p i s := by rw [Finset.mul_sum]
  }
  let K : Set V := L '' stdSimplex ℝ ι
  let D : Set V := {z | ∀ s, z s ≤ C}
  have hKconv : Convex ℝ K := by
    exact (convex_stdSimplex ℝ ι).linear_image L
  have hKcompact : IsCompact K := by
    exact (isCompact_stdSimplex ℝ ι).image L.continuous_of_finiteDimensional
  have hDconv : Convex ℝ D := by
    intro x hx y hy a b ha hb hab
    intro s
    change a * x s + b * y s ≤ C
    nlinarith [hx s, hy s]
  have hDclosed : IsClosed D := by
    rw [show D = ⋂ s : S, {z : V | z s ≤ C} by ext z; simp [D]]
    exact isClosed_iInter fun s => isClosed_le (continuous_apply s) continuous_const
  have hno : ¬ ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧
      (∀ x, ∑ i, t i * (μ i).w x ≤ C) ∧
      (∀ y, ∑ i, t i * (ν i).w y ≤ C) := by
    rintro ⟨t, ht0, ht1, htX, htY⟩
    apply hNo
    refine ⟨t, ht0, ht1, ?_, ?_⟩
    · intro x
      simpa [C, M] using htX x
    · intro y
      simpa [C, M] using htY y
  have hdisj : Disjoint K D := by
    apply Set.disjoint_left.mpr
    intro z hzK hzD
    rcases hzK with ⟨t, ht, rfl⟩
    apply hno
    refine ⟨t, ht.1, ht.2, ?_, ?_⟩
    · intro x
      simpa [L, p] using hzD (Sum.inl x)
    · intro y
      simpa [L, p] using hzD (Sum.inr y)
  obtain ⟨f, u, v, hfK, huv, hfD⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcompact hDconv hDclosed hdisj
  let lam : S → ℝ := fun s => f (fun j => if s = j then (1 : ℝ) else 0)
  have frepr (z : V) : f z = ∑ s, z s * lam s := by
    calc
      f z = f (∑ s, z s • (fun j => if s = j then (1 : ℝ) else 0)) := by
        congr 1
        exact pi_eq_sum_univ z
      _ = ∑ s, z s * lam s := by simp [lam, smul_eq_mul]
  let price : S → ℝ := fun s => -lam s
  have hprice : ∀ s, 0 ≤ price s := by
    intro s
    by_contra hnot
    have hpos : 0 < lam s := by
      dsimp [price] at hnot
      linarith
    let q : ℝ := (f (fun _ => C) - v) / lam s
    obtain ⟨n, hn⟩ := exists_nat_gt q
    let z : V := fun k => C - (n : ℝ) * (if s = k then 1 else 0)
    have hz : z ∈ D := by
      intro k
      by_cases hk : s = k
      · simp [z, hk]
      · simp [z, hk]
    have hzeq : z = (fun _ : S => C) - (n : ℝ) • (fun k => if s = k then (1 : ℝ) else 0) := by
      funext k
      by_cases hk : s = k
      · subst k
        simp [z]
      · simp [z, hk]
    have hfz : f z = f (fun _ : S => C) - (n : ℝ) * lam s := by
      rw [hzeq, map_sub, map_smul]
      simp [lam, smul_eq_mul]
    have hmul : f (fun _ => C) - v < (n : ℝ) * lam s := by
      have h := (div_lt_iff₀ hpos).mp hn
      simpa [q] using h
    have := hfD z hz
    rw [hfz] at this
    linarith
  let P : ℝ := ∑ s, price s
  have hPnonneg : 0 ≤ P := by
    apply Finset.sum_nonneg
    intro s hs
    exact hprice s
  have htotal : P = (∑ x, price (Sum.inl x)) + (∑ y, price (Sum.inr y)) := by
    dsimp [P]
    rw [Fintype.sum_sum_type]
  have hcard_bound : ∀ η : Fin N → ℝ, (∀ x, 0 ≤ η x) → (∑ x, η x ≤ P) →
      ((Finset.univ.filter fun x => η x > 2 * P / M).card : ℝ) ≤ M := by
    intro η hη hηsum
    let H := Finset.univ.filter fun x => η x > 2 * P / M
    have hprod : (H.card : ℝ) * (2 * P / M) ≤ P := by
      calc
        (H.card : ℝ) * (2 * P / M) = ∑ x ∈ H, (2 * P / M) := by
          simp [H, Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ H, η x := by
          apply Finset.sum_le_sum
          intro x hx
          exact le_of_lt (Finset.mem_filter.mp hx).2
        _ ≤ ∑ x, η x := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
            (by intro x hx hnot; exact hη x)
        _ ≤ P := hηsum
    by_cases hPpos : 0 < P
    · have ha : 0 < 2 * P / M := div_pos (by positivity) hM
      have hdiv : (H.card : ℝ) ≤ P / (2 * P / M) := (le_div_iff₀ ha).2 hprod
      have heq : P / (2 * P / M) = M / 2 := by
        field_simp
      rw [heq] at hdiv
      linarith [hM]
    · have hPzero : P = 0 := le_antisymm (not_lt.mp hPpos) hPnonneg
      have hηzero : ∀ x, η x = 0 := by
        intro x
        have hle : η x ≤ P := by
          calc
            η x ≤ ∑ y, η y := Finset.single_le_sum (fun y hy => hη y) (Finset.mem_univ x)
            _ ≤ P := hηsum
        linarith [hη x]
      have hHempty : H = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        rw [hηzero x, hPzero] at hx'
        norm_num at hx'
      simpa [H, hHempty] using le_of_lt hM
  let RX : Finset (Fin N) := Finset.univ.filter fun x => price (Sum.inl x) > 2 * P / M
  let RY : Finset (Fin N) := Finset.univ.filter fun y => price (Sum.inr y) > 2 * P / M
  have hRX : (RX.card : ℝ) ≤ M := by
    simpa [RX] using hcard_bound (fun x => price (Sum.inl x)) (fun x => hprice _) (by
      rw [htotal]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun y hy => hprice _))
  have hRY : (RY.card : ℝ) ≤ M := by
    simpa [RY] using hcard_bound (fun y => price (Sum.inr y)) (fun y => hprice _) (by
      rw [htotal]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun x hx => hprice _))
  have hRXavail : (RX.card : ℝ) ≤ κ * N := by simpa [M] using hRX
  have hRYavail : (RY.card : ℝ) ≤ κ * N := by simpa [M] using hRY
  obtain ⟨i, hiX, hiY⟩ := havail RX RY hRXavail hRYavail
  let a : ℝ := 2 * P / M
  have ha : 0 ≤ a := div_nonneg (by positivity) (le_of_lt hM)
  have hμcost : ∑ x, (μ i).w x * price (Sum.inl x) ≤ a := by
    calc
      ∑ x, (μ i).w x * price (Sum.inl x) ≤ ∑ x, (μ i).w x * a := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hxR : x ∈ RX
        · rw [hiX x hxR]
          simp
        · have hle : price (Sum.inl x) ≤ a := by
            apply le_of_not_gt
            intro hgt
            exact hxR (Finset.mem_filter.mpr ⟨Finset.mem_univ x, by simpa [a] using hgt⟩)
          exact mul_le_mul_of_nonneg_left hle ((μ i).nonneg x)
      _ = a := by
        rw [← Finset.sum_mul, (μ i).sum_eq_one]
        simp
  have hνcost : ∑ y, (ν i).w y * price (Sum.inr y) ≤ a := by
    calc
      ∑ y, (ν i).w y * price (Sum.inr y) ≤ ∑ y, (ν i).w y * a := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hyR : y ∈ RY
        · rw [hiY y hyR]
          simp
        · have hle : price (Sum.inr y) ≤ a := by
            apply le_of_not_gt
            intro hgt
            exact hyR (Finset.mem_filter.mpr ⟨Finset.mem_univ y, by simpa [a] using hgt⟩)
          exact mul_le_mul_of_nonneg_left hle ((ν i).nonneg y)
      _ = a := by
        rw [← Finset.sum_mul, (ν i).sum_eq_one]
        simp
  have hcost : ∑ s, price s * p i s ≤ C * P := by
    calc
      ∑ s, price s * p i s =
          (∑ x, (μ i).w x * price (Sum.inl x)) +
            (∑ y, (ν i).w y * price (Sum.inr y)) := by
        rw [Fintype.sum_sum_type]
        simp [p, mul_comm]
      _ ≤ a + a := add_le_add hμcost hνcost
      _ = C * P := by dsimp [a, C, M]; ring
  have hpiK : p i ∈ K := by
    refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
    funext s
    simp [L, p, Pi.single_apply]
  have hfpi : f (p i) < u := hfK (p i) hpiK
  have hfpi_eq : f (p i) = -∑ s, price s * p i s := by
    rw [frepr]
    have hlam : ∀ s, lam s = -price s := by intro s; simp [price]
    simp_rw [hlam, mul_neg]
    rw [Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hfc : v < -C * P := by
    have h := hfD (fun _ => C) (by intro s; exact le_rfl)
    have heq : f (fun _ => C) = -C * P := by
      have hsumLam : (∑ s, lam s) = -P := by
        dsimp [P, price]
        rw [Finset.sum_neg_distrib]
        ring
      calc
        f (fun _ => C) = ∑ s, C * lam s := by rw [frepr]
        _ = C * ∑ s, lam s := by rw [← Finset.mul_sum]
        _ = -C * P := by rw [hsumLam]; ring
    rw [heq] at h
    exact h
  have hsep : C * P < ∑ s, price s * p i s := by
    have hcp : C * P < -v := by linarith [hfc]
    have hmiddle : -v < -u := by linarith [huv]
    have hlast : -u < ∑ s, price s * p i s := by
      have h := hfpi
      rw [hfpi_eq] at h
      linarith
    linarith
  exact (not_lt_of_ge hcost) hsep

/-- Lemma 3.3, second assertion: finitely many players with finite action sets; player `j`'s expected output
vector, under independent profiles, can be pushed below `b j` by a best response to any profiles of the others.
Then one profile meets every bound simultaneously. -/
theorem simultaneous_profiles {J : Type*} [Fintype J] [DecidableEq J]
    {A : J → Type*} [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)]
    {m : J → ℕ} (X : ∀ j, (∀ i, A i) → Fin (m j) → ℝ) (b : ∀ j, Fin (m j) → ℝ)
    (hresp : ∀ j (q : ∀ i, A i → ℝ), (∀ i a, 0 ≤ q i a) → (∀ i, ∑ a, q i a = 1) →
      ∃ qj : A j → ℝ, (∀ a, 0 ≤ qj a) ∧ ∑ a, qj a = 1 ∧
        ∀ r, ∑ σ : (∀ i, A i), (∏ i, (Function.update q j qj) i (σ i)) * X j σ r ≤ b j r) :
    ∃ q : ∀ i, A i → ℝ, (∀ i a, 0 ≤ q i a) ∧ (∀ i, ∑ a, q i a = 1) ∧
      ∀ j r, ∑ σ : (∀ i, A i), (∏ i, q i (σ i)) * X j σ r ≤ b j r := by
  classical
  let V := ∀ i, A i → ℝ
  let S : Set V := {q | ∀ i, q i ∈ stdSimplex ℝ (A i)}
  have hSconv : Convex ℝ S := by
    intro q hq p hp a c ha hc hac i
    exact convex_stdSimplex ℝ (A i) (hq i) (hp i) ha hc hac
  have hScompact : IsCompact S := by
    change IsCompact {q : V | ∀ i, q i ∈ stdSimplex ℝ (A i)}
    exact isCompact_pi_infinite fun i => isCompact_stdSimplex ℝ (A i)
  have hSclosed : IsClosed S := by
    have hEq : S = ⋂ i, {q : V | q i ∈ stdSimplex ℝ (A i)} := by
      ext q
      simp [S]
    rw [hEq]
    exact isClosed_iInter fun i =>
      (isClosed_stdSimplex ℝ (A i)).preimage (continuous_apply i)
  have hSne : S.Nonempty := by
    refine ⟨fun i => Pi.single (Classical.choice (inferInstance : Nonempty (A i))) 1, ?_⟩
    intro i
    exact single_mem_stdSimplex ℝ _
  let payoff (q : V) (j : J) (qj : A j → ℝ) (r : Fin (m j)) : ℝ :=
    ∑ σ : (∀ i, A i),
      (∏ i, (Function.update q j qj) i (σ i)) * X j σ r
  have hprod_affine (q : V) (j : J) (qj qk : A j → ℝ) (a c : ℝ)
      (σ : ∀ i, A i) :
      (∏ i, (Function.update q j (fun x => a * qj x + c * qk x)) i (σ i)) =
        a * (∏ i, (Function.update q j qj) i (σ i)) +
          c * (∏ i, (Function.update q j qk) i (σ i)) := by
    let R : ℝ := ∏ i ∈ (Finset.univ.erase j), q i (σ i)
    have hfact (g : A j → ℝ) :
        (∏ i, (Function.update q j g) i (σ i)) = g (σ j) * R := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => (Function.update q j g) i (σ i)) (Finset.mem_univ j)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [Function.update_of_ne hij]
    rw [hfact (fun x => a * qj x + c * qk x), hfact qj, hfact qk]
    ring
  have hpayoff_affine (q : V) (j : J) (qj qk : A j → ℝ) (a c : ℝ)
      (r : Fin (m j)) :
      payoff q j (fun x => a * qj x + c * qk x) r =
        a * payoff q j qj r + c * payoff q j qk r := by
    unfold payoff
    calc
      (∑ σ : (∀ i, A i),
          (∏ i, (Function.update q j (fun x => a * qj x + c * qk x)) i (σ i)) * X j σ r) =
        ∑ σ, (a * (∏ i, (Function.update q j qj) i (σ i)) +
          c * (∏ i, (Function.update q j qk) i (σ i))) * X j σ r := by
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [hprod_affine]
      _ = (∑ σ, a * ((∏ i, (Function.update q j qj) i (σ i)) * X j σ r)) +
          ∑ σ, c * ((∏ i, (Function.update q j qk) i (σ i)) * X j σ r) := by
            calc
              _ = ∑ σ, (a * ((∏ i, (Function.update q j qj) i (σ i)) * X j σ r) +
                    c * ((∏ i, (Function.update q j qk) i (σ i)) * X j σ r)) := by
                apply Finset.sum_congr rfl
                intro σ hσ
                ring
              _ = _ := by rw [Finset.sum_add_distrib]
      _ = a * (∑ σ, (∏ i, (Function.update q j qj) i (σ i)) * X j σ r) +
          c * (∑ σ, (∏ i, (Function.update q j qk) i (σ i)) * X j σ r) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
  let response : S → Set V := fun q =>
    {z | z ∈ S ∧ ∀ j r, payoff q.1 j (z j) r ≤ b j r}
  have hresponse_subset : ∀ q : S, response q ⊆ S := by
    intro q z hz
    exact hz.1
  have hresponse_convex : ∀ q : S, Convex ℝ (response q) := by
    intro q x hx y hy a c ha hc hac
    refine ⟨hSconv hx.1 hy.1 ha hc hac, ?_⟩
    intro j r
    have hmix : (a • x + c • y) j = fun t => a * x j t + c * y j t := by
      funext t
      rfl
    rw [hmix, hpayoff_affine]
    calc
      a * payoff q.1 j (x j) r + c * payoff q.1 j (y j) r ≤
          a * b j r + c * b j r := add_le_add
            (mul_le_mul_of_nonneg_left (hx.2 j r) ha)
            (mul_le_mul_of_nonneg_left (hy.2 j r) hc)
      _ = b j r := by
        calc
          a * b j r + c * b j r = (a + c) * b j r := by ring
          _ = b j r := by rw [hac]; ring
  have hresponse_nonempty : ∀ q : S, (response q).Nonempty := by
    intro q
    have hnonneg : ∀ i a, 0 ≤ q.1 i a := fun i a => (q.2 i).1 a
    have hsum : ∀ i, ∑ a, q.1 i a = 1 := fun i => (q.2 i).2
    let resp : ∀ j, A j → ℝ := fun j => Classical.choose (hresp j q.1 hnonneg hsum)
    have hspec (j : J) := Classical.choose_spec (hresp j q.1 hnonneg hsum)
    refine ⟨resp, ?_, ?_⟩
    · intro j
      exact ⟨(hspec j).1, (hspec j).2.1⟩
    · intro j r
      simpa [payoff, resp] using (hspec j).2.2 r
  have hresponse_graph_cont (j : J) (r : Fin (m j)) :
      Continuous (fun z : S × V => payoff z.1.1 j (z.2 j) r) := by
    unfold payoff
    fun_prop
  have hgraph : closedGraph response := by
    rw [closedGraph]
    rw [show {z : S × V | z.2 ∈ response z.1} =
      {z | z.2 ∈ S} ∩ ⋂ j, ⋂ r : Fin (m j),
        {z : S × V | payoff z.1.1 j (z.2 j) r ≤ b j r} by
      ext z
      simp [response]]
    apply IsClosed.inter
    · exact hSclosed.preimage continuous_snd
    · apply isClosed_iInter
      intro j
      apply isClosed_iInter
      intro r
      exact isClosed_le (hresponse_graph_cont j r) continuous_const
  have h1 : ∀ q : S, response q ⊆ S ∧ Convex ℝ (response q) ∧ (response q).Nonempty := by
    intro q
    exact ⟨hresponse_subset q, hresponse_convex q, hresponse_nonempty q⟩
  obtain ⟨q, hq⟩ := kakutani_fixed_point S hSconv hScompact hSne response hgraph h1
  refine ⟨q.1, ?_, ?_, ?_⟩
  · intro i a
    exact (q.2 i).1 a
  · intro i
    exact (q.2 i).2
  · intro j r
    have h := hq.2 j r
    simpa [payoff, Function.update_eq_self] using h

end HypercubeRamsey
