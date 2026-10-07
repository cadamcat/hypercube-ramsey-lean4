import HypercubeRamsey.S11.Core.Slice_q_s11_slice

namespace HypercubeRamsey.Lane_q_s11_slice

open HypercubeRamsey
open HypercubeRamsey.S11.Core
open Filter
open Classical
open scoped BigOperators

noncomputable section

noncomputable def pairGateOutput_q_s11_slice {N k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] (g : ℝ)
    (μ ν : Law N) (t : Fin k → Fin N) (u : Pair I → Fin k → Fin N)
    (z : I → Fin N) : ℝ := by
  classical
  exact if ∀ a : I, Passes E G g μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a)
    then outW E G g μ ν (joinRadiusTwo_q_s11_slice t u) z else 0

theorem fixed_pair_data_tail_q_s11_slice {N k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] (g : ℝ)
    (μ ν : Law N) (y₀ : Fin N) (w : ℝ) (hw : μ.WidthLE w)
    (hg : 0 < g) (hgs : g ≤ 1 / 4)
    (hhigh : ∀ y, ν.w y ≠ 0 → 1 / 2 + 2 * g ≤ colDeg E G μ y)
    (hy₀ : ν.w y₀ ≠ 0) (hN : 0 < (N : ℝ)) (hk : 0 < (k : ℝ))
    (hmargin : Real.log 2 + w ≤ (1 / 2 : ℝ) * g * Fintype.card I)
    (u : Pair I → Fin k → Fin N) :
    ∑ z : I → Fin N,
      (∑ t : Fin k → Fin N,
        (tupLaw E G μ y₀ k).w t *
          pairGateOutput_q_s11_slice E G g μ ν t u z) *
        (if ((commonSet E G μ z).card : ℝ) <
          (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I))
        then 1 else 0) ≤
      Real.exp (-(1 / 2 : ℝ) * g * k * Fintype.card I) := by
  classical
  let T := Fin k → Fin N
  let U := Pair I → T
  let P : FinProb T := tupLaw E G μ y₀ k
  let Q (v : U) : FinProb (I → Fin N) :=
    FinProb.pi (fun a : I => deletionLaw_q_s11_slice E G μ ν y₀ v a)
  let passAll (t : T) (v : U) : Prop :=
    ∀ a, Passes E G g μ ν (ballStar (joinRadiusTwo_q_s11_slice t v) a)
  let F (t : T) (v : U) (z : I → Fin N) : ℝ :=
    if passAll t v then outW E G g μ ν (joinRadiusTwo_q_s11_slice t v) z else 0
  let m (v : U) (z : I → Fin N) : ℝ := ∑ t, P.w t * F t v z
  let H : ℝ := Fintype.card I
  let ε : ℝ := Real.exp (-(1 / 2 : ℝ) * g * k * H)
  let s : ℝ := H * ((Real.log 2 - 2 * g) * k)
  have hdeg₀ : 0 < colDeg E G μ y₀ := by
    have h := hhigh y₀ hy₀
    nlinarith [hg]
  have hρcap (x : Fin N) :
      (rhoLaw E G μ y₀).w x ≤ 2 * Real.exp w / N := by
    rw [rhoLaw, dif_pos hdeg₀]
    have hhit : hit E G x y₀ ≤ 1 := by
      unfold hit
      split_ifs <;> norm_num
    have hratio : hit E G x y₀ / colDeg E G μ y₀ ≤ 2 := by
      apply (div_le_iff₀ hdeg₀).2
      have hdegree := hhigh y₀ hy₀
      nlinarith [hhit, hdegree, hg]
    calc
      μ.w x * hit E G x y₀ / colDeg E G μ y₀ ≤ μ.w x * 2 := by
        calc
          μ.w x * hit E G x y₀ / colDeg E G μ y₀ =
              μ.w x * (hit E G x y₀ / colDeg E G μ y₀) := by ring
          _ ≤ μ.w x * 2 := mul_le_mul_of_nonneg_left hratio (μ.nonneg x)
      _ ≤ (Real.exp w / N) * 2 := mul_le_mul_of_nonneg_right (hw x) (by norm_num)
      _ = 2 * Real.exp w / N := by ring
  have hPprod (t : T) : P.w t = ∏ j : Fin k, (rhoLaw E G μ y₀).w (t j) := by
    simp [P, tupLaw, FinProb.pi]
  have hPcap (t : T) : P.w t ≤ (2 * Real.exp w / N) ^ k := by
    rw [hPprod]
    calc
      (∏ j : Fin k, (rhoLaw E G μ y₀).w (t j)) ≤
          ∏ j : Fin k, (2 * Real.exp w / N) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact (rhoLaw E G μ y₀).nonneg (t j)
        · intro j hj
          exact hρcap (t j)
      _ = (2 * Real.exp w / N) ^ k := by
        rw [Finset.prod_const]
        simp only [Finset.card_univ, Fintype.card_fin]
  have hrowNonneg (v : U) (t : T) (a : I) (y : Fin N) :
      0 ≤ oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
        (ballStar (joinRadiusTwo_q_s11_slice t v) a) y :=
    oddRowW_nonneg_q_s11_slice E G g μ ν (ballStar (joinRadiusTwo_q_s11_slice t v) a) y
  have houtNonneg (v : U) (t : T) (z : I → Fin N) :
      0 ≤ outW E G g μ ν (joinRadiusTwo_q_s11_slice t v) z := by
    unfold outW
    apply Finset.prod_nonneg
    intro a ha
    exact hrowNonneg v t a (z a)
  have hFnonneg (t : T) (v : U) (z : I → Fin N) : 0 ≤ F t v z := by
    dsimp [F]
    split_ifs
    · exact houtNonneg v t z
    · exact le_rfl
  have hQdom (t : T) (v : U) (z : I → Fin N) :
      F t v z ≤ Real.exp (s) * (Q v).w z := by
    by_cases hp : passAll t v
    · have hrowBound (a : I) :
          oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
            (ballStar (joinRadiusTwo_q_s11_slice t v) a) (z a) ≤
          Real.exp ((Real.log 2 - 2 * g) * k) *
            (deletionLaw_q_s11_slice E G μ ν y₀ v a).w (z a) := by
        exact oddRow_le_deletion_q_s11_slice E G g μ ν y₀ hg hgs hhigh
          t v a (hp a) (z a)
      have hprod :
          outW E G g μ ν (joinRadiusTwo_q_s11_slice t v) z ≤
            ∏ a : I, Real.exp ((Real.log 2 - 2 * g) * k) *
              (deletionLaw_q_s11_slice E G μ ν y₀ v a).w (z a) := by
        unfold outW
        apply Finset.prod_le_prod₀
        · intro a ha
          exact hrowNonneg v t a (z a)
        · intro a ha
          exact hrowBound a
      have hcprod :
          (∏ a : I, Real.exp ((Real.log 2 - 2 * g) * k)) = Real.exp s := by
        calc
          (∏ a : I, Real.exp ((Real.log 2 - 2 * g) * k)) =
              Real.exp ((Real.log 2 - 2 * g) * k) ^ Fintype.card I := by simp
          _ = Real.exp ((Fintype.card I : ℝ) * ((Real.log 2 - 2 * g) * k)) :=
            (Real.exp_nat_mul ((Real.log 2 - 2 * g) * k) (Fintype.card I)).symm
          _ = Real.exp s := by simp [s, H]
      calc
        F t v z = outW E G g μ ν (joinRadiusTwo_q_s11_slice t v) z := by simp [F, hp]
        _ ≤ ∏ a : I, Real.exp ((Real.log 2 - 2 * g) * k) *
            (deletionLaw_q_s11_slice E G μ ν y₀ v a).w (z a) := hprod
        _ = (∏ a : I, Real.exp ((Real.log 2 - 2 * g) * k)) *
            (∏ a : I, (deletionLaw_q_s11_slice E G μ ν y₀ v a).w (z a)) := by
              exact Finset.prod_mul_distrib
        _ = Real.exp s * (Q v).w z := by simp [Q, FinProb.pi, hcprod]
    · simp [F, hp]
      exact mul_nonneg (Real.exp_nonneg _) ((Q v).nonneg z)
  have hε : 0 < ε := by positivity
  have hMnonneg (v : U) (z : I → Fin N) : 0 ≤ m v z := by
    dsimp [m]
    apply Finset.sum_nonneg
    intro t ht
    exact mul_nonneg (P.nonneg t) (hFnonneg t v z)
  have hgp (v : U) :=
    HypercubeRamsey.gated_posterior P (fun t z => F t v z)
      (fun t z => hFnonneg t v z) (Q v) ε s hε
  have hbadmass (v : U) :
      (∑ z : I → Fin N,
        if m v z < ε * (Q v).w z ∨ m v z = 0 then m v z else 0) ≤ ε := by
    simpa [m] using (hgp v).1
  have hPostSum (v : U) (z : I → Fin N)
      (hgood : ¬ (m v z < ε * (Q v).w z ∨ m v z = 0)) :
      (∑ t : T, P.w t * F t v z / m v z) = 1 := by
    have hmne : m v z ≠ 0 := by
      intro hm
      exact hgood (Or.inr hm)
    rw [← Finset.sum_div]
    change (∑ t : T, P.w t * F t v z) / m v z = 1
    rw [show (∑ t : T, P.w t * F t v z) = m v z by rfl]
    exact div_self hmne
  have hPostCap (v : U) (z : I → Fin N)
      (hgood : ¬ (m v z < ε * (Q v).w z ∨ m v z = 0)) (t : T) :
      P.w t * F t v z / m v z ≤ Real.exp s * ε⁻¹ * P.w t := by
    have hdomV : ∀ t : T, ∀ z : I → Fin N,
        F t v z ≤ Real.exp s * (Q v).w z := fun t z => hQdom t v z
    exact (hgp v).2.1 hdomV z hgood t
  have hNoGoodSmall (v : U) (z : I → Fin N)
      (hgood : ¬ (m v z < ε * (Q v).w z ∨ m v z = 0))
      (hsmall : ((commonSet E G μ z).card : ℝ) <
        (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I))) : False := by
    let C := commonSet E G μ z
    let post (t : T) := P.w t * F t v z / m v z
    let M : ℝ := Real.exp s * ε⁻¹ * (2 * Real.exp w / N) ^ k
    have hmpos : 0 < m v z := by
      apply lt_of_le_of_ne (hMnonneg v z)
      intro hm
      exact hgood (Or.inr hm.symm)
    have hMpos : 0 ≤ M := by dsimp [M]; positivity
    have hpostCap (t : T) : post t ≤ M := by
      dsimp [post, M]
      calc
        P.w t * F t v z / m v z ≤ Real.exp s * ε⁻¹ * P.w t :=
          hPostCap v z hgood t
        _ ≤ Real.exp s * ε⁻¹ * (2 * Real.exp w / N) ^ k := by
          apply mul_le_mul_of_nonneg_left (hPcap t)
          positivity
    have hpostSupport (t : T) (ht : post t ≠ 0) : ∀ j, t j ∈ C := by
      have hpostPos : 0 < post t := by
        apply lt_of_le_of_ne (div_nonneg
          (mul_nonneg (P.nonneg t) (hFnonneg t v z)) hmpos.le)
        exact Ne.symm ht
      have hnumEq : post t * m v z = P.w t * F t v z := by
        dsimp [post]
        exact div_mul_cancel₀ _ hmpos.ne'
      have hnumPos : 0 < P.w t * F t v z := by
        rw [← hnumEq]
        exact mul_pos hpostPos hmpos
      have hPpos : 0 < P.w t := by
        by_contra h
        have hzero : P.w t = 0 := le_antisymm (le_of_not_gt h) (P.nonneg t)
        rw [hzero, zero_mul] at hnumPos
        exact (lt_irrefl _ hnumPos)
      have hFpos : 0 < F t v z := by
        by_contra h
        have hzero : F t v z = 0 := le_antisymm (le_of_not_gt h) (hFnonneg t v z)
        rw [hzero, mul_zero] at hnumPos
        exact (lt_irrefl _ hnumPos)
      have hpass : passAll t v := by
        by_contra hnot
        simp [F, hnot] at hFpos
      have houtPos : 0 < outW E G g μ ν (joinRadiusTwo_q_s11_slice t v) z := by
        simpa [F, hpass] using hFpos
      have hrowNe (a : I) :
          oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
            (ballStar (joinRadiusTwo_q_s11_slice t v) a) (z a) ≠ 0 := by
        intro hzero
        have hprod0 :
            (∏ b : I, oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
              (ballStar (joinRadiusTwo_q_s11_slice t v) b) (z b)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ a) hzero
        have hOut0 : outW E G g μ ν (joinRadiusTwo_q_s11_slice t v) z = 0 := by
          simpa [outW] using hprod0
        rw [hOut0] at houtPos
        exact (lt_irrefl _ houtPos)
      have hrowPos (a : I) :
          0 < oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
            (ballStar (joinRadiusTwo_q_s11_slice t v) a) (z a) :=
        lt_of_le_of_ne (hrowNonneg v t a (z a)) (Ne.symm (hrowNe a))
      have hdegree₀ : 0 < colDeg E G μ y₀ := by
        have h := hhigh y₀ hy₀
        nlinarith [hg]
      have hρProd :
          (∏ j : Fin k, (rhoLaw E G μ y₀).w (t j)) ≠ 0 := by
        have hPne : P.w t ≠ 0 := ne_of_gt hPpos
        simpa [P, tupLaw, FinProb.pi] using hPne
      have hρne (j : Fin k) : (rhoLaw E G μ y₀).w (t j) ≠ 0 := by
        exact (Finset.prod_ne_zero_iff.mp hρProd) j (Finset.mem_univ j)
      have hμne (j : Fin k) : μ.w (t j) ≠ 0 := by
        intro hzero
        have h := hρne j
        simp [rhoLaw, hdegree₀, hzero] at h
      intro j
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hμne j, ?_⟩
      intro a
      have hrowFormula :
          oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
            (ballStar (joinRadiusTwo_q_s11_slice t v) a) (z a) =
            ν.w (z a) * lik E G μ (ballStar (joinRadiusTwo_q_s11_slice t v) a) (z a) /
              normZ E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t v) a) := by
        simp [oddRowW, hpass a]
      have hnumPos : 0 < ν.w (z a) *
          lik E G μ (ballStar (joinRadiusTwo_q_s11_slice t v) a) (z a) := by
        have hmul := mul_pos (hrowPos a) (hpass a).1
        rw [hrowFormula] at hmul
        have hcancel := div_mul_cancel₀
          (ν.w (z a) * lik E G μ (ballStar (joinRadiusTwo_q_s11_slice t v) a) (z a))
          (hpass a).1.ne'
        simpa [hcancel] using hmul
      have hlikNe : lik E G μ
          (ballStar (joinRadiusTwo_q_s11_slice t v) a) (z a) ≠ 0 := by
        intro hzero
        rw [hzero, mul_zero] at hnumPos
        exact (lt_irrefl _ hnumPos)
      exact hit_center_of_lik_ne_zero_q_s11_slice E G μ t v a (z a) hlikNe j
    have hpostSum := hPostSum v z hgood
    have hcount := supported_function_mass_card_bound_q_s11_slice C post M hpostSum
      (fun t ht => by
        by_contra hne
        exact ht (hpostSupport t hne)) hpostCap hMpos
    have hkpos : k ≠ 0 := by exact_mod_cast (ne_of_gt hk)
    have hratioPos : 0 < 2 * Real.exp w / N := by positivity
    have hratioBase :
        (C.card : ℝ) * (2 * Real.exp w / N) <
          Real.exp (Real.log 2 + w - (Real.log 2 - g / 2) * Fintype.card I) := by
      have hcutMul := mul_lt_mul_of_pos_right hsmall hratioPos
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN
      have htwo : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      have hcancel : (N : ℝ) * (2 * Real.exp w / N) = 2 * Real.exp w := by
        field_simp [hNne]
      calc
        (C.card : ℝ) * (2 * Real.exp w / N) <
            (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) *
              (2 * Real.exp w / N) := hcutMul
        _ = Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) *
            ((N : ℝ) * (2 * Real.exp w / N)) := by ring
        _ = Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) *
            (2 * Real.exp w) := by rw [hcancel]
        _ = Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) *
            Real.exp (Real.log 2) * Real.exp w := by
          have htwoMul : 2 * Real.exp w = Real.exp (Real.log 2) * Real.exp w :=
            congrArg (fun x : ℝ => x * Real.exp w) htwo
          calc
            _ = Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) *
                (Real.exp (Real.log 2) * Real.exp w) :=
              congrArg (fun x : ℝ =>
                Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) * x) htwoMul
            _ = _ := by ring
        _ = Real.exp (Real.log 2 + w - (Real.log 2 - g / 2) * Fintype.card I) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1 <;> ring
    have hpowStrict :
        ((C.card : ℝ) * (2 * Real.exp w / N)) ^ k <
          Real.exp (Real.log 2 + w - (Real.log 2 - g / 2) * Fintype.card I) ^ k :=
      pow_lt_pow_left₀ hratioBase (by positivity) hkpos
    have hepsInv : ε⁻¹ = Real.exp ((1 / 2 : ℝ) * g * k * H) := by
      simp [ε, Real.exp_neg]
    have htotalLe :
        s + (1 / 2 : ℝ) * g * k * H +
          (Real.log 2 + w - (Real.log 2 - g / 2) * Fintype.card I) * k ≤ 0 := by
      have hcoeff : Real.log 2 + w - g * Fintype.card I ≤ 0 := by
        have hgh : 0 ≤ g * (Fintype.card I : ℝ) :=
          mul_nonneg hg.le (Nat.cast_nonneg _)
        nlinarith [hmargin, hgh]
      calc
        s + (1 / 2 : ℝ) * g * k * H +
            (Real.log 2 + w - (Real.log 2 - g / 2) * Fintype.card I) * k =
            (Real.log 2 + w - g * H) * k := by dsimp [s, H]; ring
        _ ≤ 0 := by
          have hnonneg : 0 ≤ -(Real.log 2 + w - g * H) * (k : ℝ) :=
            mul_nonneg (by linarith [hcoeff]) (Nat.cast_nonneg k)
          nlinarith [hnonneg]
    have hconclusion : (C.card : ℝ) ^ k * M < 1 := by
      dsimp [M]
      calc
        (C.card : ℝ) ^ k *
            (Real.exp s * ε⁻¹ * (2 * Real.exp w / N) ^ k) =
            Real.exp s * ε⁻¹ * ((C.card : ℝ) * (2 * Real.exp w / N)) ^ k := by
          calc
            (C.card : ℝ) ^ k *
                (Real.exp s * ε⁻¹ * (2 * Real.exp w / N) ^ k) =
              Real.exp s * ε⁻¹ *
                ((C.card : ℝ) ^ k * (2 * Real.exp w / N) ^ k) := by ring
            _ = Real.exp s * ε⁻¹ *
                ((C.card : ℝ) * (2 * Real.exp w / N)) ^ k := by rw [← mul_pow]
        _ < Real.exp s * ε⁻¹ *
              Real.exp (Real.log 2 + w - (Real.log 2 - g / 2) * Fintype.card I) ^ k :=
          mul_lt_mul_of_pos_left hpowStrict (mul_pos (Real.exp_pos _) (inv_pos.mpr hε))
        _ = Real.exp (s + (1 / 2 : ℝ) * g * k * H +
              (Real.log 2 + w - (Real.log 2 - g / 2) * Fintype.card I) * k) := by
          rw [hepsInv]
          rw [← Real.exp_nat_mul]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1 <;> ring
        _ ≤ 1 := (Real.exp_le_one_iff).2 htotalLe
    linarith
  have hTail :
      (∑ z : I → Fin N,
        m u z * (if ((commonSet E G μ z).card : ℝ) <
          (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I))
          then 1 else 0)) ≤ ε := by
    have hpoint (z : I → Fin N) :
        m u z * (if ((commonSet E G μ z).card : ℝ) <
          (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I))
          then 1 else 0) ≤
        (if m u z < ε * (Q u).w z ∨ m u z = 0 then m u z else 0) := by
      by_cases hs : ((commonSet E G μ z).card : ℝ) <
          (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I))
      · by_cases hb : m u z < ε * (Q u).w z ∨ m u z = 0
        · simp [hs, hb]
        · have hfalse := hNoGoodSmall u z hb hs
          exact (False.elim hfalse)
      · by_cases hb : m u z < ε * (Q u).w z ∨ m u z = 0 <;>
          simp [hs, hb, hMnonneg]
    calc
      (∑ z : I → Fin N,
        m u z * (if ((commonSet E G μ z).card : ℝ) <
          (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I))
          then 1 else 0)) ≤
          ∑ z, if m u z < ε * (Q u).w z ∨ m u z = 0 then m u z else 0 := by
            apply Finset.sum_le_sum
            intro z hz
            exact hpoint z
      _ ≤ ε := hbadmass u
  simpa [m, F, P, passAll, ε, H, pairGateOutput_q_s11_slice,
    joinRadiusTwo_q_s11_slice] using hTail

end

end HypercubeRamsey.Lane_q_s11_slice
