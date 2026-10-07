import HypercubeRamsey.S08.L81.Grid
import HypercubeRamsey.S08.L81.Prelude
import HypercubeRamsey.Framework.LawLemmas

/-!
# Lemma 8.1, Step 1: trimming to nearly constant survival

Source: `sections/08-…tex`, lines 23–46; blueprint L8.1b.

`excMass x = Λ{i : |d_G(x, ν_i) - 1/2| > 2n^{-η}}`; the dropped set `D` is the set of `x ∈ X` with
`excMass x > e^{-n^η/2}`; the kept tags are those with `μ_i(D) ≤ 1/2`; the trimmed mixture restricts the tag law to
the kept tags and each first law to `Dᶜ`, both normalized (08:31–39).  The trimmed data, together with the fixed
exponents and the tuple length `h`, form the context `Ctx` used by every later step; `Std` records what Step 1
delivers about it.
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey Filter
open scoped BigOperators

/-- The one-shot hypotheses of Lemma 8.1 at one dimension (`asymmetric_purity`), with the large regime reduced
to `N ≤ n 2^n`. -/
structure Input (η₀ γ β p K : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (G : Colour) (M : TagMix N) : Prop where
  size : N ≤ n * 2 ^ n
  disc : DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀))
  bal : M.Balanced K
  laws : ∀ i, 0 < M.Λ i →
    (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
    (M.μ i).WidthLE ((n : ℝ) ^ γ) ∧ (M.ν i).WidthLE ((n : ℝ) ^ β) ∧
    ∀ y, 0 < (M.ν i).w y → 1 - Real.exp (-((n : ℝ) ^ p)) ≤ colDeg E G (M.μ i) y

section Trim

variable (η₀ : ℝ) (n : ℕ) {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (X : Finset (Fin N))
  (M : TagMix N)

/-- The exceptional event `|d_G(x, ν) - 1/2| > 2n^{-η}` (08:31). -/
def Exc (x : Fin N) (ν : Law N) : Prop :=
  2 * (n : ℝ) ^ (-eta8 η₀) < |rowDeg E G x ν - 1 / 2|

/-- `b(x) = Λ{i : exceptional}` (08:31). -/
def excMass (x : Fin N) : ℝ := ∑ i, M.Λ i * if Exc η₀ n E G x (M.ν i) then 1 else 0

/-- The dropped first-side labels `D = {x ∈ X : b(x) > e^{-n^η/2}}` (08:36). -/
def dropSet : Finset (Fin N) :=
  X.filter fun x => Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) < excMass η₀ n E G M x

/-- The retained first-side labels `X \ D`. -/
def retained : Finset (Fin N) := X \ dropSet η₀ n E G X M

/-- A tag is kept when `μ_i(D) ≤ 1/2` (08:39). -/
def Keep (i : M.ι) : Prop := ∑ x ∈ dropSet η₀ n E G X M, (M.μ i).w x ≤ 1 / 2

/-- The trimmed tag law: `Λ` restricted to the kept tags, normalized (`Λ` itself if no tag is kept). -/
def trimΛ : FinProb M.ι :=
  normOr (fun i => M.Λ i * if Keep η₀ n E G X M i then 1 else 0)
    (fun i => mul_nonneg (M.Λ_nonneg i) (by split_ifs <;> norm_num)) ⟨M.Λ, M.Λ_nonneg, M.Λ_sum⟩

/-- The trimmed first law: `μ_i` restricted to `Dᶜ`, normalized (`μ_i` itself at zero mass). -/
def trimμ (i : M.ι) : Law N :=
  normOr (fun x => (M.μ i).w x * if x ∈ dropSet η₀ n E G X M then 0 else 1)
    (fun x => mul_nonneg ((M.μ i).nonneg x) (by split_ifs <;> norm_num)) (M.μ i)

/-- The trimmed mixture (08:39–40): the same tags and second laws. -/
def trimMix : TagMix N where
  ι := M.ι
  Λ := (trimΛ η₀ n E G X M).w
  Λ_nonneg := (trimΛ η₀ n E G X M).nonneg
  Λ_sum := (trimΛ η₀ n E G X M).sum_eq_one
  μ := trimμ η₀ n E G X M
  ν := M.ν

end Trim

/-- The data of one application of L8.1 after trimming: the dimension, the host side, the colouring, the colour
and the trimmed mixture.  The fixed exponents `η₀, β, p` and the tuple length `h` are parameters. -/
structure Ctx (η₀ β p : ℝ) (h : ℕ) where
  n : ℕ
  N : ℕ
  E : Fin N → Fin N → Prop
  G : Colour
  M : TagMix N

/-- The trimmed context. -/
def trimCtx (η₀ β p : ℝ) (h n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Finset (Fin N))
    (M : TagMix N) : Ctx η₀ β p h :=
  ⟨n, N, E, G, trimMix η₀ n E G X M⟩

/-- What Step 1 delivers on a context (08:39–46): (7.2) on `(X, Y)`, balance `4K`, first laws on the retained
set `R ⊆ X` of width `n^γ + log 2`, second laws on `Y` of width `n^β`, own-colour defect `2e^{-n^p}`, and survival
`α_x = 2^{-h}(1 + θ_x)`, `|θ_x| ≤ n^{-η/2}`, for every retained `x`. -/
structure Std {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) (γ K : ℝ) (X Y R : Finset (Fin D.N)) : Prop where
  size : 0 < D.N ∧ D.N ≤ D.n * 2 ^ D.n
  disc : DiscOne D.E X Y ((D.n : ℝ) ^ η₀) ((D.n : ℝ) ^ η₀) ((D.n : ℝ) ^ (-η₀))
  bal : D.M.Balanced (4 * K)
  ret : R ⊆ X
  laws : ∀ i, 0 < D.M.Λ i →
    (D.M.μ i).SupportedIn R ∧ (D.M.ν i).SupportedIn Y ∧
    (D.M.μ i).WidthLE ((D.n : ℝ) ^ γ + Real.log 2) ∧ (D.M.ν i).WidthLE ((D.n : ℝ) ^ β) ∧
    ∀ y, 0 < (D.M.ν i).w y → 1 - 2 * Real.exp (-((D.n : ℝ) ^ p)) ≤ colDeg D.E D.G (D.M.μ i) y
  survival : ∀ x ∈ R,
    |∑ i, D.M.Λ i * rowDeg D.E D.G x (D.M.ν i) ^ h - ((2 : ℝ) ^ h)⁻¹| ≤
      ((2 : ℝ) ^ h)⁻¹ * (D.n : ℝ) ^ (-(eta8 η₀ / 2))

/-- L8.1b(i) (08:29–39): for large `n`, (7.2) applied to the uniform law on either signed exceptional set of one
`ν_i` (width `≤ n^η ≤ n^{η₀}` once the set has at least `Ne^{-n^η}` labels, `ν_i` of width `n^β ≤ n^{η₀}`) bounds
its size by `Ne^{-n^η}`; hence `Σ_x b(x) ≤ 2Ne^{-n^η}`, `|D| ≤ 2Ne^{-n^η/2}`, `E_Λ μ_i(D) ≤ 2Ke^{-n^η/2}` and the
discarded tags have mass at most `4Ke^{-n^η/2}` (Markov). -/
theorem trim_drop (η₀ β K : ℝ) (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
      (M : TagMix N),
      DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) → M.Balanced K →
      (∀ i, 0 < M.Λ i → (M.ν i).SupportedIn Y ∧ (M.ν i).WidthLE ((n : ℝ) ^ β)) →
      ((dropSet η₀ n E G X M).card : ℝ) ≤ 2 * N * Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) ∧
      1 - 4 * K * Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) ≤
        ∑ i, M.Λ i * (if Keep η₀ n E G X M i then 1 else 0) := by
  classical
  refine ⟨1, ?_⟩
  intro n hn N E X Y G M hdisc hbal hlaws
  have heta : 0 < eta8 η₀ := by
    unfold eta8
    exact lt_min (by linarith) (by norm_num)
  have heta_le : eta8 η₀ ≤ η₀ := by
    have h := min_le_left (η₀ / 2) (4 / 100 : ℝ)
    unfold eta8
    linarith
  have hβsmall : β < eta8 η₀ := by
    rw [tau8_eq] at hβτ
    nlinarith [heta]
  have hβη₀ : β < η₀ := by linarith
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hpowη : (n : ℝ) ^ eta8 η₀ ≤ (n : ℝ) ^ η₀ :=
    Real.rpow_le_rpow_of_exponent_le hnR heta_le
  have hpowβ : (n : ℝ) ^ β ≤ (n : ℝ) ^ η₀ :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_of_lt hβη₀)
  have hpowNeg : (n : ℝ) ^ (-η₀) ≤ (n : ℝ) ^ (-eta8 η₀) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  let u : ℝ := (n : ℝ) ^ eta8 η₀
  let t : ℝ := 2 * (n : ℝ) ^ (-eta8 η₀)
  let r : ℝ := Real.exp (-u / 2)
  have hr : 0 < r := by positivity
  have herr : (n : ℝ) ^ (-η₀) < t := by
    dsimp [t]
    have hp : 0 < (n : ℝ) ^ (-eta8 η₀) := Real.rpow_pos_of_pos hnPos _
    nlinarith [hpowNeg]
  have hdens_row (μ ν : Law N) :
      dens E G μ ν = ∑ x, μ.w x * rowDeg E G x ν := by
    unfold dens rowDeg
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hι : Nonempty M.ι := by
    by_contra h
    have hz : ∀ i : M.ι, M.Λ i = 0 := fun i => False.elim (h ⟨i⟩)
    have hzero : (∑ i, M.Λ i) = 0 := Finset.sum_eq_zero (fun i hi => hz i)
    rw [M.Λ_sum] at hzero
    norm_num at hzero
  obtain ⟨i₀⟩ := hι
  have hN : 0 < N := by
    by_contra hnN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hnN
    subst N
    have hs := (M.μ i₀).sum_eq_one
    norm_num at hs
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcardSigned (ν : Law N) (hνY : ν.SupportedIn Y)
      (hνβ : ν.WidthLE ((n : ℝ) ^ β)) (A : Finset (Fin N))
      (hAX : A ⊆ X) (s : ℝ) (hs : s = 1 ∨ s = -1)
      (hdev : ∀ x ∈ A, t < s * (rowDeg E G x ν - 1 / 2)) :
      (A.card : ℝ) ≤ (N : ℝ) * Real.exp (-u) := by
    by_contra hlargeNot
    have hlarge : (N : ℝ) * Real.exp (-u) < (A.card : ℝ) := lt_of_not_ge hlargeNot
    have hcardPos : 0 < (A.card : ℝ) := lt_of_le_of_lt (by positivity) hlarge
    have hcardNat : 0 < A.card := by exact_mod_cast hcardPos
    have hAne : A.Nonempty := Finset.card_pos.mp hcardNat
    have hAne' := hAne
    obtain ⟨x₀, hx₀⟩ := hAne'
    have hratio : (N : ℝ) / (A.card : ℝ) < Real.exp u := by
      apply (div_lt_iff₀ hcardPos).2
      calc
        (N : ℝ) = (N : ℝ) * (Real.exp (-u) * Real.exp u) := by
          rw [← Real.exp_add]
          simp
        _ = ((N : ℝ) * Real.exp (-u)) * Real.exp u := by ring
        _ < Real.exp u * (A.card : ℝ) := by
          simpa [mul_comm] using mul_lt_mul_of_pos_right hlarge (Real.exp_pos u)
    have hlog : Real.log ((N : ℝ) / (A.card : ℝ)) < u :=
      (Real.log_lt_iff_lt_exp (div_pos hNreal hcardPos)).2 hratio
    have hμwidth0 : Law.WidthLE (FinProb.uniform A hAne)
        (Real.log ((N : ℝ) / (A.card : ℝ))) := Law.uniform_width A hAne
    have hμwidth : Law.WidthLE (FinProb.uniform A hAne) ((n : ℝ) ^ η₀) :=
      Law.WidthLE.mono hμwidth0 (le_of_lt (lt_of_lt_of_le hlog hpowη))
    have hμsupp : Law.SupportedIn (FinProb.uniform A hAne) X := by
      intro x hx
      have hxA : x ∉ A := fun hxa => hx (hAX hxa)
      simp [FinProb.uniform, hxA]
    have hνwidth : ν.WidthLE ((n : ℝ) ^ η₀) :=
      Law.WidthLE.mono hνβ hpowβ
    have hdiscA := hdisc (FinProb.uniform A hAne) ν hμsupp hνY hμwidth hνwidth G
    have havg : dens E G (FinProb.uniform A hAne) ν =
        (A.card : ℝ)⁻¹ * ∑ x ∈ A, rowDeg E G x ν := by
      rw [hdens_row]
      have hterm (x : Fin N) :
          (FinProb.uniform A hAne).w x * rowDeg E G x ν =
            if x ∈ A then (A.card : ℝ)⁻¹ * rowDeg E G x ν else 0 := by
        by_cases hx : x ∈ A <;> simp [FinProb.uniform, hx]
      simp_rw [hterm]
      rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
    have hsum : (A.card : ℝ) * t <
        ∑ x ∈ A, s * (rowDeg E G x ν - 1 / 2) := by
      calc
        (A.card : ℝ) * t = ∑ x ∈ A, t := by simp [Finset.sum_const, nsmul_eq_mul]
        _ < ∑ x ∈ A, s * (rowDeg E G x ν - 1 / 2) := by
          apply Finset.sum_lt_sum
          · intro x hx
            exact le_of_lt (hdev x hx)
          · exact ⟨x₀, hx₀, hdev x₀ hx₀⟩
    have hsumrow : (∑ x ∈ A, rowDeg E G x ν) =
        (A.card : ℝ) * dens E G (FinProb.uniform A hAne) ν := by
      rw [havg]
      field_simp [ne_of_gt hcardPos]
      <;> ring
    have hsumFormula :
        (∑ x ∈ A, s * (rowDeg E G x ν - 1 / 2)) =
          (A.card : ℝ) * (s * (dens E G (FinProb.uniform A hAne) ν - 1 / 2)) := by
      rw [← Finset.mul_sum]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
      rw [hsumrow]
      ring
    have hstrict : t < s * (dens E G (FinProb.uniform A hAne) ν - 1 / 2) := by
      rw [hsumFormula] at hsum
      nlinarith [hsum]
    have hsabs : s * (dens E G (FinProb.uniform A hAne) ν - 1 / 2) ≤
        |dens E G (FinProb.uniform A hAne) ν - 1 / 2| := by
      rcases hs with hs | hs
      · rw [hs, one_mul]
        exact le_abs_self _
      · rw [hs]
        simpa using
          (neg_le_abs (dens E G (FinProb.uniform A hAne) ν - 1 / 2))
    linarith
  let Aplus (i : M.ι) : Finset (Fin N) :=
    X.filter fun x => t < rowDeg E G x (M.ν i) - 1 / 2
  let Aminus (i : M.ι) : Finset (Fin N) :=
    X.filter fun x => t < 1 / 2 - rowDeg E G x (M.ν i)
  have hplus (i : M.ι) (hi : 0 < M.Λ i) :
      ((Aplus i).card : ℝ) ≤ (N : ℝ) * Real.exp (-u) := by
    have hlaw := hlaws i hi
    have h := hcardSigned (M.ν i) hlaw.1 hlaw.2 (Aplus i)
      (Finset.filter_subset _ _) 1 (Or.inl rfl) ?_
    · exact h
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      simpa [Aplus, mul_one] using hx'
  have hminus (i : M.ι) (hi : 0 < M.Λ i) :
      ((Aminus i).card : ℝ) ≤ (N : ℝ) * Real.exp (-u) := by
    have hlaw := hlaws i hi
    have h := hcardSigned (M.ν i) hlaw.1 hlaw.2 (Aminus i)
      (Finset.filter_subset _ _) (-1) (Or.inr rfl) ?_
    · exact h
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      nlinarith [hx']
  let Aexc (i : M.ι) : Finset (Fin N) := X.filter fun x => Exc η₀ n E G x (M.ν i)
  have hexcCard (i : M.ι) (hi : 0 < M.Λ i) :
      ((Aexc i).card : ℝ) ≤ 2 * (N : ℝ) * Real.exp (-u) := by
    have hsub : Aexc i ⊆ Aplus i ∪ Aminus i := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      have hex := hx'.2
      have hsplit :
          t < rowDeg E G x (M.ν i) - 1 / 2 ∨
            t < 1 / 2 - rowDeg E G x (M.ν i) := by
        unfold Exc at hex
        by_cases hpos : 0 ≤ rowDeg E G x (M.ν i) - 1 / 2
        · rw [abs_of_nonneg hpos] at hex
          left
          dsimp [t]
          nlinarith [hex]
        · rw [abs_of_neg (lt_of_not_ge hpos)] at hex
          right
          dsimp [t]
          nlinarith [hex]
      rcases hsplit with h | h
      · apply Finset.mem_union_left
        change x ∈ Aplus i
        simp only [Aplus, Finset.mem_filter]
        exact ⟨hx'.1, h⟩
      · apply Finset.mem_union_right
        change x ∈ Aminus i
        simp only [Aminus, Finset.mem_filter]
        exact ⟨hx'.1, h⟩
    calc
      ((Aexc i).card : ℝ) ≤ ((Aplus i ∪ Aminus i).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ (Aplus i).card + (Aminus i).card := by
        exact_mod_cast Finset.card_union_le (Aplus i) (Aminus i)
      _ ≤ (N : ℝ) * Real.exp (-u) + (N : ℝ) * Real.exp (-u) :=
        add_le_add (hplus i hi) (hminus i hi)
      _ = 2 * (N : ℝ) * Real.exp (-u) := by ring
  have hsumExc :
      (∑ x ∈ X, excMass η₀ n E G M x) ≤ 2 * (N : ℝ) * Real.exp (-u) := by
    have hEq : (∑ x ∈ X, excMass η₀ n E G M x) =
        ∑ i, M.Λ i * (Aexc i).card := by
      simp_rw [excMass]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      simp [Aexc, Finset.sum_filter]
    rw [hEq]
    calc
      (∑ i, M.Λ i * (Aexc i).card) ≤
          ∑ i, M.Λ i * (2 * (N : ℝ) * Real.exp (-u)) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hlam : 0 < M.Λ i
        · exact mul_le_mul_of_nonneg_left (hexcCard i hlam) (M.Λ_nonneg i)
        · have hlam0 : M.Λ i = 0 := le_antisymm (le_of_not_gt hlam) (M.Λ_nonneg i)
          simp [hlam0]
      _ = 2 * (N : ℝ) * Real.exp (-u) := by
        rw [← Finset.sum_mul, M.Λ_sum]
        ring
  let D : Finset (Fin N) := dropSet η₀ n E G X M
  have hDsub : D ⊆ X := by
    intro x hx
    have hx' : x ∈ X ∧ Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) <
        excMass η₀ n E G M x := by simpa [D, dropSet] using hx
    exact hx'.1
  have hDmass : (D.card : ℝ) * r ≤ 2 * (N : ℝ) * Real.exp (-u) := by
    have hsumD : (D.card : ℝ) * r ≤ ∑ x ∈ X, excMass η₀ n E G M x := by
      calc
        (D.card : ℝ) * r = ∑ x ∈ D, r := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ D, excMass η₀ n E G M x := by
          apply Finset.sum_le_sum
          intro x hx
          have hx' : x ∈ X ∧ Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) <
              excMass η₀ n E G M x := by simpa [D, dropSet] using hx
          simpa [r, u] using le_of_lt hx'.2
        _ ≤ ∑ x ∈ X, excMass η₀ n E G M x :=
          Finset.sum_le_sum_of_subset_of_nonneg hDsub
            (fun x hx hxD => by
              exact Finset.sum_nonneg fun i _ =>
                mul_nonneg (M.Λ_nonneg i) (by split_ifs <;> norm_num))
    exact hsumD.trans hsumExc
  have hDcard : (D.card : ℝ) ≤ 2 * (N : ℝ) * r := by
    have hdiv := (le_div_iff₀ hr).2 hDmass
    have hquot : (2 * (N : ℝ) * Real.exp (-u)) / r = 2 * (N : ℝ) * r := by
      have hexp : Real.exp (-u) / Real.exp (-u / 2) = Real.exp (-u / 2) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      calc
        (2 * (N : ℝ) * Real.exp (-u)) / r =
            2 * (N : ℝ) * (Real.exp (-u) / Real.exp (-u / 2)) := by
              dsimp [r]
              ring
        _ = 2 * (N : ℝ) * r := by
          simpa [r] using congrArg (fun z : ℝ => 2 * (N : ℝ) * z) hexp
    simpa [hquot] using hdiv
  have hEbound :
      (∑ i, M.Λ i * (∑ x ∈ D, (M.μ i).w x)) ≤ 2 * K * r := by
    have hEq : (∑ i, M.Λ i * (∑ x ∈ D, (M.μ i).w x)) =
        ∑ x ∈ D, ∑ i, M.Λ i * (M.μ i).w x := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hEq]
    have hKnonneg : 0 ≤ K := by
      let hx : Fin N := ⟨0, hN⟩
      have hsum : 0 ≤ ∑ i, M.Λ i * (M.μ i).w hx :=
        Finset.sum_nonneg fun i _ => mul_nonneg (M.Λ_nonneg i) ((M.μ i).nonneg hx)
      exact le_trans (mul_nonneg (le_of_lt hNreal) hsum) (hbal.1 hx)
    have hpoint : ∀ x ∈ D, (∑ i, M.Λ i * (M.μ i).w x) ≤ K / (N : ℝ) := by
      intro x hx
      apply (le_div_iff₀ hNreal).2
      simpa [mul_comm] using hbal.1 x
    calc
      (∑ x ∈ D, ∑ i, M.Λ i * (M.μ i).w x) ≤ ∑ x ∈ D, K / (N : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        exact hpoint x hx
      _ = (D.card : ℝ) * (K / (N : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (N : ℝ) * r) * (K / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hDcard (div_nonneg hKnonneg (le_of_lt hNreal))
      _ = 2 * K * r := by field_simp [ne_of_gt hNreal] <;> ring
  have hbadTag :
      (∑ i, M.Λ i * (if Keep η₀ n E G X M i then 0 else 1)) ≤
        2 * (∑ i, M.Λ i * (∑ x ∈ D, (M.μ i).w x)) := by
    calc
      (∑ i, M.Λ i * (if Keep η₀ n E G X M i then 0 else 1)) ≤
          ∑ i, 2 * (M.Λ i * (∑ x ∈ D, (M.μ i).w x)) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hk : Keep η₀ n E G X M i
        · have hmass : 0 ≤ ∑ x ∈ D, (M.μ i).w x :=
            Finset.sum_nonneg fun x _ => (M.μ i).nonneg x
          simp [hk]
          exact mul_nonneg (M.Λ_nonneg i) hmass
        · have hmu : (1 / 2 : ℝ) < ∑ x ∈ D, (M.μ i).w x := by
            exact lt_of_not_ge (by simpa [Keep, D] using hk)
          have hlam := M.Λ_nonneg i
          simp [hk]
          nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hmu) hlam]
      _ = 2 * (∑ i, M.Λ i * (∑ x ∈ D, (M.μ i).w x)) := by
        rw [Finset.mul_sum]
  have hkept :
      1 - 4 * K * r ≤ ∑ i, M.Λ i * (if Keep η₀ n E G X M i then 1 else 0) := by
    have hparts :
        (∑ i, M.Λ i * (if Keep η₀ n E G X M i then 1 else 0)) +
            (∑ i, M.Λ i * (if Keep η₀ n E G X M i then 0 else 1)) = 1 := by
      rw [← Finset.sum_add_distrib]
      calc
        (∑ i, (M.Λ i * (if Keep η₀ n E G X M i then 1 else 0) +
            M.Λ i * (if Keep η₀ n E G X M i then 0 else 1))) =
            ∑ i, M.Λ i := by
          apply Finset.sum_congr rfl
          intro i hi
          split_ifs <;> simp
        _ = 1 := M.Λ_sum
    linarith [hbadTag, hEbound]
  exact ⟨by simpa [D, r, u] using hDcard, by simpa [r, u] using hkept⟩

set_option maxHeartbeats 1000000

/-- L8.1b(ii) (08:39–46): given the drop bounds, the trimmed context satisfies `Std` for large `n` (depending on
`h`): the kept mass is at least `1/2`, so balance at most doubles twice; kept first laws lose at most half their
mass (width `+ log 2`, defect `≤ 2ε`); a retained `x` has `|d_G(x, ν_i) - 1/2| ≤ 2n^{-η}` outside trimmed tag
mass `2e^{-n^η/2}`, so `α_x = 2^{-h}(1 + O(hn^{-η}) + O(2^h e^{-n^η/2}))`. -/
theorem trim_std_of (η₀ γ β p K : ℝ) (hη₀ : 0 < η₀) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hβ₀ : 0 < β)
    (hβτ : β < tau8 η₀ / 4) (hp : 0 < p) (hK : 0 < K) (h : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
      (M : TagMix N),
      Input η₀ γ β p K n N E X Y G M →
      ((dropSet η₀ n E G X M).card : ℝ) ≤ 2 * N * Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) →
      1 - 4 * K * Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) ≤
        ∑ i, M.Λ i * (if Keep η₀ n E G X M i then 1 else 0) →
      Std (trimCtx η₀ β p h n N E G X M) γ K X Y (retained η₀ n E G X M) := by
  classical
  let η : ℝ := eta8 η₀
  let c : ℝ := ((2 : ℝ) ^ h)⁻¹
  have hη : 0 < η := by
    dsimp [η, eta8]
    exact lt_min (by linarith) (by norm_num)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have htend (a : ℝ) (ha : 0 < a) :
      Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hvEvent : ∀ᶠ n : ℕ in atTop,
      (2 * (h : ℝ) + 4) / c ≤ (n : ℝ) ^ (η / 2) :=
    (htend (η / 2) (by linarith)).eventually
      (eventually_ge_atTop ((2 * (h : ℝ) + 4) / c))
  have huEvent : ∀ᶠ n : ℕ in atTop, 16 * K ≤ (n : ℝ) ^ η :=
    (htend η hη).eventually (eventually_ge_atTop (16 * K))
  have hnEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact_mod_cast hn
  have hLargeEvent : ∀ᶠ n : ℕ in atTop,
      1 ≤ (n : ℝ) ∧ (2 * (h : ℝ) + 4) / c ≤ (n : ℝ) ^ (η / 2) ∧
        16 * K ≤ (n : ℝ) ^ η := by
    filter_upwards [hnEvent, hvEvent, huEvent] with n hn hv hu
    exact ⟨hn, hv, hu⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hLargeEvent
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y G M hI hdrop hkeep
  have hLarge := hn₀ n hn
  have hnR : 1 ≤ (n : ℝ) := hLarge.1
  have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have uPos : 0 < (n : ℝ) ^ η := Real.rpow_pos_of_pos hnPos η
  let u : ℝ := (n : ℝ) ^ η
  let v : ℝ := (n : ℝ) ^ (η / 2)
  let r : ℝ := Real.exp (-u / 2)
  let t : ℝ := 2 * (n : ℝ) ^ (-η)
  have hvPos : 0 < v := Real.rpow_pos_of_pos hnPos _
  have huV : u = v ^ 2 := by
    dsimp [u, v]
    rw [show η = η / 2 + η / 2 by ring, Real.rpow_add hnPos]
    ring
  have hpowInv : (n : ℝ) ^ (-η) = 1 / u := by
    dsimp [u]
    rw [Real.rpow_neg hnPos.le]
    simp [one_div]
  have hExpLower : u / 2 ≤ Real.exp (u / 2) := by
    exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (Real.add_one_le_exp (u / 2))
  have hrbound : r ≤ 2 / u := by
    have hrecip := one_div_le_one_div_of_le (by linarith : 0 < u / 2) hExpLower
    calc
      r = Real.exp (-(u / 2)) := by
        dsimp [r]
        congr 1
        ring
      _ = (Real.exp (u / 2))⁻¹ := Real.exp_neg _
      _ = 1 / Real.exp (u / 2) := by rw [inv_eq_one_div]
      _ ≤ 1 / (u / 2) := hrecip
      _ = 2 / u := by field_simp [ne_of_gt uPos] <;> ring
  have hrpos : 0 < r := by positivity
  have h4Kr : 4 * K * r ≤ 1 / 2 := by
    have hdiv : (8 * K) / u ≤ 1 / 2 := by
      apply (div_le_iff₀ uPos).2
      have huLarge := hLarge.2.2
      nlinarith
    calc
      4 * K * r ≤ 4 * K * (2 / u) :=
        mul_le_mul_of_nonneg_left hrbound (by positivity)
      _ = (8 * K) / u := by ring
      _ ≤ 1 / 2 := hdiv
  have hNpos : 0 < N := by
    by_contra hnN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hnN
    subst N
    obtain ⟨i⟩ : Nonempty M.ι := by
      by_contra hnι
      have hz : ∀ i : M.ι, M.Λ i = 0 := fun i => False.elim (hnι ⟨i⟩)
      have hs : (∑ i, M.Λ i) = 0 := Finset.sum_eq_zero (fun i _ => hz i)
      rw [M.Λ_sum] at hs
      norm_num at hs
    have hs := (M.μ i).sum_eq_one
    norm_num at hs
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  let Ddrop : Finset (Fin N) := dropSet η₀ n E G X M
  let Rkeep : Finset (Fin N) := retained η₀ n E G X M
  let Lkeep : ℝ := ∑ i, M.Λ i * (if Keep η₀ n E G X M i then 1 else 0)
  have hLkeep : 1 / 2 ≤ Lkeep := by
    have hkeep' : 1 - 4 * K * r ≤ Lkeep := by
      simpa [Lkeep, r, u, η] using hkeep
    linarith [h4Kr]
  have hLpos : 0 < Lkeep := lt_of_lt_of_le (by norm_num) hLkeep
  have htrimΛSum :
      (∑ i, if Keep η₀ n E G X M i then M.Λ i else 0) = Lkeep := by
    unfold Lkeep
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hk : Keep η₀ n E G X M i <;> simp [hk]
  have htrimΛSumNe :
      (∑ i, if Keep η₀ n E G X M i then M.Λ i else 0) ≠ 0 := by
    rw [htrimΛSum]
    exact ne_of_gt hLpos
  have htrimΛw (i : M.ι) :
      (trimΛ η₀ n E G X M).w i =
        (M.Λ i * (if Keep η₀ n E G X M i then 1 else 0)) / Lkeep := by
    have hsum : (∑ j, M.Λ j * (if Keep η₀ n E G X M j then 1 else 0)) = Lkeep := by
      simpa [mul_ite] using htrimΛSum
    have hsumPos : 0 < ∑ j, M.Λ j * (if Keep η₀ n E G X M j then 1 else 0) := by
      rw [hsum]
      exact hLpos
    change (if hs : (∑ j, M.Λ j *
        (if Keep η₀ n E G X M j then 1 else 0)) = 0 then M.Λ i else
        (M.Λ i * (if Keep η₀ n E G X M i then 1 else 0)) /
          (∑ j, M.Λ j * (if Keep η₀ n E G X M j then 1 else 0))) = _
    rw [dif_neg (ne_of_gt hsumPos), hsum]
  have hμFsum (i : M.ι) :
      (∑ x, (M.μ i).w x * (if x ∈ Ddrop then 0 else 1)) =
        1 - ∑ x ∈ Ddrop, (M.μ i).w x := by
    have hpoint (x : Fin N) :
        (M.μ i).w x * (if x ∈ Ddrop then 0 else 1) =
          if x ∈ Ddrop then 0 else (M.μ i).w x := by
      by_cases hx : x ∈ Ddrop <;> simp [hx]
    have hpart :
        (∑ x, if x ∈ Ddrop then (M.μ i).w x else 0) +
          (∑ x, if x ∈ Ddrop then 0 else (M.μ i).w x) = 1 := by
      calc
        _ = ∑ x, (M.μ i).w x := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hmem : x ∈ Ddrop <;> simp [hmem]
        _ = 1 := (M.μ i).sum_eq_one
    have hdropSum :
        (∑ x, if x ∈ Ddrop then (M.μ i).w x else 0) =
          ∑ x ∈ Ddrop, (M.μ i).w x := by rw [Finset.sum_ite_mem_eq]
    have hcomp : (∑ x, if x ∈ Ddrop then 0 else (M.μ i).w x) =
        1 - ∑ x ∈ Ddrop, (M.μ i).w x := by rw [← hdropSum]; linarith
    calc
      (∑ x, (M.μ i).w x * (if x ∈ Ddrop then 0 else 1)) =
          ∑ x, if x ∈ Ddrop then 0 else (M.μ i).w x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpoint x
      _ = 1 - ∑ x ∈ Ddrop, (M.μ i).w x := hcomp
  have hμFsumIte (i : M.ι) :
      (∑ x, if x ∈ Ddrop then 0 else (M.μ i).w x) =
        1 - ∑ x ∈ Ddrop, (M.μ i).w x := by
    calc
      (∑ x, if x ∈ Ddrop then 0 else (M.μ i).w x) =
          ∑ x, (M.μ i).w x * (if x ∈ Ddrop then 0 else 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxD : x ∈ Ddrop <;> simp [hxD]
      _ = 1 - ∑ x ∈ Ddrop, (M.μ i).w x := hμFsum i
  have hmHalf (i : M.ι) (hk : Keep η₀ n E G X M i) :
      1 / 2 ≤ 1 - ∑ x ∈ Ddrop, (M.μ i).w x := by
    have hk' : ∑ x ∈ Ddrop, (M.μ i).w x ≤ 1 / 2 := by
      simpa [Keep, Ddrop] using hk
    linarith
  have htrimμw (i : M.ι) (hk : Keep η₀ n E G X M i) (x : Fin N) :
      (trimμ η₀ n E G X M i).w x =
        ((M.μ i).w x * (if x ∈ Ddrop then 0 else 1)) /
          (1 - ∑ x ∈ Ddrop, (M.μ i).w x) := by
    have hmPosHere : 0 < 1 - ∑ x ∈ Ddrop, (M.μ i).w x :=
      lt_of_lt_of_le (by norm_num) (hmHalf i hk)
    have hsum := hμFsum i
    have hsumPos : 0 < ∑ z, (M.μ i).w z * (if z ∈ Ddrop then 0 else 1) := by
      rw [hsum]
      exact hmPosHere
    change (if hs : (∑ z, (M.μ i).w z *
        (if z ∈ Ddrop then 0 else 1)) = 0 then (M.μ i).w x else
        ((M.μ i).w x * (if x ∈ Ddrop then 0 else 1)) /
          (∑ z, (M.μ i).w z * (if z ∈ Ddrop then 0 else 1))) = _
    rw [dif_neg (ne_of_gt hsumPos), hsum]
  have hmPos (i : M.ι) (hk : Keep η₀ n E G X M i) :
      0 < 1 - ∑ x ∈ Ddrop, (M.μ i).w x :=
    lt_of_lt_of_le (by norm_num) (hmHalf i hk)
  have htrimμle (i : M.ι) (hk : Keep η₀ n E G X M i) (x : Fin N) :
      (trimμ η₀ n E G X M i).w x ≤ 2 * (M.μ i).w x := by
    rw [htrimμw i hk x]
    by_cases hx : x ∈ Ddrop
    · have hμnon : 0 ≤ (M.μ i).w x := (M.μ i).nonneg x
      simpa [hx] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hμnon
    · simp only [hx, ↓reduceIte]
      apply (div_le_iff₀ (hmPos i hk)).2
      have hmul := mul_le_mul_of_nonneg_left (hmHalf i hk)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((M.μ i).nonneg x))
      nlinarith
  have htrimΛle (i : M.ι) :
      (trimΛ η₀ n E G X M).w i ≤ 2 * M.Λ i := by
    by_cases hk : Keep η₀ n E G X M i
    · rw [htrimΛw i]
      simp only [if_pos hk, mul_one]
      apply (div_le_iff₀ hLpos).2
      have hmul := mul_le_mul_of_nonneg_left hLkeep (M.Λ_nonneg i)
      nlinarith
    · have hlamNon : 0 ≤ M.Λ i := M.Λ_nonneg i
      have hzero : (trimΛ η₀ n E G X M).w i = 0 := by
        rw [htrimΛw i]
        simp [hk]
      rw [hzero]
      exact mul_nonneg (by norm_num) hlamNon
  have hcolcomp (μ : Law N) (y : Fin N) :
      colDeg E G μ y + colDeg E (!G) μ y = 1 := by
    unfold colDeg
    rw [← Finset.sum_add_distrib]
    have hterm (x : Fin N) :
        μ.w x * (if Hits E G x y then 1 else 0) +
          μ.w x * (if Hits E (!G) x y then 1 else 0) = μ.w x := by
      cases G <;> by_cases hxy : E x y <;> simp [Hits, hxy]
    calc
      (∑ x, (μ.w x * (if Hits E G x y then 1 else 0) +
          μ.w x * (if Hits E (!G) x y then 1 else 0))) = ∑ x, μ.w x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hterm x
      _ = 1 := μ.sum_eq_one
  have hpairBound (i : M.ι) (x : Fin N) :
      (trimΛ η₀ n E G X M).w i * (trimμ η₀ n E G X M i).w x ≤
        4 * (M.Λ i * (M.μ i).w x) := by
    by_cases hk : Keep η₀ n E G X M i
    · have hlam := htrimΛle i
      have hμ := htrimμle i hk x
      calc
        (trimΛ η₀ n E G X M).w i * (trimμ η₀ n E G X M i).w x ≤
            (2 * M.Λ i) * (trimμ η₀ n E G X M i).w x :=
          mul_le_mul_of_nonneg_right hlam ((trimμ η₀ n E G X M i).nonneg x)
        _ ≤ (2 * M.Λ i) * (2 * (M.μ i).w x) :=
          mul_le_mul_of_nonneg_left hμ (mul_nonneg (by norm_num) (M.Λ_nonneg i))
        _ = 4 * (M.Λ i * (M.μ i).w x) := by ring
    · have hzero : (trimΛ η₀ n E G X M).w i = 0 := by
        rw [htrimΛw i]
        simp [hk]
      rw [hzero]
      simp only [zero_mul]
      change 0 ≤ (4 : ℝ) * (M.Λ i * (M.μ i).w x)
      exact mul_nonneg (by norm_num) (mul_nonneg (M.Λ_nonneg i) ((M.μ i).nonneg x))
  have hbalance : (trimMix η₀ n E G X M).Balanced (4 * K) := by
    constructor
    · intro x
      have hsum :
          (∑ i, (trimΛ η₀ n E G X M).w i * (trimμ η₀ n E G X M i).w x) ≤
            4 * (∑ i, M.Λ i * (M.μ i).w x) := by
        calc
          (∑ i, (trimΛ η₀ n E G X M).w i * (trimμ η₀ n E G X M i).w x) ≤
              ∑ i, 4 * (M.Λ i * (M.μ i).w x) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hpairBound i x
          _ = 4 * (∑ i, M.Λ i * (M.μ i).w x) := by rw [Finset.mul_sum]
      calc
        (N : ℝ) * ∑ i, (trimΛ η₀ n E G X M).w i * (trimμ η₀ n E G X M i).w x ≤
            (N : ℝ) * (4 * ∑ i, M.Λ i * (M.μ i).w x) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hNreal)
        _ = 4 * ((N : ℝ) * ∑ i, M.Λ i * (M.μ i).w x) := by ring
        _ ≤ 4 * K := mul_le_mul_of_nonneg_left (hI.bal.1 x) (by norm_num)
    · intro y
      have hsum :
          (∑ i, (trimΛ η₀ n E G X M).w i * (M.ν i).w y) ≤
            2 * (∑ i, M.Λ i * (M.ν i).w y) := by
        calc
          (∑ i, (trimΛ η₀ n E G X M).w i * (M.ν i).w y) ≤
              ∑ i, 2 * (M.Λ i * (M.ν i).w y) := by
            apply Finset.sum_le_sum
            intro i hi
            calc
              (trimΛ η₀ n E G X M).w i * (M.ν i).w y ≤
                  (2 * M.Λ i) * (M.ν i).w y :=
                mul_le_mul_of_nonneg_right (htrimΛle i) ((M.ν i).nonneg y)
              _ = 2 * (M.Λ i * (M.ν i).w y) := by ring
          _ = 2 * (∑ i, M.Λ i * (M.ν i).w y) := by rw [Finset.mul_sum]
      calc
        (N : ℝ) * ∑ i, (trimΛ η₀ n E G X M).w i * (M.ν i).w y ≤
            (N : ℝ) * (2 * ∑ i, M.Λ i * (M.ν i).w y) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hNreal)
        _ = 2 * ((N : ℝ) * ∑ i, M.Λ i * (M.ν i).w y) := by ring
        _ ≤ 2 * K := mul_le_mul_of_nonneg_left (hI.bal.2 y) (by norm_num)
        _ ≤ 4 * K := by nlinarith [hK]
  have hKeepOfPos (i : M.ι) (hi : 0 < (trimΛ η₀ n E G X M).w i) :
      Keep η₀ n E G X M i := by
    by_contra hk
    rw [htrimΛw i] at hi
    simp [hk] at hi
  have hΛOfPos (i : M.ι) (hk : Keep η₀ n E G X M i)
      (hi : 0 < (trimΛ η₀ n E G X M).w i) : 0 < M.Λ i := by
    by_contra hnot
    have hzero : M.Λ i = 0 := le_antisymm (le_of_not_gt hnot) (M.Λ_nonneg i)
    rw [htrimΛw i] at hi
    simp [hk, hzero] at hi
  refine ⟨⟨hNpos, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [trimCtx] using hI.size
  · simpa [trimCtx] using hI.disc
  · simpa [trimCtx, trimMix] using hbalance
  · intro x hx
    exact (Finset.mem_sdiff.mp (by simpa [Rkeep, retained] using hx)).1
  · intro i hi
    have hi' : 0 < (trimΛ η₀ n E G X M).w i := by
      simpa [trimCtx, trimMix] using hi
    have hk : Keep η₀ n E G X M i := hKeepOfPos i hi'
    have hlam : 0 < M.Λ i := hΛOfPos i hk hi'
    rcases hI.laws i hlam with ⟨hμX, hνY, hμwidth, hνwidth, hdeg⟩
    have hμsupport : Law.SupportedIn (trimμ η₀ n E G X M i) Rkeep := by
      intro x hxR
      by_cases hxD : x ∈ Ddrop
      · rw [htrimμw i hk x]
        simp [hxD]
      · have hxX : x ∉ X := by
          intro hxX
          apply hxR
          have hxmem : x ∈ retained η₀ n E G X M := by
            change x ∈ X \ dropSet η₀ n E G X M
            exact Finset.mem_sdiff.mpr ⟨hxX, by simpa [Ddrop] using hxD⟩
          simpa [Rkeep, retained] using hxmem
        rw [htrimμw i hk x]
        simp [hxD, hμX x hxX]
    have hμwidthTrim : Law.WidthLE (trimμ η₀ n E G X M i)
        ((n : ℝ) ^ γ + Real.log 2) := by
      intro x
      calc
        (trimμ η₀ n E G X M i).w x ≤ 2 * (M.μ i).w x := htrimμle i hk x
        _ ≤ 2 * (Real.exp ((n : ℝ) ^ γ) / N) :=
          mul_le_mul_of_nonneg_left (hμwidth x) (by norm_num)
        _ = Real.exp ((n : ℝ) ^ γ + Real.log 2) / N := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          ring
    have hdegTrim : ∀ y, 0 < (M.ν i).w y →
        1 - 2 * Real.exp (-((n : ℝ) ^ p)) ≤
          colDeg E G (trimμ η₀ n E G X M i) y := by
      intro y hy
      have hmPos' := hmPos i hk
      have hmissCompare :
          colDeg E (!G) (trimμ η₀ n E G X M i) y ≤
            colDeg E (!G) (M.μ i) y /
              (1 - ∑ x ∈ Ddrop, (M.μ i).w x) := by
        unfold colDeg
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro x hx
        rw [htrimμw i hk x]
        by_cases hxD : x ∈ Ddrop
        · simp [hxD]
          have hnum : 0 ≤ if Hits E (!G) x y then (M.μ i).w x else 0 := by
            by_cases hhit : Hits E (!G) x y <;> simp [hhit, (M.μ i).nonneg x]
          exact div_nonneg hnum (le_of_lt hmPos')
        · simp [hxD, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      have hmissOrig : colDeg E (!G) (M.μ i) y ≤ Real.exp (-((n : ℝ) ^ p)) := by
        have hc := hcolcomp (M.μ i) y
        have hd := hdeg y hy
        linarith
      have hmissTrim :
          colDeg E (!G) (trimμ η₀ n E G X M i) y ≤
            2 * Real.exp (-((n : ℝ) ^ p)) := by
        calc
          colDeg E (!G) (trimμ η₀ n E G X M i) y ≤
              colDeg E (!G) (M.μ i) y /
                (1 - ∑ x ∈ Ddrop, (M.μ i).w x) := hmissCompare
          _ ≤ Real.exp (-((n : ℝ) ^ p)) /
                (1 - ∑ x ∈ Ddrop, (M.μ i).w x) :=
              div_le_div_of_nonneg_right hmissOrig (le_of_lt hmPos')
          _ ≤ 2 * Real.exp (-((n : ℝ) ^ p)) := by
              apply (div_le_iff₀ hmPos').2
              calc
                Real.exp (-((n : ℝ) ^ p)) =
                    (2 * Real.exp (-((n : ℝ) ^ p))) * (1 / 2 : ℝ) := by ring
                _ ≤ (2 * Real.exp (-((n : ℝ) ^ p))) *
                    (1 - ∑ x ∈ Ddrop, (M.μ i).w x) :=
                  mul_le_mul_of_nonneg_left (hmHalf i hk) (by positivity)
      have hc := hcolcomp (trimμ η₀ n E G X M i) y
      linarith
    exact ⟨hμsupport, hνY, by simpa [trimCtx, trimMix] using hμwidthTrim,
      hνwidth, by simpa [trimCtx, trimMix] using hdegTrim⟩
  · intro x hxR
    let xN : Fin N := by simpa [trimCtx] using x
    have hxR' : xN ∈ X ∧ xN ∉ Ddrop := by
      have hxR'' : xN ∈ X \ dropSet η₀ n E G X M := by
        change x ∈ X \ dropSet η₀ n E G X M at hxR
        exact hxR
      rcases Finset.mem_sdiff.mp hxR'' with ⟨hxX, hxD⟩
      exact ⟨hxX, by simpa [Ddrop] using hxD⟩
    have hbadMass :
        (∑ i, (trimΛ η₀ n E G X M).w i *
          (if Exc η₀ n E G xN (M.ν i) then 1 else 0)) ≤ 2 * r := by
      have hExc : excMass η₀ n E G M xN ≤ r := by
        by_contra hnot
        have hlt : r < excMass η₀ n E G M xN := lt_of_not_ge hnot
        have hxD : xN ∈ Ddrop := by
          change xN ∈ X.filter (fun z =>
            Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) < excMass η₀ n E G M z)
          exact Finset.mem_filter.mpr ⟨hxR'.1, by simpa [r, u, η] using hlt⟩
        exact hxR'.2 hxD
      have hterm (i : M.ι) :
          (trimΛ η₀ n E G X M).w i *
            (if Exc η₀ n E G xN (M.ν i) then 1 else 0) ≤
          (M.Λ i * (if Exc η₀ n E G xN (M.ν i) then 1 else 0)) / Lkeep := by
        rw [htrimΛw i]
        by_cases hk : Keep η₀ n E G X M i
        · simp [hk, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        · simp [hk]
          have hnum : 0 ≤ if Exc η₀ n E G xN (M.ν i) then M.Λ i else 0 := by
            by_cases hex : Exc η₀ n E G xN (M.ν i) <;> simp [hex, M.Λ_nonneg i]
          exact div_nonneg hnum (le_of_lt hLpos)
      calc
        (∑ i, (trimΛ η₀ n E G X M).w i *
            (if Exc η₀ n E G xN (M.ν i) then 1 else 0)) ≤
            ∑ i, (M.Λ i * (if Exc η₀ n E G xN (M.ν i) then 1 else 0)) / Lkeep := by
          apply Finset.sum_le_sum
          intro i hi
          exact hterm i
        _ = excMass η₀ n E G M xN / Lkeep := by
          calc
            (∑ i, (M.Λ i * (if Exc η₀ n E G xN (M.ν i) then 1 else 0)) / Lkeep) =
                (∑ i, M.Λ i * (if Exc η₀ n E G xN (M.ν i) then 1 else 0)) / Lkeep := by
              rw [← Finset.sum_div]
            _ = excMass η₀ n E G M xN / Lkeep := rfl
        _ ≤ r / Lkeep := div_le_div_of_nonneg_right hExc (le_of_lt hLpos)
        _ ≤ 2 * r := by
          apply (div_le_iff₀ hLpos).2
          calc
            r = (2 * r) * (1 / 2 : ℝ) := by ring
            _ ≤ (2 * r) * Lkeep :=
              mul_le_mul_of_nonneg_left hLkeep (by positivity)
    have hrow0 (i : M.ι) : 0 ≤ rowDeg E G xN (M.ν i) := by
      unfold rowDeg
      exact Finset.sum_nonneg fun y _ =>
        mul_nonneg ((M.ν i).nonneg y) (by split_ifs <;> norm_num)
    have hrow1 (i : M.ι) : rowDeg E G xN (M.ν i) ≤ 1 := by
      unfold rowDeg
      calc
        (∑ y, (M.ν i).w y * (if Hits E G xN y then 1 else 0)) ≤
            ∑ y, (M.ν i).w y := by
          apply Finset.sum_le_sum
          intro y hy
          by_cases hhit : Hits E G xN y <;> simp [hhit, (M.ν i).nonneg y]
        _ = 1 := (M.ν i).sum_eq_one
    have hpowdiff (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
        |d ^ h - (1 / 2 : ℝ) ^ h| ≤ |d - 1 / 2| * (h : ℝ) := by
      have hmax : max |d| |(1 / 2 : ℝ)| ≤ 1 := by
        apply max_le_iff.mpr
        constructor
        · rw [abs_of_nonneg hd0]
          exact hd1
        · norm_num
      have hmax0 : 0 ≤ max |d| |(1 / 2 : ℝ)| :=
        le_trans (abs_nonneg d) (le_max_left _ _)
      have hpowMax : max |d| |(1 / 2 : ℝ)| ^ (h - 1) ≤ 1 :=
        pow_le_one₀ hmax0 hmax
      calc
        |d ^ h - (1 / 2 : ℝ) ^ h| ≤
            |d - 1 / 2| * (h : ℝ) * max |d| |(1 / 2 : ℝ)| ^ (h - 1) :=
          abs_pow_sub_pow_le d (1 / 2 : ℝ) h
        _ ≤ |d - 1 / 2| * (h : ℝ) :=
          mul_le_of_le_one_right
            (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg h)) hpowMax
    have hcPow : c = (1 / 2 : ℝ) ^ h := by
      dsimp [c]
      calc
        ((2 : ℝ) ^ h)⁻¹ = ((2 : ℝ)⁻¹) ^ h := by rw [inv_pow]
        _ = (1 / 2 : ℝ) ^ h := by norm_num
    have hpointDiff (i : M.ι) :
        |(rowDeg E G xN (M.ν i)) ^ h - c| ≤
          (h : ℝ) * t + (if Exc η₀ n E G xN (M.ν i) then 1 else 0) := by
      by_cases hex : Exc η₀ n E G xN (M.ν i)
      · have hd0 := hrow0 i
        have hd1 := hrow1 i
        have hp0 : 0 ≤ (rowDeg E G xN (M.ν i)) ^ h := pow_nonneg hd0 _
        have hp1 : (rowDeg E G xN (M.ν i)) ^ h ≤ 1 := pow_le_one₀ hd0 hd1
        have hc0 : 0 ≤ c := by rw [hcPow]; positivity
        have hc1 : c ≤ 1 := by rw [hcPow]; exact pow_le_one₀ (by norm_num) (by norm_num)
        have habs : |(rowDeg E G xN (M.ν i)) ^ h - c| ≤ 1 :=
          abs_le.mpr ⟨by linarith, by linarith⟩
        simp [hex]
        nlinarith [habs, (show 0 ≤ (h : ℝ) * t by positivity)]
      · have hnear : |rowDeg E G xN (M.ν i) - 1 / 2| ≤ t := by
          by_contra hgt
          apply hex
          unfold Exc
          simpa [t] using lt_of_not_ge hgt
        rw [if_neg hex]
        calc
          |(rowDeg E G xN (M.ν i)) ^ h - c| =
              |(rowDeg E G xN (M.ν i)) ^ h - (1 / 2 : ℝ) ^ h| := by rw [hcPow]
          _ ≤ |rowDeg E G xN (M.ν i) - 1 / 2| * (h : ℝ) :=
            hpowdiff _ (hrow0 i) (hrow1 i)
          _ ≤ t * (h : ℝ) := mul_le_mul_of_nonneg_right hnear (Nat.cast_nonneg h)
          _ = (h : ℝ) * t := by ring
          _ ≤ (h : ℝ) * t + 0 := by simp
    have hqsum : ∑ i, (trimΛ η₀ n E G X M).w i = 1 :=
      (trimΛ η₀ n E G X M).sum_eq_one
    have hsurvEq :
        (∑ i, (trimΛ η₀ n E G X M).w i *
          (rowDeg E G xN (M.ν i)) ^ h) - c =
        ∑ i, (trimΛ η₀ n E G X M).w i *
          ((rowDeg E G xN (M.ν i)) ^ h - c) := by
      calc
        (∑ i, (trimΛ η₀ n E G X M).w i * (rowDeg E G xN (M.ν i)) ^ h) - c =
            (∑ i, (trimΛ η₀ n E G X M).w i * (rowDeg E G xN (M.ν i)) ^ h) -
              (∑ i, (trimΛ η₀ n E G X M).w i) * c := by rw [hqsum]; ring
        _ = ∑ i, ((trimΛ η₀ n E G X M).w i * (rowDeg E G xN (M.ν i)) ^ h -
              (trimΛ η₀ n E G X M).w i * c) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        _ = ∑ i, (trimΛ η₀ n E G X M).w i *
              ((rowDeg E G xN (M.ν i)) ^ h - c) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    have hmoment :
        |(∑ i, (trimΛ η₀ n E G X M).w i *
            (rowDeg E G xN (M.ν i)) ^ h) - c| ≤ (h : ℝ) * t + 2 * r := by
      rw [hsurvEq]
      calc
        |∑ i, (trimΛ η₀ n E G X M).w i *
            ((rowDeg E G xN (M.ν i)) ^ h - c)| ≤
            ∑ i, |(trimΛ η₀ n E G X M).w i *
              ((rowDeg E G xN (M.ν i)) ^ h - c)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, (trimΛ η₀ n E G X M).w i *
              |(rowDeg E G xN (M.ν i)) ^ h - c| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul, abs_of_nonneg ((trimΛ η₀ n E G X M).nonneg i)]
        _ ≤ ∑ i, (trimΛ η₀ n E G X M).w i *
              ((h : ℝ) * t +
                (if Exc η₀ n E G xN (M.ν i) then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hpointDiff i) ((trimΛ η₀ n E G X M).nonneg i)
        _ = (∑ i, (trimΛ η₀ n E G X M).w i) * ((h : ℝ) * t) +
              ∑ i, (trimΛ η₀ n E G X M).w i *
                (if Exc η₀ n E G xN (M.ν i) then 1 else 0) := by
          calc
            _ = ∑ i, ((trimΛ η₀ n E G X M).w i * ((h : ℝ) * t) +
                  (trimΛ η₀ n E G X M).w i *
                    (if Exc η₀ n E G xN (M.ν i) then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = (∑ i, (trimΛ η₀ n E G X M).w i) * ((h : ℝ) * t) +
                  ∑ i, (trimΛ η₀ n E G X M).w i *
                    (if Exc η₀ n E G xN (M.ν i) then 1 else 0) := by
              rw [Finset.sum_add_distrib, Finset.sum_mul]
        _ = (h : ℝ) * t +
              ∑ i, (trimΛ η₀ n E G X M).w i *
                (if Exc η₀ n E G xN (M.ν i) then 1 else 0) := by
          rw [hqsum]
          ring
        _ ≤ (h : ℝ) * t + 2 * r := by
          simpa [add_comm] using add_le_add_left hbadMass ((h : ℝ) * t)
    have htEq : t = 2 / (v ^ 2) := by
      dsimp [t]
      rw [hpowInv, huV]
      ring
    have htail : (h : ℝ) * t + 2 * r ≤
        (2 * (h : ℝ) + 4) / (v ^ 2) := by
      have hr' : 2 * r ≤ 4 / (v ^ 2) := by
        calc
          2 * r ≤ 2 * (2 / u) := mul_le_mul_of_nonneg_left hrbound (by norm_num)
          _ = 4 / (v ^ 2) := by rw [huV]; ring
      rw [htEq]
      calc
        (h : ℝ) * (2 / (v ^ 2)) + 2 * r =
            2 * r + (h : ℝ) * (2 / (v ^ 2)) := by ring
        _ ≤ 4 / (v ^ 2) + (h : ℝ) * (2 / (v ^ 2)) :=
          by
            have hh := add_le_add_right hr' ((h : ℝ) * (2 / (v ^ 2)))
            simpa [add_comm] using hh
        _ = (2 * (h : ℝ) + 4) / (v ^ 2) := by ring
    have hcoef : 2 * (h : ℝ) + 4 ≤ c * v := by
      have hcoef' := (div_le_iff₀ hc).mp hLarge.2.1
      simpa [mul_comm] using hcoef'
    have hfinalNum : (2 * (h : ℝ) + 4) / (v ^ 2) ≤ c / v := by
      apply (div_le_iff₀ (sq_pos_of_pos hvPos)).2
      calc
        2 * (h : ℝ) + 4 ≤ c * v := hcoef
        _ = (c / v) * (v ^ 2) := by field_simp [ne_of_gt hvPos] <;> ring
    have hvInv : (n : ℝ) ^ (-(η / 2)) = 1 / v := by
      dsimp [v]
      rw [Real.rpow_neg hnPos.le]
      simp [one_div]
    have hfinal :
        |(∑ i, (trimΛ η₀ n E G X M).w i *
            (rowDeg E G xN (M.ν i)) ^ h) - c| ≤
          c * (n : ℝ) ^ (-(η / 2)) := by
      calc
        |(∑ i, (trimΛ η₀ n E G X M).w i *
            (rowDeg E G xN (M.ν i)) ^ h) - c| ≤ (h : ℝ) * t + 2 * r := hmoment
        _ ≤ (2 * (h : ℝ) + 4) / (v ^ 2) := htail
        _ ≤ c / v := hfinalNum
        _ = c * (n : ℝ) ^ (-(η / 2)) := by rw [hvInv]; ring
    change |(∑ i, (trimΛ η₀ n E G X M).w i *
        (rowDeg E G xN (M.ν i)) ^ h) - c| ≤ c * (n : ℝ) ^ (-(η / 2))
    exact hfinal

/-- L8.1b assembled (08:23–46). -/
theorem trim_std (η₀ γ β p K : ℝ) (hη₀ : 0 < η₀) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hβ₀ : 0 < β)
    (hβτ : β < tau8 η₀ / 4) (hp : 0 < p) (hK : 0 < K) (h : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
      (M : TagMix N),
      Input η₀ γ β p K n N E X Y G M →
      Std (trimCtx η₀ β p h n N E G X M) γ K X Y (retained η₀ n E G X M) := by
  obtain ⟨n₁, hdrop⟩ := trim_drop η₀ β K hη₀ hβ₀ hβτ
  obtain ⟨n₂, hstd⟩ := trim_std_of η₀ γ β p K hη₀ hγ₀ hγ₁ hβ₀ hβτ hp hK h
  refine ⟨max n₁ n₂, fun n hn N E X Y G M hI => ?_⟩
  obtain ⟨hcard, hkeep⟩ := hdrop n (le_trans (le_max_left _ _) hn) N E X Y G M hI.disc hI.bal
    (fun i hi => ⟨(hI.laws i hi).2.1, (hI.laws i hi).2.2.2.1⟩)
  exact hstd n (le_trans (le_max_right _ _) hn) N E X Y G M hI hcard hkeep

end HypercubeRamsey.S08
