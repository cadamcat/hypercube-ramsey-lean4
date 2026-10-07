import HypercubeRamsey.S07.SmallGridPurity_q_s07_even
import HypercubeRamsey.S07.Support
import HypercubeRamsey.S07.EvenStage
import HypercubeRamsey.Framework.OneShot

set_option maxHeartbeats 1000000

/-!
# Lemma 7.1: small-grid purity exclusion

Source: `sections/07-…tex`, lines 41–392.  The stages (`tag_stage`, `anchor_stage`, `clock_rows`,
`even_stage`) and the three-stage averaging node `grid_realization_of` give a realization with valid cells, an
injective odd assignment avoiding predictive failure, and even column sums at most one (07:386–391); the
posterior even rows of that realization are Hall data (07:391–392), and the framework's `cubeAt_of_rows`
(F-HallEmbed) gives the cube.
-/

namespace HypercubeRamsey.S07

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators

/-- The conclusion of the probabilistic construction in L7.1i, before applying Hall's embedding theorem. -/
def GridHallData {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) : Prop :=
  ∃ (fB : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N)
    (p : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ),
      Function.Injective fB ∧
      (∀ a x, 0 ≤ p a x) ∧
      (∀ a, ∑ x, p a x = 1) ∧
      (∀ a x, p a x ≠ 0 → ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
        (cube n).Adj a.1 b.1 → Hits E G x (fB b)) ∧
      (∀ x, ∑ a, p a x ≤ 1)

/-- Monotonicity of the large regime in its constants. -/
theorem largeAt_weaken {n₀ n₀' : ℕ} {C₀ C₀' : ℝ} {n N : ℕ} (h : LargeAt n₀ C₀ n N)
    (hn : n₀' ≤ n₀) (hC : C₀' ≤ C₀) : LargeAt n₀' C₀' n N :=
  ⟨le_trans hn h.1, le_trans (mul_le_mul_of_nonneg_right hC (by positivity)) h.2.1, h.2.2⟩

/-- L7.1, Steps 4–6 averaged (07:386–391): if typical tags fail with probability at most `δ = n 2^n 4^{-n}`, the
odd column sums exceed `θ₀` with probability at most `δ` under the two-stage law, both avoidance events have
positive mass, successful prehistories admit clock-sampler laws, and at typical admitted tags every
clock-sampler family has even column sums above one with probability at most `δ`, then (as `3δ < 1` for large
`n`) some realization has valid cells, an injective odd assignment avoiding predictive failure, and even column
sums at most one. -/
theorem grid_realization_of :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {d : ℝ} {s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
      {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
      (Q : Γ.Key → FinProb M.ι) (D₀ C : ℝ), 0 < N →
      (tagLaw Γ M Q D₀).pr (fun σ => ¬ Typical Γ M C σ) ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n →
      (FinProb.bind (tagLaw Γ M Q D₀) (anchorLaw Γ M)).pr
          (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n →
      0 < (FinProb.pi Q).pr (fun σ => ∀ g, ¬ TagBad Γ M D₀ σ g) →
      (∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) →
        0 < (rawAnchors Γ M σ).pr (fun W => ∀ c, ¬ CellBad Γ M σ W c)) →
      (∀ σ W, GoodPre Γ M σ W → ∃ J, ClockOK Γ M σ W J) →
      (∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) → Typical Γ M C σ →
        ∀ J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N),
          (∀ W, GoodPre Γ M σ W → ClockOK Γ M σ W (J W)) →
          ∑ W, (anchorLaw Γ M σ).w W *
            (if GoodPre Γ M σ W then (J W).pr (fun f => ∃ x, 1 < evenColumn Γ M σ W f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) →
      ∃ (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N),
        (∀ c, CellValid Γ M σ W c) ∧ Function.Injective f ∧
        (∀ a : EvenRole n, ¬ PredFail Γ M σ W a.1 (nbrLabels f a)) ∧
        ∀ x, evenColumn Γ M σ W f x ≤ 1 := by
  classical
  refine ⟨4, ?_⟩
  intro n hn d s ℓ q N E G X Y p κ Γ M Q D₀ C hN htyp hodd htag hcell hclock heven
  let δ : ℝ := (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n
  have hNatPow : ∀ k : ℕ, 4 ≤ k → 4 * k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
        intro hk
        by_cases hkeq : k = 3
        · subst k
          norm_num
        have hk4 : 4 ≤ k := by omega
        have hbase : 4 ≤ 2 ^ k := by
          obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk4
          have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by omega)
          calc
            4 = 4 * 1 := by norm_num
            _ ≤ 4 * 2 ^ j := Nat.mul_le_mul_left _ hpow
            _ ≤ 2 ^ 4 * 2 ^ j := by norm_num
            _ = 2 ^ (4 + j) := by rw [Nat.pow_add]
        rw [pow_succ]
        nlinarith [ih hk4, hbase]
  have hNat : 4 * n ≤ 2 ^ n := hNatPow n hn
  have hDelta : δ ≤ 1 / 4 := by
    have hpow : (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    have hdiv : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
      rw [one_div_pow]
    have hratio : (n : ℝ) / (2 : ℝ) ^ n ≤ 1 / 4 := by
      apply (div_le_iff₀ (by positivity)).2
      have hcast : (4 : ℝ) * n ≤ (2 : ℝ) ^ n := by exact_mod_cast hNat
      nlinarith
    calc
      δ = (n : ℝ) * (2 ^ n * (1 / 4 : ℝ) ^ n) := by dsimp [δ]; ring
      _ = (n : ℝ) * (1 / 2 : ℝ) ^ n := by rw [hpow]
      _ = (n : ℝ) / (2 : ℝ) ^ n := by rw [hdiv]; ring
      _ ≤ 1 / 4 := hratio
  have h3δ : 3 * δ < 1 := by nlinarith
  have htagSupport : ∀ σ, (tagLaw Γ M Q D₀).w σ ≠ 0 → ∀ g, ¬ TagBad Γ M D₀ σ g := by
    intro σ hσ g
    apply condOr_weight_support (P := FinProb.pi Q)
      (A := fun σ => ∀ g, ¬ TagBad Γ M D₀ σ g) htag
    simpa [tagLaw] using hσ
  have hcellSupport : ∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) →
      ∀ W, (anchorLaw Γ M σ).w W ≠ 0 → ∀ c, ¬ CellBad Γ M σ W c := by
    intro σ hσ W hW c
    apply condOr_weight_support (P := rawAnchors Γ M σ)
      (A := fun W => ∀ c, ¬ CellBad Γ M σ W c) (hcell σ hσ)
    simpa [anchorLaw] using hW
  have hcellAvoidZero : ∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) →
      (anchorLaw Γ M σ).pr (fun W => ¬ ∀ c, ¬ CellBad Γ M σ W c) = 0 := by
    intro σ hσ
    simpa [anchorLaw] using condOr_pr_not (rawAnchors Γ M σ)
      (fun W => ∀ c, ¬ CellBad Γ M σ W c) (hcell σ hσ)
  let μ₀ : FinProb (Fin N) := FinProb.uniform Finset.univ
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let J₀ : FinProb (OddRole n → Fin N) := FinProb.pi fun _ => μ₀
  let Jfam : (Γ.Key → M.ι) → (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N) :=
    fun σ W => if h : GoodPre Γ M σ W then Classical.choose (hclock σ W h) else J₀
  have hJfam (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (hpre : GoodPre Γ M σ W) :
      ClockOK Γ M σ W (Jfam σ W) := by
    simp [Jfam, hpre]
    exact Classical.choose_spec (hclock σ W hpre)
  let P : FinProb ((Γ.Key → M.ι) × ((Γ.Cell → Fin N) × (OddRole n → Fin N))) :=
    FinProb.bind (tagLaw Γ M Q D₀) (fun σ => FinProb.bind (anchorLaw Γ M σ) (Jfam σ))
  let tagBad (σ : Γ.Key → M.ι) : Prop := ¬ Typical Γ M C σ
  let cellBad (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) : Prop :=
    ¬ ∀ c, ¬ CellBad Γ M σ W c
  let oddBad (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) : Prop :=
    ∃ y, (1e-8 : ℝ) < oddColumn Γ M σ W y
  let evenBad (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N) : Prop :=
    ∃ x, 1 < evenColumn Γ M σ W f x
  let success (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N) : Prop :=
    Typical Γ M C σ ∧ GoodPre Γ M σ W ∧ ∀ x, evenColumn Γ M σ W f x ≤ 1
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  letI : DecidablePred tagBad := fun σ => Classical.propDecidable (tagBad σ)
  letI : ∀ σ, DecidablePred (cellBad σ) := fun σ W => Classical.propDecidable (cellBad σ W)
  letI : ∀ σ, DecidablePred (oddBad σ) := fun σ W => Classical.propDecidable (oddBad σ W)
  letI : ∀ σ W, DecidablePred (evenBad σ W) := fun σ W f => Classical.propDecidable (evenBad σ W f)
  letI : ∀ σ W, DecidablePred (success σ W) := fun σ W f => Classical.propDecidable (success σ W f)
  have htagP : P.pr (fun ω => tagBad ω.1) = (tagLaw Γ M Q D₀).pr tagBad := by
    have hexpand : P.pr (fun ω => tagBad ω.1) =
        ∑ σ, (tagLaw Γ M Q D₀).w σ *
          (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr (fun _ => tagBad σ) := by
      simpa [P] using bind_pr_eq (tagLaw Γ M Q D₀)
        (fun σ => FinProb.bind (anchorLaw Γ M σ) (Jfam σ)) (fun σ _ => tagBad σ)
    calc
      P.pr (fun ω => tagBad ω.1) =
        ∑ σ, (tagLaw Γ M Q D₀).w σ *
          (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr (fun _ => tagBad σ) := hexpand
      _ =
          ∑ σ, (tagLaw Γ M Q D₀).w σ * (if tagBad σ then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [pr_const]
      _ = (tagLaw Γ M Q D₀).pr tagBad := by
        simpa using (pr_as_weight_sum (tagLaw Γ M Q D₀) tagBad).symm
  have hoddKernel (σ : Γ.Key → M.ι) :
      (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr
          (fun wf => oddBad σ wf.1) = (anchorLaw Γ M σ).pr (oddBad σ) := by
    have hexpand := bind_pr_eq (anchorLaw Γ M σ) (Jfam σ) (fun W _ => oddBad σ W)
    calc
      (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr (fun wf => oddBad σ wf.1) =
          ∑ W, (anchorLaw Γ M σ).w W * (Jfam σ W).pr (fun _ => oddBad σ W) := hexpand
      _ =
          ∑ W, (anchorLaw Γ M σ).w W * (if oddBad σ W then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [pr_const]
      _ = (anchorLaw Γ M σ).pr (oddBad σ) := by
        simpa using (pr_as_weight_sum (anchorLaw Γ M σ) (oddBad σ)).symm
  have hoddP : P.pr (fun ω => oddBad ω.1 ω.2.1) =
      (FinProb.bind (tagLaw Γ M Q D₀) (anchorLaw Γ M)).pr (fun ω => oddBad ω.1 ω.2) := by
    have hexpand : P.pr (fun ω => oddBad ω.1 ω.2.1) =
        ∑ σ, (tagLaw Γ M Q D₀).w σ *
          (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr (fun wf => oddBad σ wf.1) := by
      simpa [P] using bind_pr_eq (tagLaw Γ M Q D₀)
        (fun σ => FinProb.bind (anchorLaw Γ M σ) (Jfam σ)) (fun σ wf => oddBad σ wf.1)
    calc
      P.pr (fun ω => oddBad ω.1 ω.2.1) =
        ∑ σ, (tagLaw Γ M Q D₀).w σ *
          (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr (fun wf => oddBad σ wf.1) := hexpand
      _ =
          ∑ σ, (tagLaw Γ M Q D₀).w σ * (anchorLaw Γ M σ).pr (oddBad σ) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [hoddKernel]
      _ = (FinProb.bind (tagLaw Γ M Q D₀) (anchorLaw Γ M)).pr (fun ω => oddBad ω.1 ω.2) :=
        (bind_pr_eq (tagLaw Γ M Q D₀) (anchorLaw Γ M) (fun σ W => oddBad σ W)).symm
  have hcellKernel (σ : Γ.Key → M.ι) :
      (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr
          (fun wf => cellBad σ wf.1) = (anchorLaw Γ M σ).pr (cellBad σ) := by
    have hexpand := bind_pr_eq (anchorLaw Γ M σ) (Jfam σ) (fun W _ => cellBad σ W)
    calc
      (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr (fun wf => cellBad σ wf.1) =
          ∑ W, (anchorLaw Γ M σ).w W * (Jfam σ W).pr (fun _ => cellBad σ W) := hexpand
      _ =
          ∑ W, (anchorLaw Γ M σ).w W * (if cellBad σ W then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [pr_const]
      _ = (anchorLaw Γ M σ).pr (cellBad σ) := by
        simpa using (pr_as_weight_sum (anchorLaw Γ M σ) (cellBad σ)).symm
  have hcellP : P.pr (fun ω => cellBad ω.1 ω.2.1) = 0 := by
    have hexpand : P.pr (fun ω => cellBad ω.1 ω.2.1) =
        ∑ σ, (tagLaw Γ M Q D₀).w σ *
          (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr (fun wf => cellBad σ wf.1) := by
      simpa [P] using bind_pr_eq (tagLaw Γ M Q D₀)
        (fun σ => FinProb.bind (anchorLaw Γ M σ) (Jfam σ)) (fun σ wf => cellBad σ wf.1)
    rw [hexpand]
    apply Finset.sum_eq_zero
    intro σ hσ
    by_cases hweight : (tagLaw Γ M Q D₀).w σ = 0
    · simp [hweight]
    · have hσgood := htagSupport σ hweight
      rw [hcellKernel]
      have hzero : (anchorLaw Γ M σ).pr (cellBad σ) = 0 := by
        simpa [cellBad] using hcellAvoidZero σ hσgood
      simp [hweight, hzero]
  have hevenKernel (σ : Γ.Key → M.ι) :
      (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr
          (fun wf => Typical Γ M C σ ∧ GoodPre Γ M σ wf.1 ∧ evenBad σ wf.1 wf.2) =
        if Typical Γ M C σ then
          ∑ W, (anchorLaw Γ M σ).w W *
            (if GoodPre Γ M σ W then (Jfam σ W).pr (evenBad σ W) else 0)
        else 0 := by
    have hexpand := bind_pr_eq (anchorLaw Γ M σ) (Jfam σ)
      (fun W f => Typical Γ M C σ ∧ GoodPre Γ M σ W ∧ evenBad σ W f)
    by_cases htyp0 : Typical Γ M C σ
    · calc
        (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr
            (fun wf => Typical Γ M C σ ∧ GoodPre Γ M σ wf.1 ∧ evenBad σ wf.1 wf.2) =
          ∑ W, (anchorLaw Γ M σ).w W *
            (Jfam σ W).pr (fun f => Typical Γ M C σ ∧ GoodPre Γ M σ W ∧ evenBad σ W f) := hexpand
        _ = ∑ W, (anchorLaw Γ M σ).w W *
            (if GoodPre Γ M σ W then (Jfam σ W).pr (evenBad σ W) else 0) := by
              apply Finset.sum_congr rfl
              intro W hW
              by_cases hpre : GoodPre Γ M σ W
              · simp only [htyp0, hpre, ↓reduceIte, true_and]
              · simp only [htyp0, hpre, ↓reduceIte, true_and, false_and,
                  pr_const, if_false, mul_zero]
        _ = if Typical Γ M C σ then
              ∑ W, (anchorLaw Γ M σ).w W *
                (if GoodPre Γ M σ W then (Jfam σ W).pr (evenBad σ W) else 0)
            else 0 := by simp [htyp0]
    · calc
        (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr
            (fun wf => Typical Γ M C σ ∧ GoodPre Γ M σ wf.1 ∧ evenBad σ wf.1 wf.2) =
          ∑ W, (anchorLaw Γ M σ).w W *
            (Jfam σ W).pr (fun f => Typical Γ M C σ ∧ GoodPre Γ M σ W ∧ evenBad σ W f) := hexpand
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro W hW
        simp only [htyp0, false_and, pr_const, if_false, mul_zero]
      _ = if Typical Γ M C σ then
            ∑ W, (anchorLaw Γ M σ).w W *
              (if GoodPre Γ M σ W then (Jfam σ W).pr (evenBad σ W) else 0)
          else 0 := by simp [htyp0]
  have hevenP : P.pr (fun ω => Typical Γ M C ω.1 ∧
      GoodPre Γ M ω.1 ω.2.1 ∧ evenBad ω.1 ω.2.1 ω.2.2) ≤ δ := by
    have hexpand : P.pr (fun ω => Typical Γ M C ω.1 ∧
        GoodPre Γ M ω.1 ω.2.1 ∧ evenBad ω.1 ω.2.1 ω.2.2) =
      ∑ σ, (tagLaw Γ M Q D₀).w σ *
        (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr
          (fun wf => Typical Γ M C σ ∧ GoodPre Γ M σ wf.1 ∧ evenBad σ wf.1 wf.2) := by
        simpa [P] using bind_pr_eq (tagLaw Γ M Q D₀)
          (fun σ => FinProb.bind (anchorLaw Γ M σ) (Jfam σ))
          (fun σ wf => Typical Γ M C σ ∧ GoodPre Γ M σ wf.1 ∧ evenBad σ wf.1 wf.2)
    calc
      P.pr (fun ω => Typical Γ M C ω.1 ∧
          GoodPre Γ M ω.1 ω.2.1 ∧ evenBad ω.1 ω.2.1 ω.2.2) =
          ∑ σ, (tagLaw Γ M Q D₀).w σ *
        (FinProb.bind (anchorLaw Γ M σ) (Jfam σ)).pr
          (fun wf => Typical Γ M C σ ∧ GoodPre Γ M σ wf.1 ∧ evenBad σ wf.1 wf.2) := hexpand
      _ =
          ∑ σ, (tagLaw Γ M Q D₀).w σ *
            (if Typical Γ M C σ then
              ∑ W, (anchorLaw Γ M σ).w W *
                (if GoodPre Γ M σ W then (Jfam σ W).pr (evenBad σ W) else 0)
             else 0) := by
              apply Finset.sum_congr rfl
              intro σ hσ
              rw [hevenKernel]
      _ ≤ ∑ σ, (tagLaw Γ M Q D₀).w σ * δ := by
        apply Finset.sum_le_sum
        intro σ hσ
        by_cases hweight : (tagLaw Γ M Q D₀).w σ = 0
        · rw [hweight]
          simp
        · have hσgood := htagSupport σ hweight
          by_cases htyp0 : Typical Γ M C σ
          · have hbound := heven σ hσgood htyp0 (Jfam σ) (hJfam σ)
            simp only [htyp0, ↓reduceIte]
            exact mul_le_mul_of_nonneg_left hbound ((tagLaw Γ M Q D₀).nonneg σ)
          · simp only [htyp0, ↓reduceIte]
            exact mul_le_mul_of_nonneg_left hδ_nonneg ((tagLaw Γ M Q D₀).nonneg σ)
      _ = δ := by
        calc
          (∑ σ, (tagLaw Γ M Q D₀).w σ * δ) =
              (∑ σ, (tagLaw Γ M Q D₀).w σ) * δ := by rw [Finset.sum_mul]
          _ = δ := by rw [(tagLaw Γ M Q D₀).sum_eq_one]; ring
  let badUnion (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N) : Prop :=
    ((tagBad σ ∨ cellBad σ W) ∨ oddBad σ W) ∨
      (Typical Γ M C σ ∧ GoodPre Γ M σ W ∧ evenBad σ W f)
  have hbadUnion : P.pr (fun ω => badUnion ω.1 ω.2.1 ω.2.2) ≤ 3 * δ := by
    calc
      P.pr (fun ω => badUnion ω.1 ω.2.1 ω.2.2) =
          P.pr (fun ω => ((tagBad ω.1 ∨ cellBad ω.1 ω.2.1) ∨ oddBad ω.1 ω.2.1) ∨
            (Typical Γ M C ω.1 ∧ GoodPre Γ M ω.1 ω.2.1 ∧ evenBad ω.1 ω.2.1 ω.2.2)) := rfl
      _ ≤ P.pr (fun ω => (tagBad ω.1 ∨ cellBad ω.1 ω.2.1) ∨ oddBad ω.1 ω.2.1) +
          P.pr (fun ω => Typical Γ M C ω.1 ∧ GoodPre Γ M ω.1 ω.2.1 ∧ evenBad ω.1 ω.2.1 ω.2.2) :=
        FinProb.pr_union P _ _
      _ ≤ (P.pr (fun ω => tagBad ω.1 ∨ cellBad ω.1 ω.2.1) +
            P.pr (fun ω => oddBad ω.1 ω.2.1)) +
          P.pr (fun ω => Typical Γ M C ω.1 ∧ GoodPre Γ M ω.1 ω.2.1 ∧ evenBad ω.1 ω.2.1 ω.2.2) := by
        have h := FinProb.pr_union P (fun ω => tagBad ω.1 ∨ cellBad ω.1 ω.2.1)
          (fun ω => oddBad ω.1 ω.2.1)
        nlinarith [h]
      _ ≤ ((P.pr (fun ω => tagBad ω.1) + P.pr (fun ω => cellBad ω.1 ω.2.1)) +
            P.pr (fun ω => oddBad ω.1 ω.2.1)) +
          P.pr (fun ω => Typical Γ M C ω.1 ∧ GoodPre Γ M ω.1 ω.2.1 ∧ evenBad ω.1 ω.2.1 ω.2.2) := by
        have h := FinProb.pr_union P (fun ω => tagBad ω.1) (fun ω => cellBad ω.1 ω.2.1)
        nlinarith [h]
      _ ≤ δ + (0 + (δ + δ)) := by
        rw [htagP, hcellP, hoddP]
        have htyp' : (tagLaw Γ M Q D₀).pr tagBad ≤ δ := by
          simpa [δ, tagBad] using htyp
        have hodd' : (FinProb.bind (tagLaw Γ M Q D₀) (anchorLaw Γ M)).pr
            (fun ω => oddBad ω.1 ω.2) ≤ δ := by
          simpa [δ, oddBad] using hodd
        nlinarith [htyp', hodd', hevenP]
      _ = 3 * δ := by ring
  have hnotSuccess : ∀ (ω : (Γ.Key → M.ι) × ((Γ.Cell → Fin N) × (OddRole n → Fin N))),
      ¬ success ω.1 ω.2.1 ω.2.2 →
      badUnion ω.1 ω.2.1 ω.2.2 := by
    intro ω hfail
    by_cases htyp0 : Typical Γ M C ω.1
    · by_cases hpre : GoodPre Γ M ω.1 ω.2.1
      · by_cases he : evenBad ω.1 ω.2.1 ω.2.2
        · exact Or.inr ⟨htyp0, hpre, he⟩
        · exfalso
          apply hfail
          refine ⟨htyp0, hpre, ?_⟩
          intro x
          exact le_of_not_gt (fun hx => he ⟨x, hx⟩)
      · have hpre' : ¬ ((∀ c, ¬ CellBad Γ M ω.1 ω.2.1 c) ∧
            ∀ y, oddColumn Γ M ω.1 ω.2.1 y ≤ (1e-8 : ℝ)) := by
          simpa [GoodPre] using hpre
        rcases (not_and_or.mp hpre') with hcell | hodd
        · exact Or.inl (Or.inl (Or.inr hcell))
        · have hy : ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2.1 y := by
            by_contra hnone
            have hall : ∀ y, oddColumn Γ M ω.1 ω.2.1 y ≤ (1e-8 : ℝ) := by
              intro y
              exact le_of_not_gt (fun hy => hnone ⟨y, hy⟩)
            exact hodd hall
          exact Or.inl (Or.inr hy)
    · exact Or.inl (Or.inl (Or.inl htyp0))
  have hbadMass : P.pr (fun ω => ¬ success ω.1 ω.2.1 ω.2.2) ≤ 3 * δ :=
    le_trans (pr_mono P (fun ω h => hnotSuccess ω h)) hbadUnion
  have hsuccessPos : 0 < P.pr (fun ω => success ω.1 ω.2.1 ω.2.2) := by
    have hcomp := pr_compl P (fun ω => success ω.1 ω.2.1 ω.2.2)
    linarith
  have hexists : ∃ ω, P.w ω ≠ 0 ∧ success ω.1 ω.2.1 ω.2.2 := by
    by_contra hnone
    push_neg at hnone
    have hzero : ∀ ω,
        (if success ω.1 ω.2.1 ω.2.2 then P.w ω else 0) = 0 := by
      intro ω
      by_cases hs : success ω.1 ω.2.1 ω.2.2
      · have hw : P.w ω = 0 := by
          by_contra hw
          exact (hnone ω hw) hs
        simp [hs, hw]
      · simp [hs]
    have : P.pr (fun ω => success ω.1 ω.2.1 ω.2.2) = 0 := by
      unfold FinProb.pr
      simp [hzero]
    linarith
  obtain ⟨ω, hωweight, hωsuccess⟩ := hexists
  obtain ⟨σ, ⟨W, f⟩⟩ := ω
  have htagWeight : (tagLaw Γ M Q D₀).w σ ≠ 0 := by
    intro hz
    apply hωweight
    simp [P, FinProb.bind, hz]
  have hWWeight : (anchorLaw Γ M σ).w W ≠ 0 := by
    intro hz
    apply hωweight
    simp [P, FinProb.bind, hz]
  have hfWeight : (Jfam σ W).w f ≠ 0 := by
    intro hz
    apply hωweight
    simp [P, FinProb.bind, hz]
  have hσ : ∀ g, ¬ TagBad Γ M D₀ σ g := htagSupport σ htagWeight
  have hcells : ∀ c, ¬ CellBad Γ M σ W c := hcellSupport σ hσ W hWWeight
  have hpre : GoodPre Γ M σ W := by
    rcases hωsuccess with ⟨htyp0, hpre, hcol⟩
    exact hpre
  have hclockOK : ClockOK Γ M σ W (Jfam σ W) := hJfam σ W hpre
  have hsample := (hclockOK.1 f hfWeight)
  refine ⟨σ, W, f, ?_, hsample.1, ?_, ?_⟩
  · intro c
    by_contra hvalid
    exact hcells c (Or.inl hvalid)
  · exact hsample.2
  · rcases hωsuccess with ⟨_, _, hcol⟩
    exact hcol

/-- F-HallEmbed input from a good realization (07:389–392): the posterior even rows are probability laws on the
common neighbourhoods of the injective odd labels, with column sums at most one. -/
theorem hall_data_of_realization {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hlaw : EvenRowLaw Γ M) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N)
    (hinj : Function.Injective f) (hpf : ∀ a : EvenRole n, ¬ PredFail Γ M σ W a.1 (nbrLabels f a))
    (hcol : ∀ x, evenColumn Γ M σ W f x ≤ 1) : GridHallData (n := n) E G :=
  ⟨f, fun a x => evenRow Γ M σ W f a x, hinj, fun a x => (hlaw σ W f a (hpf a)).1 x,
    fun a => (hlaw σ W f a (hpf a)).2.1, fun a x hx => (hlaw σ W f a (hpf a)).2.2 x hx, hcol⟩

/-- L7.1, Steps 1–6 assembled at one dimension: on sets satisfying (7.1), every geometry and menu of the lemma
admit a good realization. -/
theorem grid_realization (D₀ d p κ : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10) (hd : 0 < d)
    (hd' : d < D₀ / 1000) (hp : 0 < p) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ), Eq71At D₀ d n N E X Y →
        ∃ (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N),
          (∀ c, CellValid Γ M σ W c) ∧ Function.Injective f ∧
          (∀ a : EvenRole n, ¬ PredFail Γ M σ W a.1 (nbrLabels f a)) ∧
          ∀ x, evenColumn Γ M σ W f x ≤ 1 := by
  have hd8 : d < 1 / 8 := by linarith
  set K : ℝ := 4 / κ with hKdef
  have hK : 0 ≤ K := by positivity
  set C : ℝ := 8 * (K + 1) with hCdef
  have hC : 0 ≤ C := by positivity
  obtain ⟨nF, hfilt⟩ := filterFacts d hd hd8
  obtain ⟨nT, htag⟩ := tag_stage D₀ d K hD₀ hD₀' hd hd' hK
  obtain ⟨nA, CA, hanchor⟩ := anchor_stage D₀ d p K hD₀ hD₀' hd hd' hp hK
  obtain ⟨nK, CK, hclock⟩ := clock_rows d hd hd8
  obtain ⟨nE, CE, heven⟩ := even_stage D₀ d C hD₀ hD₀' hd hd' hC
  obtain ⟨nR, hreal⟩ := grid_realization_of
  refine ⟨max (max (max nF nT) (max nA nK)) (max nE nR), max (max CA CK) (max CE 1), ?_⟩
  intro n N hL E G X Y Γ M h71
  have hn : max (max (max nF nT) (max nA nK)) (max nE nR) ≤ n := hL.1
  have hnF : nF ≤ n := by omega
  have hnT : nT ≤ n := by omega
  have hnR : nR ≤ n := by omega
  have hLA : LargeAt nA CA n N :=
    largeAt_weaken hL (by omega) (le_trans (le_max_left CA CK) (le_max_left _ _))
  have hLK : LargeAt nK CK n N :=
    largeAt_weaken hL (by omega) (le_trans (le_max_right CA CK) (le_max_left _ _))
  have hLE : LargeAt nE CE n N :=
    largeAt_weaken hL (by omega) (le_trans (le_max_left CE 1) (le_max_right _ _))
  have hNreal : (1 : ℝ) * 2 ^ n ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right (le_trans (le_max_right CE 1) (le_max_right _ _))
      (by positivity)) hL.2.1
  have hN : 0 < N := by
    have h2 : (0 : ℝ) < 1 * 2 ^ n := by positivity
    exact_mod_cast lt_of_lt_of_le h2 hNreal
  have hG : GeomFacts Γ := geomFacts Γ
  have hF : FilterFacts Γ M := hfilt n hnF Γ M hN hG
  obtain ⟨P⟩ := grid_profiles balanced_mixture_sub Γ M hκ hN hF.row_law
  obtain ⟨hT, htyp⟩ := htag n hnT Γ M P hN hL.2.2 hG h71
  obtain ⟨hA, hodd⟩ := hanchor n N hLA Γ M P hG hF hT
  exact hreal n hnR Γ M P.Q D₀ C hN htyp hodd (cond_product_bound _ _ _ _ _ hT).1
    (fun σ hσ => (cond_product_bound _ _ _ _ _ (hA σ hσ)).1)
    (fun σ W hW => hclock n N hLK Γ M σ W hG.loc hF.row_law hF.row_cap hW)
    (fun σ hσ hty J hJ => heven n N hLE Γ M σ J hG hF (hA σ hσ) hty hJ)

/-- Lemma 7.1 before the Hall step: the one-shot hypotheses give Hall data. -/
theorem grid_hall_data_from_input
    (D₀ d p₀ κ : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10)
    (hd : 0 < d) (hd' : d < D₀ / 1000) (hp₀ : 0 < p₀) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
      ∀ X Y : Finset (Fin N), ∀ G : Colour,
        LargeAt n₀ C₀ n N → Eq71At D₀ d n N E X Y →
        AvailableAt κ (PGridPure G d p₀).toPatch n N E X Y → GridHallData (n := n) E G := by
  have hd8 : d < 1 / 8 := by linarith
  obtain ⟨nG, hgeom⟩ := gridGeom_exists d hd hd8
  obtain ⟨nF, hfilt⟩ := filterFacts d hd hd8
  obtain ⟨nR, CR, hreal⟩ := grid_realization D₀ d p₀ κ hD₀ hD₀' hd hd' hp₀ hκ
  refine ⟨max (max nG nF) nR, max CR 1, ?_⟩
  intro n N E X Y G hL h71 havail
  have hn : max (max nG nF) nR ≤ n := hL.1
  have hnG : nG ≤ n := by omega
  have hnF : nF ≤ n := by omega
  have hLR : LargeAt nR CR n N := largeAt_weaken hL (by omega) (le_max_left _ _)
  have hNreal : (1 : ℝ) * 2 ^ n ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right CR 1) (by positivity)) hL.2.1
  have hN : 0 < N := by
    have h2 : (0 : ℝ) < 1 * 2 ^ n := by positivity
    exact_mod_cast lt_of_lt_of_le h2 hNreal
  obtain ⟨M⟩ := menu7_of_available hκ.le havail
  obtain ⟨Γ⟩ := hgeom n hnG
  have hF : FilterFacts Γ M := hfilt n hnF Γ M hN (geomFacts Γ)
  obtain ⟨σ, W, f, _hvalid, hinj, hpf, hcol⟩ := hreal n N hLR Γ M h71
  exact hall_data_of_realization Γ M hF.evenRow_law σ W f hinj hpf hcol

/-- L7.1 (07:41–391), the one-shot small-grid purity exclusion. -/
theorem small_grid_purity
    (D₀ d p₀ κ : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10)
    (hd : 0 < d) (hd' : d < D₀ / 1000) (hp₀ : 0 < p₀) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
      ∀ X Y : Finset (Fin N), ∀ G : Colour,
        LargeAt n₀ C₀ n N → Eq71At D₀ d n N E X Y →
        AvailableAt κ (PGridPure G d p₀).toPatch n N E X Y → CubeAt n N E := by
  obtain ⟨n₀, C₀, hnode⟩ := by
    exact grid_hall_data_from_input D₀ d p₀ κ hD₀ hD₀' hd hd' hp₀ hκ
  refine ⟨n₀, C₀, ?_⟩
  intro n N E X Y G hlarge h71 havail
  obtain ⟨fB, p, hinj, hp0, hp1, hsupp, hload⟩ :=
    hnode n N E X Y G hlarge h71 havail
  exact cubeAt_of_rows E G fB hinj p hp0 hp1 hsupp hload

end HypercubeRamsey.S07
