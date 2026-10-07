import HypercubeRamsey.S10.Transfer_sol_s10_1k
import HypercubeRamsey.S10.LocalNodes
import HypercubeRamsey.Framework.Props
import HypercubeRamsey.S10.Split_opus_s10_row_q_s10_c

/-!
# Section 10: split of the even-row construction (TeX 10:23–294)

`hconstruction` in `ClusterExclusion.lean` asks for a
`Lane_sol_s10_1k.RowExperiment` from `LargeAt`, the initial discrepancy and
cluster availability. This file splits it along the paper's order of
argument, from the end backwards:

* `rowExperiment_of_transferData` (10:281–294): clock injection, transfer of
  the reference estimates through the clock comparison, scattered even
  moments. Input: `TransferData`, a prehistory/cluster/reference-label
  experiment with its reference-law estimates.
* `transferData_of_typical` (10:271–281): odd column sums of the prehistory
  rows (scattered moments) and cluster column sums (independent groups,
  exponential Markov). Input: `TypicalSystem`, the experiment at fixed
  typical tags.
* `typical_of_tagged` (10:263–269): simultaneous balanced tag profiles and
  typical tags (scattered moments over the product tag law). Input:
  `TaggedSystem`, the experiment for every tag assignment.
* `tagged_of_menu` (10:23–262): the construction itself (projections,
  heights, eligibility, tilts, masks, lists, likelihoods, predictive tests and
  posterior rows) with its local estimates. Input: `PatchMenu`.
* `patchMenu_of_available` (10:23–24): a finite menu from availability.

The assembly `rowExperiment_eventually` composes them with the clock lemma.
-/

namespace HypercubeRamsey.Lane_opus_s10_row

open Classical OAI.HypercubeRamsey Filter
open scoped BigOperators

/-- Odd roles of the cube. -/
abbrev OddRole (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

/-- Even roles of the cube. -/
abbrev EvenRole (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

/-- The odd neighbours of an even role. -/
noncomputable def star {n : ℕ} (a : EvenRole n) : Finset (OddRole n) :=
  Finset.univ.filter fun b => (cube n).Adj a.1 b.1

/-- An even role has at most `n` odd neighbours. -/
theorem star_card_le {n : ℕ} (a : EvenRole n) : (star a).card ≤ n := by
  classical
  let f : OddRole n → Finset (Fin n) := fun b => Finset.univ.filter fun i => a.1 i ≠ b.1 i
  let t : Finset (Finset (Fin n)) := Finset.univ.image fun i : Fin n => ({i} : Finset (Fin n))
  have hmaps : ∀ b ∈ star a, f b ∈ t := by
    intro b hb
    have hadj : (cube n).Adj a.1 b.1 := (Finset.mem_filter.mp hb).2
    have hone : (Finset.univ.filter (fun i : Fin n => a.1 i ≠ b.1 i)).card = 1 := hadj
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩
  have hinj : Set.InjOn f (star a : Set (OddRole n)) := by
    intro b _ b' _ hbb'
    apply Subtype.ext
    funext i
    have hi : a.1 i ≠ b.1 i ↔ a.1 i ≠ b'.1 i := by
      have := congrArg (fun s : Finset (Fin n) => i ∈ s) hbb'
      simpa [f] using this
    cases ha : a.1 i <;> cases hb : b.1 i <;> cases hb' : b'.1 i <;> simp_all
  calc (star a).card ≤ t.card :=
        Finset.card_le_card_of_injOn f
          (fun b hb => Finset.mem_coe.mpr (hmaps b (Finset.mem_coe.mp hb))) hinj
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

instance evenRole_nonempty (n : ℕ) : Nonempty (EvenRole n) :=
  ⟨⟨fun _ => false, by simp [IsEvenRole]⟩⟩

/-- The clock lemma at one dimension with no forbidden predicates and at most
`n²` queried rows (TeX 10:281, Lemma 3.10). -/
def ClockAt (n N : ℕ) (A ε : ℝ) : Prop :=
  ∀ {R : Type} [Fintype R] [DecidableEq R] (p : R → FinProb (Fin N)),
    (∀ y, ∑ a, (p a).w y ≤ 1e-8) → (∀ a y, (p a).w y ≤ (n : ℝ) ^ (-A)) →
    ∃ J : FinProb (R → Fin N), (∀ ω, J.w ω ≠ 0 → Function.Injective ω) ∧
      ∀ (S : Finset R) (o : R → Fin N), (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) →
        J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤ (1 + ε) * ∏ a ∈ S, (p a).w (o a)

/-! ## Stage 4: the transfer experiment (TeX 10:281–294) -/

/-- The experiment entering the transfer paragraph (10:283–292). `H` is the
pre-cluster history at the fixed typical tags, `K h` the law of the cluster
configuration, and `lab h c b` the reference law of the odd label of `b` given
the clusters. `goodH` is the entering success of the prehistory (validity and
small odd columns); `clusterGood` is the cluster-column success at which the
clock lemma applies. The even predictive events and rows read the odd labels
of their star only. The three estimates are stated under the reference law
(independent odd labels given clusters), with the prehistory indicator still
present; the clock comparison is done in `rowExperiment_of_transferData`. -/
structure TransferData (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (A : ℝ) where
  H : Type
  [fH : Fintype H]
  PH : FinProb H
  goodH : H → Prop
  C : Type
  [fC : Fintype C]
  K : H → FinProb C
  lab : H → C → OddRole n → FinProb (Fin N)
  clusterGood : H → C → Prop
  column_small : ∀ h c, goodH h → clusterGood h c → ∀ y, ∑ b, (lab h c b).w y ≤ 1e-8
  atom_small : ∀ h c, goodH h → clusterGood h c → ∀ b y, (lab h c b).w y ≤ (n : ℝ) ^ (-A)
  predictive : EvenRole n → H → (OddRole n → Fin N) → Prop
  row : H → (OddRole n → Fin N) → EvenRole n → Fin N → ℝ
  row_nonneg : ∀ h ω a x, 0 ≤ row h ω a x
  row_sum : ∀ h ω a, goodH h → predictive a h ω → ∑ x, row h ω a x = 1
  common_neighbor : ∀ h ω a, goodH h → predictive a h ω → ∀ x, row h ω a x ≠ 0 →
    ∀ b : OddRole n, (cube n).Adj a.1 b.1 → Hits E G x (ω b)
  predictive_local : ∀ a h, FinProb.DependsOn (fun ω => predictive a h ω) (star a)
  row_local : ∀ a h x, FinProb.DependsOn (fun ω => row h ω a x) (star a)
  rowCap : ℝ
  rowCap_nonneg : 0 ≤ rowCap
  row_cap : ∀ h ω a x, goodH h → (N : ℝ) * row h ω a x ≤ rowCap
  near : EvenRole n → Finset (EvenRole n)
  near_self : ∀ a, a ∈ near a
  nearFrac : ℝ
  near_card : ∀ a, ((near a).card : ℝ) ≤ nearFrac * Fintype.card (EvenRole n)
  jointConst : ℝ
  jointConst_ge : 1 ≤ jointConst
  mean : Fin N → EvenRole n → ℝ
  mean_nonneg : ∀ x a, 0 ≤ mean x a
  meanAvg : ℝ
  mean_avg : ∀ x, (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, mean x a ≤ meanAvg
  ref_joint : ∀ x (m : ℕ), m ≤ n → ∀ s : Fin m → EvenRole n,
    (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
      ∑ h, PH.w h * (if goodH h then ∑ c, (K h).w c *
        (FinProb.pi (lab h c)).expect (fun ω => ∏ i, (N : ℝ) * row h ω (s i) x) else 0)
        ≤ jointConst ^ m * ∏ i, mean x (s i)
  ε_pre : ℝ
  ε_cluster : ℝ
  ε_ref : ℝ
  pre_failure : PH.pr (fun h => ¬ goodH h) ≤ ε_pre
  cluster_failure : ∑ h, PH.w h *
    (if goodH h then (K h).pr (fun c => ¬ clusterGood h c) else 0) ≤ ε_cluster
  ref_predictive : ∀ a, ∑ h, PH.w h * (if goodH h then ∑ c, (K h).w c *
      (FinProb.pi (lab h c)).pr (fun ω => ¬ predictive a h ω) else 0) ≤ ε_ref
  N_pos : 0 < N
  budget : ε_pre + ε_cluster + Fintype.card (EvenRole n) * (2 * ε_ref) +
    N * (((Fintype.card (EvenRole n) : ℝ) / N) * (2 * jointConst) *
      (meanAvg + n * nearFrac * rowCap)) ^ n < 1

attribute [instance] TransferData.fH TransferData.fC

set_option maxHeartbeats 1000000 in
/-- **Sub-lemma (a)**, TeX 10:281–294. Draw the clock labels at clock-good
cluster histories, compare each queried star and each family of at most `n`
separated stars with the reference law (`Lane_sol_s10_1k.query_expect_le`),
and apply scattered moments to the even columns. -/
theorem rowExperiment_of_transferData {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {A ε : ℝ} (D : TransferData n N E G A)
    (hclock : ClockAt n N A ε) (hε₀ : -1 ≤ ε) (hε₁ : ε ≤ 1) :
    Nonempty (Lane_sol_s10_1k.RowExperiment n N E G) := by
  classical
  have hC0 : 0 ≤ 1 + ε := by linarith
  have hC2 : 1 + ε ≤ 2 := by linarith
  -- the clock law at clock-good cluster histories
  have hspec : ∀ h c, D.goodH h → D.clusterGood h c →
      ∃ J : FinProb (OddRole n → Fin N), (∀ ω, J.w ω ≠ 0 → Function.Injective ω) ∧
        ∀ (S : Finset (OddRole n)) (o : OddRole n → Fin N),
          (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) →
          J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤ (1 + ε) * ∏ a ∈ S, (D.lab h c a).w (o a) :=
    fun h c hg hc => hclock (D.lab h c) (D.column_small h c hg hc) (D.atom_small h c hg hc)
  let Jc : D.H → D.C → FinProb (OddRole n → Fin N) := fun h c =>
    if hg : D.goodH h ∧ D.clusterGood h c then Classical.choose (hspec h c hg.1 hg.2)
    else FinProb.pi (D.lab h c)
  have hJ : ∀ h c, D.goodH h → D.clusterGood h c →
      (∀ ω, (Jc h c).w ω ≠ 0 → Function.Injective ω) ∧
      ∀ (S : Finset (OddRole n)) (o : OddRole n → Fin N),
        (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) →
        (Jc h c).pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
          (1 + ε) * ∏ a ∈ S, (D.lab h c a).w (o a) := by
    intro h c hg hc
    have hJc : Jc h c = Classical.choose (hspec h c hg hc) := by
      simp only [Jc, dif_pos (And.intro hg hc)]
    rw [hJc]
    exact Classical.choose_spec (hspec h c hg hc)
  have hcmp : ∀ h c, D.goodH h → D.clusterGood h c → ∀ (S : Finset (OddRole n))
      (F : (OddRole n → Fin N) → ℝ), (∀ ω, 0 ≤ F ω) → FinProb.DependsOn F S →
      (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) →
      (Jc h c).expect F ≤ (1 + ε) * (FinProb.pi (D.lab h c)).expect F := by
    intro h c hg hc S F hF hdep hS
    exact Lane_sol_s10_1k.query_expect_le (Ω := fun _ => Fin N) (D.lab h c) (Jc h c) S
      (1 + ε) F hF hdep (fun o => (hJ h c hg hc).2 S o hS)
  -- the outcome space and its law
  let law : FinProb ((D.H × D.C) × (OddRole n → Fin N)) :=
    FinProb.bind (FinProb.bind D.PH D.K) (fun hc => Jc hc.1 hc.2)
  let goodP : (D.H × D.C) × (OddRole n → Fin N) → Prop :=
    fun o => D.goodH o.1.1 ∧ D.clusterGood o.1.1 o.1.2
  let good : Finset ((D.H × D.C) × (OddRole n → Fin N)) := Finset.univ.filter goodP
  have hlaw : ∀ f : (D.H × D.C) × (OddRole n → Fin N) → ℝ, ∑ o, law.w o * f o =
      ∑ h, D.PH.w h * ∑ c, (D.K h).w c * ∑ ω, (Jc h c).w ω * f ((h, c), ω) := by
    intro f
    simp only [law, FinProb.bind, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro ω _
    ring
  have hgoodsum : ∀ f : (D.H × D.C) × (OddRole n → Fin N) → ℝ,
      ∑ o ∈ good, law.w o * f o = ∑ h, D.PH.w h * ∑ c, (D.K h).w c *
        (if D.goodH h ∧ D.clusterGood h c then
          (Jc h c).expect (fun ω => f ((h, c), ω)) else 0) := by
    intro f
    calc ∑ o ∈ good, law.w o * f o = ∑ o, law.w o * (if goodP o then f o else 0) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro o _
          split_ifs <;> simp
      _ = _ := hlaw _
      _ = _ := by
          apply Finset.sum_congr rfl; intro h _; congr 1
          apply Finset.sum_congr rfl; intro c _; congr 1
          by_cases hp : D.goodH h ∧ D.clusterGood h c
          · rw [if_pos hp]
            unfold FinProb.expect
            apply Finset.sum_congr rfl; intro ω _
            have hp' : goodP ((h, c), ω) := hp
            rw [if_pos hp']
          · rw [if_neg hp]
            apply Finset.sum_eq_zero; intro ω _
            have hp' : ¬ goodP ((h, c), ω) := hp
            rw [if_neg hp', mul_zero]
  have hprsum : ∀ A : (D.H × D.C) × (OddRole n → Fin N) → Prop,
      law.pr A = ∑ o, law.w o * (if A o then 1 else 0) := by
    intro A
    unfold FinProb.pr
    apply Finset.sum_congr rfl; intro o _
    split_ifs <;> simp
  -- entering failure
  have henter : law.pr (fun o => o ∉ good) ≤ D.ε_pre + D.ε_cluster := by
    have h1 : law.pr (fun o => o ∉ good) = ∑ h, D.PH.w h *
        ((if D.goodH h then 0 else 1) +
          (if D.goodH h then (D.K h).pr (fun c => ¬ D.clusterGood h c) else 0)) := by
      rw [hprsum, hlaw]
      beta_reduce
      apply Finset.sum_congr rfl; intro h _; congr 1
      by_cases hg : D.goodH h
      · rw [if_pos hg, if_pos hg, zero_add]
        unfold FinProb.pr
        apply Finset.sum_congr rfl; intro c _
        by_cases hc : D.clusterGood h c
        · rw [if_neg (not_not.mpr hc)]
          apply mul_eq_zero_of_right
          apply Finset.sum_eq_zero; intro ω _
          have hm : ((h, c), ω) ∈ good := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg, hc⟩
          rw [if_neg (not_not.mpr hm), mul_zero]
        · rw [if_pos hc]
          have hm : ∀ ω, ((h, c), ω) ∉ good := fun ω hm => hc (Finset.mem_filter.mp hm).2.2
          calc (D.K h).w c * _ = (D.K h).w c * 1 := by
                congr 1
                calc _ = ∑ ω, (Jc h c).w ω := by
                      apply Finset.sum_congr rfl; intro ω _; rw [if_pos (hm ω), mul_one]
                  _ = 1 := (Jc h c).sum_eq_one
            _ = (D.K h).w c := mul_one _
      · rw [if_neg hg, if_neg hg, add_zero]
        calc _ = ∑ c, (D.K h).w c := by
              apply Finset.sum_congr rfl; intro c _
              have hm : ∀ ω, ((h, c), ω) ∉ good := fun ω hm => hg (Finset.mem_filter.mp hm).2.1
              calc (D.K h).w c * _ = (D.K h).w c * 1 := by
                    congr 1
                    calc _ = ∑ ω, (Jc h c).w ω := by
                          apply Finset.sum_congr rfl; intro ω _; rw [if_pos (hm ω), mul_one]
                      _ = 1 := (Jc h c).sum_eq_one
                _ = (D.K h).w c := mul_one _
          _ = 1 := (D.K h).sum_eq_one
    rw [h1]
    have hsplit : ∑ h, D.PH.w h * ((if D.goodH h then 0 else 1) +
          (if D.goodH h then (D.K h).pr (fun c => ¬ D.clusterGood h c) else 0)) =
        D.PH.pr (fun h => ¬ D.goodH h) + ∑ h, D.PH.w h *
          (if D.goodH h then (D.K h).pr (fun c => ¬ D.clusterGood h c) else 0) := by
      unfold FinProb.pr
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro h _
      by_cases hg : D.goodH h <;> simp [hg]
    rw [hsplit]
    exact add_le_add D.pre_failure D.cluster_failure
  -- predictive failures
  have hpred : ∀ a, law.pr (fun o => o ∈ good ∧ ¬ D.predictive a o.1.1 o.2) ≤
      2 * D.ε_ref := by
    intro a
    have h1 : law.pr (fun o => o ∈ good ∧ ¬ D.predictive a o.1.1 o.2) =
        ∑ o ∈ good, law.w o * (if ¬ D.predictive a o.1.1 o.2 then 1 else 0) := by
      rw [hprsum, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro o _
      by_cases hg : goodP o
      · have hm : o ∈ good := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
        by_cases hp : D.predictive a o.1.1 o.2
        · rw [if_pos hg, if_neg (fun h' => h'.2 hp), if_neg (not_not.mpr hp)]
        · rw [if_pos hg, if_pos ⟨hm, hp⟩, if_pos hp]
      · have hm : o ∉ good := fun hm => hg (Finset.mem_filter.mp hm).2
        rw [if_neg hg, if_neg (fun h' => hm h'.1), mul_zero]
    rw [h1, hgoodsum]
    set S0 := ∑ h, D.PH.w h * (if D.goodH h then ∑ c, (D.K h).w c *
      (FinProb.pi (D.lab h c)).pr (fun ω => ¬ D.predictive a h ω) else 0) with hS0
    have hS0nn : 0 ≤ S0 := by
      apply Finset.sum_nonneg; intro h _
      apply mul_nonneg (D.PH.nonneg h)
      split_ifs
      · exact Finset.sum_nonneg fun c _ => mul_nonneg ((D.K h).nonneg c)
          (Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [(FinProb.pi _).nonneg ω])
      · exact le_rfl
    have hstep : ∑ h, D.PH.w h * ∑ c, (D.K h).w c *
        (if D.goodH h ∧ D.clusterGood h c then
          (Jc h c).expect (fun ω => if ¬ D.predictive a h ω then (1 : ℝ) else 0) else 0) ≤
        (1 + ε) * S0 := by
      rw [hS0, Finset.mul_sum]
      apply Finset.sum_le_sum; intro h _
      rw [← mul_assoc, mul_comm (1 + ε) (D.PH.w h), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (D.PH.nonneg h)
      by_cases hg : D.goodH h
      · rw [if_pos hg, Finset.mul_sum]
        apply Finset.sum_le_sum; intro c _
        rw [← mul_assoc, mul_comm (1 + ε) ((D.K h).w c), mul_assoc]
        apply mul_le_mul_of_nonneg_left _ ((D.K h).nonneg c)
        have hprpi : (FinProb.pi (D.lab h c)).pr (fun ω => ¬ D.predictive a h ω) =
            (FinProb.pi (D.lab h c)).expect
              (fun ω => if ¬ D.predictive a h ω then (1 : ℝ) else 0) := by
          unfold FinProb.pr FinProb.expect
          apply Finset.sum_congr rfl; intro ω _
          beta_reduce
          by_cases hp : D.predictive a h ω
          · rw [if_neg (not_not.mpr hp), if_neg (not_not.mpr hp), mul_zero]
          · rw [if_pos hp, if_pos hp, mul_one]
        by_cases hc : D.clusterGood h c
        · rw [if_pos ⟨hg, hc⟩, hprpi]
          apply hcmp h c hg hc (star a)
          · intro ω; split_ifs <;> norm_num
          · intro ω ω' hω
            have := D.predictive_local a h ω ω' hω
            simp only [this]
          · have hcard : ((star a).card : ℝ) ≤ n := by exact_mod_cast star_card_le a
            have hn : (n : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
              rcases Nat.eq_zero_or_pos n with h0 | h0
              · simp [h0]
              · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
                nlinarith
            linarith
        · rw [if_neg (fun h' => hc h'.2)]
          apply mul_nonneg hC0
          unfold FinProb.pr
          exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [(FinProb.pi _).nonneg ω]
      · rw [if_neg hg, mul_zero]
        apply le_of_eq
        apply Finset.sum_eq_zero; intro c _
        rw [if_neg (fun h' => hg h'.1), mul_zero]
    calc _ ≤ (1 + ε) * S0 := hstep
      _ ≤ 2 * S0 := mul_le_mul_of_nonneg_right hC2 hS0nn
      _ ≤ 2 * D.ε_ref := by
          have := D.ref_predictive a
          linarith
  -- even column moments
  let moment : ℝ := (((Fintype.card (EvenRole n) : ℝ) / N) * (2 * D.jointConst) *
    (D.meanAvg + n * D.nearFrac * D.rowCap)) ^ n
  have hUpos : (0 : ℝ) < Fintype.card (EvenRole n) := by exact_mod_cast Fintype.card_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast D.N_pos
  have hcolumn : ∀ x, ∑ o ∈ good, law.w o * (∑ a, D.row o.1.1 o.2 a x) ^ n ≤ moment := by
    intro x
    let Z : EvenRole n → (D.H × D.C) × (OddRole n → Fin N) → ℝ :=
      fun a o => (N : ℝ) * D.row o.1.1 o.2 a x
    have hZ0 : ∀ a o, 0 ≤ Z a o := fun a o =>
      mul_nonneg (Nat.cast_nonneg _) (D.row_nonneg _ _ _ _)
    have hZL : ∀ a, ∀ o ∈ good, Z a o ≤ D.rowCap := fun a o ho =>
      D.row_cap _ _ _ _ (Finset.mem_filter.mp ho).2.1
    have hjoint : ∀ (m : ℕ), m ≤ n → ∀ s : Fin m → EvenRole n,
        (∀ i j : Fin m, j < i → s i ∉ D.near (s j)) →
          ∑ o ∈ good, law.w o * ∏ i, Z (s i) o ≤
            (2 * D.jointConst) ^ m * ∏ i, D.mean x (s i) := by
      intro m hm s hsep
      rcases Nat.eq_zero_or_pos m with h0 | hmpos
      · subst h0
        simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, pow_zero]
        calc ∑ o ∈ good, law.w o ≤ ∑ o, law.w o :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun o _ _ => law.nonneg o)
          _ = 1 := law.sum_eq_one
      let S : Finset (OddRole n) := Finset.univ.biUnion fun i => star (s i)
      have hScard : (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
        have h1 : S.card ≤ ∑ i, (star (s i)).card := Finset.card_biUnion_le
        have h2 : ∑ i, (star (s i)).card ≤ ∑ _i : Fin m, n :=
          Finset.sum_le_sum fun i _ => star_card_le (s i)
        have h3 : ∑ _i : Fin m, n = m * n := by simp
        have h4 : S.card ≤ n * n := by
          calc S.card ≤ m * n := by omega
            _ ≤ n * n := Nat.mul_le_mul_right n hm
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have : ((S.card : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast h4
        simpa [sq] using this
      let F : D.H → (OddRole n → Fin N) → ℝ := fun h ω => ∏ i, (N : ℝ) * D.row h ω (s i) x
      have hF0 : ∀ h ω, 0 ≤ F h ω := fun h ω =>
        Finset.prod_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (D.row_nonneg _ _ _ _)
      have hFdep : ∀ h, FinProb.DependsOn (F h) S := by
        intro h ω ω' hω
        apply Finset.prod_congr rfl; intro i _
        congr 1
        apply D.row_local (s i) h x ω ω'
        intro b hb
        exact hω b (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩)
      have hpiNN : ∀ h c, 0 ≤ (FinProb.pi (D.lab h c)).expect (F h) := fun h c =>
        Finset.sum_nonneg fun ω _ => mul_nonneg ((FinProb.pi _).nonneg ω) (hF0 h ω)
      set S1 := ∑ h, D.PH.w h * (if D.goodH h then ∑ c, (D.K h).w c *
        (FinProb.pi (D.lab h c)).expect (F h) else 0) with hS1
      have hS1nn : 0 ≤ S1 := by
        apply Finset.sum_nonneg; intro h _
        apply mul_nonneg (D.PH.nonneg h)
        split_ifs
        · exact Finset.sum_nonneg fun c _ => mul_nonneg ((D.K h).nonneg c) (hpiNN h c)
        · exact le_rfl
      have hS1le : S1 ≤ D.jointConst ^ m * ∏ i, D.mean x (s i) :=
        D.ref_joint x m hm s hsep
      have hstep : ∑ h, D.PH.w h * ∑ c, (D.K h).w c *
          (if D.goodH h ∧ D.clusterGood h c then (Jc h c).expect (F h) else 0) ≤
          (1 + ε) * S1 := by
        rw [hS1, Finset.mul_sum]
        apply Finset.sum_le_sum; intro h _
        rw [← mul_assoc, mul_comm (1 + ε) (D.PH.w h), mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (D.PH.nonneg h)
        by_cases hg : D.goodH h
        · rw [if_pos hg, Finset.mul_sum]
          apply Finset.sum_le_sum; intro c _
          rw [← mul_assoc, mul_comm (1 + ε) ((D.K h).w c), mul_assoc]
          apply mul_le_mul_of_nonneg_left _ ((D.K h).nonneg c)
          by_cases hc : D.clusterGood h c
          · rw [if_pos ⟨hg, hc⟩]
            exact hcmp h c hg hc S (F h) (hF0 h) (hFdep h) hScard
          · rw [if_neg (fun h' => hc h'.2)]
            exact mul_nonneg hC0 (hpiNN h c)
        · rw [if_neg hg, mul_zero]
          apply le_of_eq
          apply Finset.sum_eq_zero; intro c _
          rw [if_neg (fun h' => hg h'.1), mul_zero]
      have hprodnn : 0 ≤ D.jointConst ^ m * ∏ i, D.mean x (s i) :=
        mul_nonneg (pow_nonneg (by linarith [D.jointConst_ge]) m)
          (Finset.prod_nonneg fun i _ => D.mean_nonneg x (s i))
      have h2m : (2 : ℝ) ≤ 2 ^ m := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hmpos
      calc ∑ o ∈ good, law.w o * ∏ i, Z (s i) o
          = ∑ h, D.PH.w h * ∑ c, (D.K h).w c *
              (if D.goodH h ∧ D.clusterGood h c then (Jc h c).expect (F h) else 0) :=
            hgoodsum _
        _ ≤ (1 + ε) * S1 := hstep
        _ ≤ 2 * S1 := mul_le_mul_of_nonneg_right hC2 hS1nn
        _ ≤ 2 * (D.jointConst ^ m * ∏ i, D.mean x (s i)) :=
            mul_le_mul_of_nonneg_left hS1le (by norm_num)
        _ ≤ 2 ^ m * (D.jointConst ^ m * ∏ i, D.mean x (s i)) :=
            mul_le_mul_of_nonneg_right h2m hprodnn
        _ = (2 * D.jointConst) ^ m * ∏ i, D.mean x (s i) := by rw [mul_pow]; ring
    have hsc := scattered_moments law.w law.nonneg good Z hZ0 D.rowCap D.rowCap_nonneg hZL
      D.near D.near_self D.nearFrac D.near_card n (2 * D.jointConst)
      (by linarith [D.jointConst_ge]) (D.mean x) (D.mean_nonneg x) hjoint
    have hrow : ∀ o, (∑ a, D.row o.1.1 o.2 a x) ^ n =
        ((Fintype.card (EvenRole n) : ℝ) / N) ^ n * ((Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, Z a o) ^ n := by
      intro o
      rw [← mul_pow]
      congr 1
      have hsumZ : ∑ a, Z a o = (N : ℝ) * ∑ a, D.row o.1.1 o.2 a x := by
        simp only [Z]; rw [← Finset.mul_sum]
      rw [hsumZ]
      field_simp
    have hfrac : 0 ≤ D.nearFrac := by
      have h1 := D.near_card (Classical.arbitrary (EvenRole n))
      have h2 : (1 : ℝ) ≤ (D.near (Classical.arbitrary (EvenRole n))).card := by
        exact_mod_cast Finset.card_pos.mpr ⟨_, D.near_self _⟩
      by_contra hneg
      push_neg at hneg
      nlinarith
    have havg0 : 0 ≤ (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, D.mean x a + n * D.nearFrac * D.rowCap :=
      add_nonneg (mul_nonneg (inv_nonneg.mpr hUpos.le)
        (Finset.sum_nonneg fun a _ => D.mean_nonneg x a))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hfrac) D.rowCap_nonneg)
    calc ∑ o ∈ good, law.w o * (∑ a, D.row o.1.1 o.2 a x) ^ n
        = ((Fintype.card (EvenRole n) : ℝ) / N) ^ n *
            ∑ o ∈ good, law.w o * ((Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, Z a o) ^ n := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro o _
          rw [hrow o]; ring
      _ ≤ ((Fintype.card (EvenRole n) : ℝ) / N) ^ n * ((2 * D.jointConst) ^ n *
            ((Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, D.mean x a + n * D.nearFrac * D.rowCap) ^ n) :=
          mul_le_mul_of_nonneg_left hsc (pow_nonneg (div_nonneg hUpos.le hNpos.le) n)
      _ ≤ ((Fintype.card (EvenRole n) : ℝ) / N) ^ n * ((2 * D.jointConst) ^ n *
            (D.meanAvg + n * D.nearFrac * D.rowCap) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (div_nonneg hUpos.le hNpos.le) n)
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith [D.jointConst_ge]) n)
          apply pow_le_pow_left₀ havg0
          linarith [D.mean_avg x]
      _ = moment := by simp only [moment]; rw [mul_pow, mul_pow]; ring
  -- assemble
  refine ⟨{
    Outcome := (D.H × D.C) × (OddRole n → Fin N)
    law := law
    good := good
    predictive := fun a o => D.predictive a o.1.1 o.2
    odd := fun o => o.2
    row := fun o => D.row o.1.1 o.2
    odd_injective := ?_
    row_nonnegative := fun o a x => D.row_nonneg _ _ _ _
    row_sum := fun o a ho hp => D.row_sum _ _ _ (Finset.mem_filter.mp ho).2.1 hp
    common_neighbor := fun o a ho hp =>
      D.common_neighbor _ _ _ (Finset.mem_filter.mp ho).2.1 hp
    ε_enter := D.ε_pre + D.ε_cluster
    ε_predictive := 2 * D.ε_ref
    moment := moment
    entering_failure := henter
    predictive_failure := hpred
    column_moment := hcolumn
    failure_budget := by
      have hb := D.budget
      simp only [moment]
      linarith }⟩
  intro o hw hg
  have hg' := (Finset.mem_filter.mp hg).2
  have hJw : (Jc o.1.1 o.1.2).w o.2 ≠ 0 := by
    intro h0
    apply hw
    simp only [law, FinProb.bind, h0, mul_zero]
  exact (hJ o.1.1 o.1.2 hg'.1 hg'.2).1 o.2 hJw

/-! ## Stage 3: the experiment at fixed typical tags (TeX 10:271–281) -/

/-- The pre-cluster experiment at one tag assignment. Groups `Grp` draw
independent clusters `Kg h g` (common finite index type `Cl`); the odd role
`b` then has reference label law `lab h b c` for the cluster `c` of its group.
`oddRow h b` is the cluster-averaged row `p_b^W` (zero off the group's validity
event), and `oddMean y b` the normalized fixed-tag comparison mean
`N p̂_b(y)` (10:156, 10:275). `mean x a` is the normalized even comparison mean
`N p̂_v^X(x)` (10:253, 10:292). All rows are extended locally, so the stated
joint bounds over separated roles hold under the unconditioned law. -/
structure TypicalCore (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (A : ℝ) where
  H : Type
  [fH : Fintype H]
  PH : FinProb H
  valid : H → Prop
  ε_valid : ℝ
  valid_failure : PH.pr (fun h => ¬ valid h) ≤ ε_valid
  Grp : Type
  [fGrp : Fintype Grp]
  [dGrp : DecidableEq Grp]
  grp : OddRole n → Grp
  Cl : Type
  [fCl : Fintype Cl]
  Kg : H → Grp → FinProb Cl
  lab : H → OddRole n → Cl → FinProb (Fin N)
  oddRow : H → OddRole n → Fin N → ℝ
  oddRow_nonneg : ∀ h b y, 0 ≤ oddRow h b y
  cluster_mean : ∀ h, valid h → ∀ b y,
    (Kg h (grp b)).expect (fun c => (lab h b c).w y) ≤ oddRow h b y
  groupCap : ℝ
  groupCap_pos : 0 < groupCap
  group_cap : ∀ h, valid h → ∀ g (c : Cl) y,
    ∑ b ∈ Finset.univ.filter (fun b => grp b = g), (lab h b c).w y ≤ groupCap
  atom_small : ∀ h, valid h → ∀ b c y, (lab h b c).w y ≤ (n : ℝ) ^ (-A)
  oddCap : ℝ
  oddCap_nonneg : 0 ≤ oddCap
  odd_cap : ∀ h, valid h → ∀ b y, (N : ℝ) * oddRow h b y ≤ oddCap
  oddNear : OddRole n → Finset (OddRole n)
  oddNear_self : ∀ b, b ∈ oddNear b
  oddFrac : ℝ
  oddNear_card : ∀ b, ((oddNear b).card : ℝ) ≤ oddFrac * Fintype.card (OddRole n)
  oddMean : Fin N → OddRole n → ℝ
  oddMean_nonneg : ∀ y b, 0 ≤ oddMean y b
  odd_joint : ∀ y (m : ℕ), m ≤ n → ∀ s : Fin m → OddRole n,
    (∀ i j : Fin m, j < i → s i ∉ oddNear (s j)) →
      ∑ h, PH.w h * (if valid h then ∏ i, (N : ℝ) * oddRow h (s i) y else 0) ≤
        ∏ i, oddMean y (s i)
  predictive : EvenRole n → H → (OddRole n → Fin N) → Prop
  row : H → (OddRole n → Fin N) → EvenRole n → Fin N → ℝ
  row_nonneg : ∀ h ω a x, 0 ≤ row h ω a x
  row_sum : ∀ h ω a, valid h → predictive a h ω → ∑ x, row h ω a x = 1
  common_neighbor : ∀ h ω a, valid h → predictive a h ω → ∀ x, row h ω a x ≠ 0 →
    ∀ b : OddRole n, (cube n).Adj a.1 b.1 → Hits E G x (ω b)
  predictive_local : ∀ a h, FinProb.DependsOn (fun ω => predictive a h ω) (star a)
  row_local : ∀ a h x, FinProb.DependsOn (fun ω => row h ω a x) (star a)
  rowCap : ℝ
  rowCap_nonneg : 0 ≤ rowCap
  row_cap : ∀ h ω a x, valid h → (N : ℝ) * row h ω a x ≤ rowCap
  near : EvenRole n → Finset (EvenRole n)
  near_self : ∀ a, a ∈ near a
  nearFrac : ℝ
  near_card : ∀ a, ((near a).card : ℝ) ≤ nearFrac * Fintype.card (EvenRole n)
  jointConst : ℝ
  jointConst_ge : 1 ≤ jointConst
  mean : Fin N → EvenRole n → ℝ
  mean_nonneg : ∀ x a, 0 ≤ mean x a
  ref_joint : ∀ x (m : ℕ), m ≤ n → ∀ s : Fin m → EvenRole n,
    (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
      ∑ h, PH.w h * (if valid h then ∑ c : Grp → Cl, (FinProb.pi (Kg h)).w c *
        (FinProb.pi (fun b => lab h b (c (grp b)))).expect
          (fun ω => ∏ i, (N : ℝ) * row h ω (s i) x) else 0)
        ≤ jointConst ^ m * ∏ i, mean x (s i)
  ε_ref : ℝ
  ref_predictive : ∀ a, ∑ h, PH.w h * (if valid h then ∑ c : Grp → Cl,
      (FinProb.pi (Kg h)).w c *
        (FinProb.pi (fun b => lab h b (c (grp b)))).pr (fun ω => ¬ predictive a h ω)
      else 0) ≤ ε_ref
  n_pos : 0 < n
  N_pos : 0 < N

attribute [instance] TypicalCore.fH TypicalCore.fGrp TypicalCore.dGrp TypicalCore.fCl

/-- The failure budget at fixed tags, with odd-column threshold `oddThr`
and average comparison-mean bounds `oddAvg`, `meanAvg`. The five terms are
validity (10:117), odd columns (10:275), cluster columns at the clock
threshold `1e-8` (10:277–281), predictive tests with the clock factor 2
(10:286), and even columns (10:288–292). -/
def TypicalCore.Budget {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {A : ℝ}
    (D : TypicalCore n N E G A) (oddThr oddAvg meanAvg : ℝ) : Prop :=
  0 < oddThr ∧
  D.ε_valid
    + N * ((Fintype.card (OddRole n) : ℝ) * (oddAvg + n * D.oddFrac * D.oddCap) /
        (N * oddThr)) ^ n
    + N * Real.exp (((Real.exp 1 - 1) * oddThr - 1e-8) / D.groupCap)
    + Fintype.card (EvenRole n) * (2 * D.ε_ref)
    + N * (((Fintype.card (EvenRole n) : ℝ) / N) * (2 * D.jointConst) *
        (meanAvg + n * D.nearFrac * D.rowCap)) ^ n < 1

/-- The experiment at fixed typical tags (10:269): the averaged normalized
comparison means are bounded for every label. -/
structure TypicalSystem (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (A : ℝ) where
  core : TypicalCore n N E G A
  oddThr : ℝ
  oddAvg : ℝ
  meanAvg : ℝ
  odd_avg : ∀ y, (Fintype.card (OddRole n) : ℝ)⁻¹ * ∑ b, core.oddMean y b ≤ oddAvg
  mean_avg : ∀ x, (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, core.mean x a ≤ meanAvg
  budget : core.Budget oddThr oddAvg meanAvg

/-- **Sub-lemma (b)**, TeX 10:271–281. `goodH` = validity and all odd column
sums of `oddRow` at most `oddThr` (scattered moments with `K = 1`,
`Lane_sol_s10_1k.scattered_retained_tail`); `clusterGood` = all cluster
column sums at most `1e-8` (`Lane_sol_s10_1k.independent_group_column_tail`
over the groups, mean at most `oddThr` by `cluster_mean`); the cluster law is
`FinProb.pi (Kg h)` and `lab h c b = lab h b (c (grp b))`. -/
theorem transferData_of_typical {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {A : ℝ}
    (S : TypicalSystem n N E G A) : Nonempty (TransferData n N E G A) := by
  sorry

/-! ## Stage 2: all tag assignments (TeX 10:263–269) -/

/-- The experiment for every tag assignment `t : Slice → Tag`, with the
tag-locality of the comparison means (10:263), their caps `e^{.1m}`
(10:157, 10:253), the near fraction `n^{O(1)} 2^{-m}` of the tag-dependence
domains (10:267), the one-slice balanced response (10:265; availability and
price separation), and the budgets. The slice term is the slice sum of
normalized means scaled so that its average over slices is the global
average over roles. -/
structure TaggedSystem (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (A : ℝ) where
  Slice : Type
  [fSlice : Fintype Slice]
  [dSlice : DecidableEq Slice]
  [neSlice : Nonempty Slice]
  Tag : Type
  [fTag : Fintype Tag]
  [dTag : DecidableEq Tag]
  [neTag : Nonempty Tag]
  core : (Slice → Tag) → TypicalCore n N E G A
  oddSlice : OddRole n → Slice
  evenSlice : EvenRole n → Slice
  tagNbhd : Slice → Finset Slice
  tagNbhd_self : ∀ j, j ∈ tagNbhd j
  odd_local : ∀ y b, FinProb.DependsOn
    (fun t : Slice → Tag => (core t).oddMean y b) (tagNbhd (oddSlice b))
  even_local : ∀ x a, FinProb.DependsOn
    (fun t : Slice → Tag => (core t).mean x a) (tagNbhd (evenSlice a))
  meanCap : ℝ
  meanCap_nonneg : 0 ≤ meanCap
  odd_mean_cap : ∀ t y b, (core t).oddMean y b ≤ meanCap
  even_mean_cap : ∀ t x a, (core t).mean x a ≤ meanCap
  tagFrac : ℝ
  odd_tag_near : ∀ b, ((Finset.univ.filter (fun b' : OddRole n =>
      ¬ Disjoint (tagNbhd (oddSlice b)) (tagNbhd (oddSlice b')))).card : ℝ) ≤
    tagFrac * Fintype.card (OddRole n)
  even_tag_near : ∀ a, ((Finset.univ.filter (fun a' : EvenRole n =>
      ¬ Disjoint (tagNbhd (evenSlice a)) (tagNbhd (evenSlice a')))).card : ℝ) ≤
    tagFrac * Fintype.card (EvenRole n)
  balConst : ℝ
  response : ∀ j (q : Slice → Tag → ℝ), (∀ i a, 0 ≤ q i a) → (∀ i, ∑ a, q i a = 1) →
    ∃ qj : Tag → ℝ, (∀ a, 0 ≤ qj a) ∧ ∑ a, qj a = 1 ∧
      (∀ y, ∑ σ : Slice → Tag, (∏ i, Function.update q j qj i (σ i)) *
          ((Fintype.card Slice : ℝ) / Fintype.card (OddRole n) *
            ∑ b ∈ Finset.univ.filter (fun b => oddSlice b = j), (core σ).oddMean y b)
        ≤ balConst) ∧
      (∀ x, ∑ σ : Slice → Tag, (∏ i, Function.update q j qj i (σ i)) *
          ((Fintype.card Slice : ℝ) / Fintype.card (EvenRole n) *
            ∑ a ∈ Finset.univ.filter (fun a => evenSlice a = j), (core σ).mean x a)
        ≤ balConst)
  typThr : ℝ
  typThr_pos : 0 < typThr
  tag_budget : 2 * N * ((balConst + n * tagFrac * meanCap) / typThr) ^ n < 1
  oddThr : ℝ
  core_budget : ∀ t, (core t).Budget oddThr typThr typThr

attribute [instance] TaggedSystem.fSlice TaggedSystem.dSlice TaggedSystem.neSlice
  TaggedSystem.fTag TaggedSystem.dTag TaggedSystem.neTag

/-- **Sub-lemma (c)**, TeX 10:263–269. `simultaneous_profiles` (Lemma 3.3)
on the responses gives product profiles whose expected slice terms are at
most `balConst`; scattered moments over the product tag law (independence at
disjoint tag domains, `FinProb.pi_expect_mul_of_disjoint`) and a union over
the `2N` labels give a tag assignment with both averages at most `typThr`. -/
theorem typical_of_tagged {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {A : ℝ}
    (S : TaggedSystem n N E G A) : Nonempty (TypicalSystem n N E G A) := by
  sorry

/-! ## Stage 1: the finite patch menu and the construction (TeX 10:23–262) -/

/-- A finite menu of cluster patches of colour `G` (10:23–24): every allowed
discard pair is avoided by some patch. -/
structure PatchMenu (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (G : Colour) (ζ δ κ : ℝ) where
  I : Type
  [fI : Fintype I]
  [dI : DecidableEq I]
  [neI : Nonempty I]
  μ : I → Law N
  K : I → ℕ
  lam : (i : I) → Fin (K i) → ℝ
  D : (i : I) → Fin (K i) → Law N
  μ_support : ∀ i, (μ i).SupportedIn X
  D_support : ∀ i j, (D i j).SupportedIn Y
  lam_nonneg : ∀ i j, 0 ≤ lam i j
  lam_sum : ∀ i, ∑ j, lam i j = 1
  μ_width : ∀ i, (μ i).WidthLE ((n : ℝ) ^ δ)
  ν_width : ∀ i y, ∑ j, lam i j * (D i j).w y ≤ Real.exp ((n : ℝ) ^ δ) / N
  D_atom : ∀ i j y, (D i j).w y ≤ Real.exp (-(n : ℝ) ^ ζ)
  codegree : ∀ i j, 0 < lam i j → ∀ y y', 0 < (D i j).w y → 0 < (D i j).w y' →
    1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G (μ i) y y'
  avoid : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
    ∃ i, (∀ x ∈ RX, (μ i).w x = 0) ∧ ∀ y ∈ RY, ∑ j, lam i j * (D i j).w y = 0

attribute [instance] PatchMenu.fI PatchMenu.dI PatchMenu.neI

/-- **Sub-lemma (e)**, TeX 10:23–24: index the menu by the allowed discard
pairs and choose a witness off each. -/
theorem patchMenu_of_available {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {G : Colour} {ζ δ κ : ℝ} (hκ : 0 ≤ κ)
    (havail : AvailableAt κ (PCluster G ζ δ) n N E X Y) :
    Nonempty (PatchMenu n N E X Y G ζ δ κ) := by
  classical
  let I := {p : Finset (Fin N) × Finset (Fin N) //
    (p.1.card : ℝ) ≤ κ * N ∧ (p.2.card : ℝ) ≤ κ * N}
  have hw : ∀ i : I, ∃ AB : Finset (Fin N) × Finset (Fin N),
      AB ∈ PCluster G ζ δ n N E ∧ AB.1 ⊆ X \ i.1.1 ∧ AB.2 ⊆ Y \ i.1.2 := by
    intro i
    obtain ⟨A, B, hAB, hA, hB⟩ := havail i.1.1 i.1.2 i.2.1 i.2.2
    exact ⟨(A, B), hAB, hA, hB⟩
  choose AB hAB hA hB using hw
  have hP : ∀ i : I, ∃ (μ : Law N) (K : ℕ) (lam : Fin K → ℝ) (D : Fin K → Law N),
      μ.SupportedIn (AB i).1 ∧ (∀ j, (D j).SupportedIn (AB i).2) ∧
      (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧
      μ.WidthLE ((n : ℝ) ^ δ) ∧
      (∀ y, ∑ j, lam j * (D j).w y ≤ Real.exp ((n : ℝ) ^ δ) / N) ∧
      (∀ j y, (D j).w y ≤ Real.exp (-(n : ℝ) ^ ζ)) ∧
      (∀ j, 0 < lam j → ∀ y y', 0 < (D j).w y → 0 < (D j).w y' →
        1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ y y') := fun i => hAB i
  choose μ K lam D hμ hD hlam hsum hμw hνw hDa hcod using hP
  have hne : Nonempty I := ⟨⟨(∅, ∅), by simpa using mul_nonneg hκ (Nat.cast_nonneg N),
    by simpa using mul_nonneg hκ (Nat.cast_nonneg N)⟩⟩
  exact ⟨{
    I := I
    μ := μ
    K := K
    lam := lam
    D := D
    μ_support := fun i x hx => hμ i x (fun hxA => hx (Finset.mem_sdiff.mp (hA i hxA)).1)
    D_support := fun i j y hy => hD i j y (fun hyB => hy (Finset.mem_sdiff.mp (hB i hyB)).1)
    lam_nonneg := hlam
    lam_sum := hsum
    μ_width := hμw
    ν_width := hνw
    D_atom := hDa
    codegree := hcod
    avoid := by
      intro RX RY hRX hRY
      let i : I := ⟨(RX, RY), hRX, hRY⟩
      refine ⟨i, ?_, ?_⟩
      · intro x hx
        exact hμ i x (fun hxA => (Finset.mem_sdiff.mp (hA i hxA)).2 hx)
      · intro y hy
        apply Finset.sum_eq_zero
        intro j _
        rw [hD i j y (fun hyB => (Finset.mem_sdiff.mp (hB i hyB)).2 hy), mul_zero] }⟩

/-- **Sub-lemma (d)**, TeX 10:23–262: the construction. For every clock
exponent `A`, in the large regime, the menu and the initial discrepancy give a
`TaggedSystem`. This carries P10.1b (definitions and randomization order),
P10.1c (fixed-list test, available as `S10.p10_1c_fixed_list_squared_mass_test`),
P10.1d (eligibility and validity), P10.1e (squared tilt), P10.1f (masks),
P10.1g (odd comparison mean cap), P10.1h (likelihood comparison), P10.1i
(predictive test, light part, even comparison mean cap), the locality and
independence of separated local experiments, and the budget arithmetic.
It needs a further split once the global experiment is defined. -/
theorem tagged_of_menu (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) (A : ℝ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour),
      LargeAt n₀ C₀ n N →
      DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
      PatchMenu n N E X Y G ζ δ κ →
      Nonempty (TaggedSystem n N E G A) := by
  sorry

/-! ## Assembly -/

/-- `LargeAt` is antitone in its thresholds. -/
theorem largeAt_mono {n₀ n₁ n N : ℕ} {C₀ C₁ : ℝ}
    (hn : n₀ ≤ n₁) (hC : C₀ ≤ C₁) (h : LargeAt n₁ C₁ n N) : LargeAt n₀ C₀ n N :=
  ⟨le_trans hn h.1,
    le_trans (mul_le_mul_of_nonneg_right hC (pow_nonneg (by norm_num) n)) h.2.1, h.2.2⟩

/-- In the large regime `log N ≤ 2 n`. -/
theorem log_le_of_largeAt {n₀ n N : ℕ} {C₀ : ℝ} (h : LargeAt n₀ C₀ n N) :
    Real.log N ≤ 2 * n := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, Real.log_zero]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (N : ℝ) ≤ (4 : ℝ) ^ n := by
    have h1 : (N : ℝ) ≤ n * 2 ^ n := by exact_mod_cast h.2.2
    have h2 : (n : ℝ) ≤ 2 ^ n := by
      exact_mod_cast (Nat.lt_two_pow_self).le
    calc (N : ℝ) ≤ n * 2 ^ n := h1
      _ ≤ 2 ^ n * 2 ^ n := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (4 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_one_gt_d9,
        show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h4
      _ = 2 := Real.log_exp 2
  calc Real.log N ≤ Real.log ((4 : ℝ) ^ n) := Real.log_le_log hNpos hle
    _ = n * Real.log 4 := by rw [Real.log_pow]
    _ ≤ n * 2 := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg n)
    _ = 2 * n := by ring

/-- The construction hole of `S10.p10_1k_transfer_to_even_rows`, assembled from
sub-lemmas (a)–(e) and the clock lemma. -/
theorem rowExperiment_eventually (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ)
    (hδ : 0 < δ) (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ C₀, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour),
      LargeAt n₀ C₀ n N →
      DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
      AvailableAt κ (PCluster G ζ δ) n N E X Y →
      Nonempty (Lane_sol_s10_1k.RowExperiment n N E G) := by
  obtain ⟨A, nc, ε, hε, hclock⟩ := Lane_sol_s10_1k.clock_injective_labels 2
  obtain ⟨n₁, C₁, htag⟩ := tagged_of_menu η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ A
  have hεsmall : ∀ᶠ k : ℕ in atTop, ε k ∈ Set.Icc (-1 : ℝ) 1 :=
    hε.eventually (Icc_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp hεsmall
  refine ⟨max n₁ (max nc n₂), max C₁ 1, ?_⟩
  intro n N E X Y G hlarge hdisc havail
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hlarge.1
  have hnc : nc ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlarge.1
  have hn₂' : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlarge.1
  obtain ⟨menu⟩ := patchMenu_of_available hκ.le havail
  obtain ⟨sys⟩ := htag n N E X Y G
    (largeAt_mono (le_max_left _ _) (le_max_left _ _) hlarge) hdisc menu
  obtain ⟨typ⟩ := typical_of_tagged sys
  obtain ⟨td⟩ := transferData_of_typical typ
  have hlog : Real.log N ≤ 2 * n := log_le_of_largeAt hlarge
  have hclockAt : ClockAt n N A (ε n) := by
    intro R _ _ p hcol hatom
    exact hclock n hnc N hlog p hcol hatom
  exact rowExperiment_of_transferData td hclockAt (hn₂ n hn₂').1 (hn₂ n hn₂').2

end HypercubeRamsey.Lane_opus_s10_row
