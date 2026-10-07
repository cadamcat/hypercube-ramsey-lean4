import HypercubeRamsey.S10.Transfer_sol_s10_1k
import HypercubeRamsey.S10.Split_opus_s10_row_q_s10_b
import HypercubeRamsey.S10.LocalNodes
import HypercubeRamsey.Framework.Props
import HypercubeRamsey.S10.Split_opus_s10_tagged
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
  classical
  let D := S.core
  letI : Fintype D.H := D.fH
  letI : Fintype D.Grp := D.fGrp
  letI : DecidableEq D.Grp := D.dGrp
  letI : Fintype D.Cl := D.fCl
  have hOdd : Nonempty (OddRole n) := by
    let v : CubeVertex n := fun _ => false
    have hv : IsEvenRole v := by simp [IsEvenRole, v]
    let i : Fin n := ⟨0, D.n_pos⟩
    refine ⟨⟨cubeFlip v i, ?_⟩⟩
    intro hflip
    exact (cubeFlip_parity v i).mp hflip hv
  letI : Nonempty (OddRole n) := hOdd
  let validRows : Finset D.H := Finset.univ.filter D.valid
  let goodH : D.H → Prop := fun h => D.valid h ∧
    ∀ y, ∑ b, D.oddRow h b y ≤ S.oddThr
  letI : DecidablePred goodH := fun h => Classical.propDecidable (goodH h)
  let clusterGood : D.H → (D.Grp → D.Cl) → Prop := fun h c =>
    ∀ y, ∑ b, (D.lab h b (c (D.grp b))).w y ≤ (1e-8 : ℝ)
  let oddOne : ℝ := ((Fintype.card (OddRole n) : ℝ) *
    (S.oddAvg + n * D.oddFrac * D.oddCap) / ((N : ℝ) * S.oddThr)) ^ n
  let errOdd : ℝ := (N : ℝ) * oddOne
  let epsCluster : ℝ := (N : ℝ) *
    Real.exp (((Real.exp 1 - 1) * S.oddThr - 1e-8) / D.groupCap)
  have hepsCluster_nonneg : 0 ≤ epsCluster := by positivity
  have hodd_est := Lane_q_s10_b.scattered_scaled_column_tail
      D.PH validRows (fun b y h => D.oddRow h b y)
      (by intro b y h; exact D.oddRow_nonneg h b y)
      N D.N_pos D.oddCap D.oddCap_nonneg
      (by
        intro b y h hh
        exact D.odd_cap h (Finset.mem_filter.mp hh).2 b y)
      D.oddNear D.oddNear_self D.oddFrac D.oddNear_card n
      (fun y b => D.oddMean y b)
      (by intro y b; exact D.oddMean_nonneg y b)
      (by
        intro y m hm s hs
        have hj := D.odd_joint y m hm s hs
        calc
          ∑ h ∈ validRows, D.PH.w h *
              ∏ i, (N : ℝ) * D.oddRow h (s i) y =
              ∑ h, D.PH.w h *
                (if D.valid h then ∏ i, (N : ℝ) * D.oddRow h (s i) y else 0) := by
            simp [validRows, Finset.sum_filter]
          _ ≤ ∏ i, D.oddMean y (s i) := hj)
      S.oddAvg S.odd_avg S.oddThr S.budget.1
  have hodd_each : ∀ y,
      D.PH.pr (fun h => D.valid h ∧ S.oddThr < ∑ b, D.oddRow h b y) ≤ oddOne := by
    intro y
    simpa [validRows, oddOne] using hodd_est y
  have hodd_failure :
      D.PH.pr (fun h => D.valid h ∧ ∃ y : Fin N,
        S.oddThr < ∑ b, D.oddRow h b y) ≤ errOdd := by
    calc
      D.PH.pr (fun h => D.valid h ∧ ∃ y : Fin N,
          S.oddThr < ∑ b, D.oddRow h b y) ≤
          ∑ y : Fin N, D.PH.pr (fun h => D.valid h ∧
            S.oddThr < ∑ b, D.oddRow h b y) :=
        (by
          simpa only [exists_and_left] using
            (Lane_q_s10_b.pr_exists_le_sum D.PH
              (fun y h => D.valid h ∧ S.oddThr < ∑ b, D.oddRow h b y)))
      _ ≤ ∑ _y : Fin N, oddOne :=
        Finset.sum_le_sum fun y _ => hodd_each y
      _ = errOdd := by simp [errOdd, oddOne]
  have hpre_failure : D.PH.pr (fun h => ¬ goodH h) ≤ D.ε_valid + errOdd := by
    have hevent : (fun h => ¬ goodH h) =
        (fun h => ¬ D.valid h ∨ (D.valid h ∧ ∃ y : Fin N,
          S.oddThr < ∑ b, D.oddRow h b y)) := by
      funext h
      by_cases hv : D.valid h <;> simp [goodH, hv, not_le]
    rw [hevent]
    calc
      D.PH.pr (fun h => ¬ D.valid h ∨
          (D.valid h ∧ ∃ y : Fin N, S.oddThr < ∑ b, D.oddRow h b y)) ≤
          D.PH.pr (fun h => ¬ D.valid h) +
            D.PH.pr (fun h => D.valid h ∧ ∃ y : Fin N,
              S.oddThr < ∑ b, D.oddRow h b y) := FinProb.pr_union D.PH _ _
      _ ≤ D.ε_valid + errOdd := add_le_add D.valid_failure hodd_failure
  have hgate_sum_le (q : D.H → ℝ) (hq : ∀ h, 0 ≤ q h) :
      ∑ h, D.PH.w h * (if goodH h then q h else 0) ≤
        ∑ h, D.PH.w h * (if D.valid h then q h else 0) := by
    apply Finset.sum_le_sum
    intro h hh
    by_cases hg : goodH h
    · simp [hg, hg.1]
    · by_cases hv : D.valid h
      · have hn := mul_nonneg (D.PH.nonneg h) (hq h)
        simpa [hg, hv] using hn
      · simp [hg, hv]
  let groupX : D.H → D.Grp → Fin N → D.Cl → ℝ := fun h g y c =>
    ∑ b, if D.grp b = g then (D.lab h b c).w y else 0
  have hcluster_tail (h : D.H) (hh : goodH h) :
      (FinProb.pi (D.Kg h)).pr (fun c => ¬ clusterGood h c) ≤ epsCluster := by
    have hgroup_total (c : D.Grp → D.Cl) (y : Fin N) :
        ∑ g, groupX h g y (c g) = ∑ b, (D.lab h b (c (D.grp b))).w y := by
      calc
        ∑ g, groupX h g y (c g) =
            ∑ g, ∑ b, if D.grp b = g then (D.lab h b (c g)).w y else 0 := rfl
        _ = ∑ g, ∑ b,
              if D.grp b = g then (D.lab h b (c (D.grp b))).w y else 0 := by
          apply Finset.sum_congr rfl
          intro g hg
          apply Finset.sum_congr rfl
          intro b hb
          split_ifs with hbg
          · rw [hbg]
          · rfl
        _ = ∑ b, (D.lab h b (c (D.grp b))).w y :=
          Lane_q_s10_b.grouped_sum_eq D.grp
            (fun b => (D.lab h b (c (D.grp b))).w y)
    have hX : ∀ g y c, 0 ≤ groupX h g y c ∧ groupX h g y c ≤ D.groupCap := by
      intro g y c
      constructor
      · unfold groupX
        apply Finset.sum_nonneg
        intro b hb
        by_cases hbg : D.grp b = g
        · simp [hbg, (D.lab h b c).nonneg y]
        · simp [hbg]
      · simpa [groupX, Finset.sum_filter] using D.group_cap h hh.1 g c y
    have hmean : ∀ y, ∑ g, (D.Kg h g).expect (fun c => groupX h g y c) ≤ S.oddThr := by
      intro y
      calc
        ∑ g, (D.Kg h g).expect (fun c => groupX h g y c) =
            ∑ b, (D.Kg h (D.grp b)).expect (fun c => (D.lab h b c).w y) := by
          simpa [groupX] using
            (Lane_q_s10_b.grouped_expect_sum_eq D.grp (D.Kg h) (D.lab h) y)
        _ ≤ ∑ b, D.oddRow h b y := by
          apply Finset.sum_le_sum
          intro b hb
          exact D.cluster_mean h hh.1 b y
        _ ≤ S.oddThr := hh.2 y
    have htail := Lane_q_s10_b.independent_group_tail (D.Kg h)
      (fun g y c => groupX h g y c) D.groupCap S.oddThr (1e-8 : ℝ)
      D.groupCap_pos hX hmean
    have hinc : ∀ c, ¬ clusterGood h c →
        ∃ y : Fin N, (1e-8 : ℝ) ≤ ∑ g, groupX h g y (c g) := by
      intro c hc
      have hex : ∃ y : Fin N,
          (1e-8 : ℝ) < ∑ b, (D.lab h b (c (D.grp b))).w y := by
        by_contra hno
        apply hc
        intro y
        by_contra hle
        exact hno ⟨y, lt_of_not_ge hle⟩
      obtain ⟨y, hy⟩ := hex
      exact ⟨y, by rw [hgroup_total]; exact le_of_lt hy⟩
    have hunion := Lane_q_s10_b.pr_exists_le_sum (FinProb.pi (D.Kg h))
      (fun y c => (1e-8 : ℝ) ≤ ∑ g, groupX h g y (c g))
    calc
      (FinProb.pi (D.Kg h)).pr (fun c => ¬ clusterGood h c) ≤
          (FinProb.pi (D.Kg h)).pr
            (fun c => ∃ y : Fin N, (1e-8 : ℝ) ≤ ∑ g, groupX h g y (c g)) :=
        Lane_q_s10_b.pr_mono _ hinc
      _ ≤ ∑ y : Fin N, (FinProb.pi (D.Kg h)).pr
            (fun c => (1e-8 : ℝ) ≤ ∑ g, groupX h g y (c g)) := hunion
      _ ≤ ∑ _y : Fin N,
            Real.exp (((Real.exp 1 - 1) * S.oddThr - 1e-8) / D.groupCap) :=
        Finset.sum_le_sum fun y hy => htail y
      _ = epsCluster := by simp [epsCluster]
  have hcluster_failure :
      ∑ h, D.PH.w h *
        (if goodH h then (FinProb.pi (D.Kg h)).pr (fun c => ¬ clusterGood h c) else 0)
        ≤ epsCluster := by
    calc
      _ ≤ ∑ h, D.PH.w h * (if goodH h then epsCluster else 0) := by
        apply Finset.sum_le_sum
        intro h hh
        by_cases hg : goodH h
        · simp [hg]
          exact mul_le_mul_of_nonneg_left (hcluster_tail h hg) (D.PH.nonneg h)
        · simp [hg]
      _ ≤ ∑ h, D.PH.w h * epsCluster := by
        apply Finset.sum_le_sum
        intro h hh
        by_cases hg : goodH h
        · simp [hg]
        · simp [hg]
          exact mul_nonneg (D.PH.nonneg h) hepsCluster_nonneg
      _ = epsCluster := by
        rw [← Finset.sum_mul, D.PH.sum_eq_one]
        ring
  refine ⟨{
    H := D.H
    PH := D.PH
    goodH := goodH
    C := D.Grp → D.Cl
    K := fun h => FinProb.pi (D.Kg h)
    lab := fun h c b => D.lab h b (c (D.grp b))
    clusterGood := clusterGood
    column_small := by
      intro h c hh hc y
      exact hc y
    atom_small := by
      intro h c hh hc b y
      exact D.atom_small h hh.1 b (c (D.grp b)) y
    predictive := D.predictive
    row := D.row
    row_nonneg := D.row_nonneg
    row_sum := by
      intro h ω a hh hp
      exact D.row_sum h ω a hh.1 hp
    common_neighbor := by
      intro h ω a hh hp x hx b hb
      exact D.common_neighbor h ω a hh.1 hp x hx b hb
    predictive_local := D.predictive_local
    row_local := D.row_local
    rowCap := D.rowCap
    rowCap_nonneg := D.rowCap_nonneg
    row_cap := by
      intro h ω a x hh
      exact D.row_cap h ω a x hh.1
    near := D.near
    near_self := D.near_self
    nearFrac := D.nearFrac
    near_card := D.near_card
    jointConst := D.jointConst
    jointConst_ge := D.jointConst_ge
    mean := D.mean
    mean_nonneg := D.mean_nonneg
    meanAvg := S.meanAvg
    mean_avg := S.mean_avg
    ref_joint := by
      intro x m hm s hs
      have hq (h : D.H) : 0 ≤
          ∑ c : D.Grp → D.Cl, (FinProb.pi (D.Kg h)).w c *
          (FinProb.pi (fun b => D.lab h b (c (D.grp b)))).expect
            (fun ω => ∏ i, (N : ℝ) * D.row h ω (s i) x) := by
        apply Finset.sum_nonneg
        intro c hc
        have hprod (ω : OddRole n → Fin N) :
            0 ≤ ∏ i : Fin m, (N : ℝ) * D.row h ω (s i) x := by
          apply Finset.prod_nonneg
          intro i hi
          exact mul_nonneg (by positivity) (D.row_nonneg h ω (s i) x)
        have hexpect : 0 ≤
            (FinProb.pi (fun b => D.lab h b (c (D.grp b)))).expect
              (fun ω => ∏ i : Fin m, (N : ℝ) * D.row h ω (s i) x) := by
          unfold FinProb.expect
          apply Finset.sum_nonneg
          intro ω hw
          exact mul_nonneg
            ((FinProb.pi (fun b => D.lab h b (c (D.grp b)))).nonneg ω) (hprod ω)
        exact mul_nonneg ((FinProb.pi (D.Kg h)).nonneg c) hexpect
      exact (hgate_sum_le
        (fun h => ∑ c : D.Grp → D.Cl, (FinProb.pi (D.Kg h)).w c *
          (FinProb.pi (fun b => D.lab h b (c (D.grp b)))).expect
            (fun ω => ∏ i, (N : ℝ) * D.row h ω (s i) x)) hq).trans
        (D.ref_joint x m hm s hs)
    ε_pre := D.ε_valid + errOdd
    ε_cluster := epsCluster
    ε_ref := D.ε_ref
    pre_failure := hpre_failure
    cluster_failure := hcluster_failure
    ref_predictive := by
      intro a
      exact (hgate_sum_le
        (fun h => ∑ c : D.Grp → D.Cl, (FinProb.pi (D.Kg h)).w c *
          (FinProb.pi (fun b => D.lab h b (c (D.grp b)))).pr
            (fun ω => ¬ D.predictive a h ω))
        (by
          intro h
          apply Finset.sum_nonneg
          intro c hc
          exact mul_nonneg ((FinProb.pi (D.Kg h)).nonneg c)
            (Lane_q_s10_b.pr_nonneg _ _))
      ).trans (D.ref_predictive a)
    N_pos := D.N_pos
    budget := by
      simpa [TypicalCore.Budget, errOdd, oddOne, epsCluster, D] using S.budget.2
  }⟩

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
  classical
  let t₀ : S.Slice → S.Tag := fun _ => Classical.choice S.neTag
  have hn : 0 < n := (S.core t₀).n_pos
  have hOddSetEq :
      (Finset.univ.filter fun v : CubeVertex n => ¬ IsEvenRole v) =
        (Finset.univ \ HypercubeRamsey.evenRoleSet n) := by
    ext v
    simp [HypercubeRamsey.evenRoleSet]
  have hOddCardEq : Fintype.card (OddRole n) =
      (Finset.univ \ HypercubeRamsey.evenRoleSet n).card := by
    rw [Fintype.card_subtype]
    exact congrArg Finset.card hOddSetEq
  have hOddCardPos : 0 < Fintype.card (OddRole n) := by
    rw [hOddCardEq, (HypercubeRamsey.parity_class_card hn).2]
    positivity
  letI : Nonempty (OddRole n) := Fintype.card_pos_iff.mp hOddCardPos
  let oddScale : ℝ := (Fintype.card S.Slice : ℝ) / Fintype.card (OddRole n)
  let evenScale : ℝ := (Fintype.card S.Slice : ℝ) / Fintype.card (EvenRole n)
  let Label := Sum (Fin N) (Fin N)
  let labelEquiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin Label
  let payoff : ∀ j : S.Slice, (S.Slice → S.Tag) →
      Fin (Fintype.card Label) → ℝ := fun j σ r =>
    match labelEquiv.symm r with
    | Sum.inl y => oddScale *
        ∑ b ∈ Finset.univ.filter (fun b : OddRole n => S.oddSlice b = j),
          (S.core σ).oddMean y b
    | Sum.inr x => evenScale *
        ∑ a ∈ Finset.univ.filter (fun a : EvenRole n => S.evenSlice a = j),
          (S.core σ).mean x a
  have hresponse : ∀ j (q : S.Slice → S.Tag → ℝ),
      (∀ i a, 0 ≤ q i a) → (∀ i, ∑ a, q i a = 1) →
      ∃ qj : S.Tag → ℝ, (∀ a, 0 ≤ qj a) ∧ ∑ a, qj a = 1 ∧
        ∀ r, ∑ σ : S.Slice → S.Tag, (∏ i, Function.update q j qj i (σ i)) *
          payoff j σ r ≤ S.balConst := by
    intro j q hq0 hq1
    obtain ⟨qj, hqj0, hqj1, hodd, heven⟩ := S.response j q hq0 hq1
    refine ⟨qj, hqj0, hqj1, ?_⟩
    intro r
    cases hlabel : labelEquiv.symm r with
    | inl y =>
        simpa [payoff, hlabel, oddScale] using hodd y
    | inr x =>
        simpa [payoff, hlabel, evenScale] using heven x
  obtain ⟨q, hq0, hq1, hprofile⟩ :=
    HypercubeRamsey.simultaneous_profiles payoff (fun _ _ => S.balConst) hresponse
  let P : S.Slice → FinProb S.Tag := fun j => ⟨q j, hq0 j, hq1 j⟩
  let Q : FinProb (S.Slice → S.Tag) := FinProb.pi P
  let Zodd : Fin N → OddRole n → (S.Slice → S.Tag) → ℝ :=
    fun y b σ => (S.core σ).oddMean y b
  let Zeven : Fin N → EvenRole n → (S.Slice → S.Tag) → ℝ :=
    fun x a σ => (S.core σ).mean x a
  have hprofileOdd (j : S.Slice) (y : Fin N) :
      Q.expect (fun σ => oddScale *
        ∑ b ∈ Finset.univ.filter (fun b : OddRole n => S.oddSlice b = j), Zodd y b σ)
          ≤ S.balConst := by
    have h := hprofile j (labelEquiv (Sum.inl y))
    simpa [Q, P, payoff, Zodd, FinProb.expect, FinProb.pi] using h
  have hprofileEven (j : S.Slice) (x : Fin N) :
      Q.expect (fun σ => evenScale *
        ∑ a ∈ Finset.univ.filter (fun a : EvenRole n => S.evenSlice a = j), Zeven x a σ)
          ≤ S.balConst := by
    have h := hprofile j (labelEquiv (Sum.inr x))
    simpa [Q, P, payoff, Zeven, FinProb.expect, FinProb.pi] using h
  have hoddAverage : ∀ y : Fin N, (Fintype.card (OddRole n) : ℝ)⁻¹ *
      ∑ b, Q.expect (Zodd y b) ≤ S.balConst := by
    intro y
    apply Lane_q_s10_c.role_average_of_profiles
      (roleSlice := S.oddSlice) (Z := Zodd) (scale := oddScale)
      (bound := S.balConst) (hscale := by rfl) (q := q) hq0 hq1
    exact hprofileOdd
  have hevenAverage : ∀ x : Fin N, (Fintype.card (EvenRole n) : ℝ)⁻¹ *
      ∑ a, Q.expect (Zeven x a) ≤ S.balConst := by
    intro x
    apply Lane_q_s10_c.role_average_of_profiles
      (roleSlice := S.evenSlice) (Z := Zeven) (scale := evenScale)
      (bound := S.balConst) (hscale := by rfl) (q := q) hq0 hq1
    exact hprofileEven
  have htagFrac0 : 0 ≤ S.tagFrac := by
    obtain ⟨a⟩ := (inferInstance : Nonempty (EvenRole n))
    have hcard : 0 < (Fintype.card (EvenRole n) : ℝ) :=
      Nat.cast_pos.mpr Fintype.card_pos
    have hnearPos : 0 < ((Finset.univ.filter (fun a' : EvenRole n =>
        ¬ Disjoint (S.tagNbhd (S.evenSlice a)) (S.tagNbhd (S.evenSlice a')))).card : ℝ) := by
      have hmem : a ∈ Finset.univ.filter (fun a' : EvenRole n =>
          ¬ Disjoint (S.tagNbhd (S.evenSlice a)) (S.tagNbhd (S.evenSlice a'))) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hdis
        have hself := S.tagNbhd_self (S.evenSlice a)
        exact (Finset.disjoint_left.mp hdis) hself hself
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨a, hmem⟩)
    by_contra h
    have hneg : S.tagFrac < 0 := lt_of_not_ge h
    have hprod : S.tagFrac * (Fintype.card (EvenRole n) : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hneg hcard
    have hbound := S.even_tag_near a
    linarith
  let oddScope : OddRole n → Finset S.Slice := fun b => S.tagNbhd (S.oddSlice b)
  let evenScope : EvenRole n → Finset S.Slice := fun a => S.tagNbhd (S.evenSlice a)
  let oddNear : OddRole n → Finset (OddRole n) := fun b =>
    Finset.univ.filter (fun b' => ¬ Disjoint (oddScope b) (oddScope b'))
  let evenNear : EvenRole n → Finset (EvenRole n) := fun a =>
    Finset.univ.filter (fun a' => ¬ Disjoint (evenScope a) (evenScope a'))
  have hoddScopeDisjoint : ∀ b b', b' ∉ oddNear b →
      Disjoint (oddScope b) (oddScope b') := by
    intro b b' hnot
    by_contra hdis
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdis⟩)
  have hevenScopeDisjoint : ∀ a a', a' ∉ evenNear a →
      Disjoint (evenScope a) (evenScope a') := by
    intro a a' hnot
    by_contra hdis
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdis⟩)
  have hoddSelf : ∀ b, b ∈ oddNear b := by
    intro b
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hdis
    have hself := S.tagNbhd_self (S.oddSlice b)
    exact (Finset.disjoint_left.mp hdis) hself hself
  have hevenSelf : ∀ a, a ∈ evenNear a := by
    intro a
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hdis
    have hself := S.tagNbhd_self (S.evenSlice a)
    exact (Finset.disjoint_left.mp hdis) hself hself
  have hoddNearCard : ∀ b, ((oddNear b).card : ℝ) ≤ S.tagFrac * Fintype.card (OddRole n) := by
    intro b
    simpa [oddNear, oddScope] using S.odd_tag_near b
  have hevenNearCard : ∀ a, ((evenNear a).card : ℝ) ≤ S.tagFrac * Fintype.card (EvenRole n) := by
    intro a
    simpa [evenNear, evenScope] using S.even_tag_near a
  have hoddTail : ∀ y : Fin N, Q.pr (fun t => S.typThr ≤
      (Fintype.card (OddRole n) : ℝ)⁻¹ * ∑ b, Zodd y b t) ≤
        ((S.balConst + n * S.tagFrac * S.meanCap) / S.typThr) ^ n := by
    intro y
    simpa [Q, Zodd] using Lane_q_s10_c.pi_scattered_average_tail
      P oddScope oddNear hoddScopeDisjoint hoddSelf S.tagFrac S.meanCap
      S.balConst S.typThr hoddNearCard htagFrac0 S.meanCap_nonneg S.typThr_pos
      Zodd (fun y b => S.odd_local y b)
      (fun y b t => (S.core t).oddMean_nonneg y b)
      (fun y b t => S.odd_mean_cap t y b) hoddAverage n y
  have hevenTail : ∀ x : Fin N, Q.pr (fun t => S.typThr ≤
      (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, Zeven x a t) ≤
        ((S.balConst + n * S.tagFrac * S.meanCap) / S.typThr) ^ n := by
    intro x
    simpa [Q, Zeven] using Lane_q_s10_c.pi_scattered_average_tail
      P evenScope evenNear hevenScopeDisjoint hevenSelf S.tagFrac S.meanCap
      S.balConst S.typThr hevenNearCard htagFrac0 S.meanCap_nonneg S.typThr_pos
      Zeven (fun x a => S.even_local x a)
      (fun x a t => (S.core t).mean_nonneg x a)
      (fun x a t => S.even_mean_cap t x a) hevenAverage n x
  let oddAt (y : Fin N) (t : S.Slice → S.Tag) : ℝ :=
    (Fintype.card (OddRole n) : ℝ)⁻¹ * ∑ b, (S.core t).oddMean y b
  let evenAt (x : Fin N) (t : S.Slice → S.Tag) : ℝ :=
    (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, (S.core t).mean x a
  let badOdd : (S.Slice → S.Tag) → Prop := fun t => ∃ y, S.typThr ≤ oddAt y t
  let badEven : (S.Slice → S.Tag) → Prop := fun t => ∃ x, S.typThr ≤ evenAt x t
  have hoddUnion : Q.pr badOdd ≤ ∑ y : Fin N,
      Q.pr (fun t => S.typThr ≤ oddAt y t) := by
    simpa [badOdd, oddAt] using Lane_q_s10_c.pr_exists_finset_le_sum Q
      (Finset.univ : Finset (Fin N)) (fun y t => S.typThr ≤ oddAt y t)
  have hevenUnion : Q.pr badEven ≤ ∑ x : Fin N,
      Q.pr (fun t => S.typThr ≤ evenAt x t) := by
    simpa [badEven, evenAt] using Lane_q_s10_c.pr_exists_finset_le_sum Q
      (Finset.univ : Finset (Fin N)) (fun x t => S.typThr ≤ evenAt x t)
  let ratio : ℝ := ((S.balConst + n * S.tagFrac * S.meanCap) / S.typThr) ^ n
  have hoddUnionBound : Q.pr badOdd ≤ N * ratio := by
    calc
      Q.pr badOdd ≤ ∑ y : Fin N, Q.pr (fun t => S.typThr ≤ oddAt y t) := hoddUnion
      _ ≤ ∑ y : Fin N, ratio := Finset.sum_le_sum fun y hy => by
            simpa [oddAt] using hoddTail y
      _ = N * ratio := by simp [Finset.sum_const, nsmul_eq_mul]
  have hevenUnionBound : Q.pr badEven ≤ N * ratio := by
    calc
      Q.pr badEven ≤ ∑ x : Fin N, Q.pr (fun t => S.typThr ≤ evenAt x t) := hevenUnion
      _ ≤ ∑ x : Fin N, ratio := Finset.sum_le_sum fun x hx => by
            simpa [evenAt] using hevenTail x
      _ = N * ratio := by simp [Finset.sum_const, nsmul_eq_mul]
  have hbadBound : Q.pr (fun t => badOdd t ∨ badEven t) < 1 := by
    calc
      Q.pr (fun t => badOdd t ∨ badEven t) ≤ Q.pr badOdd + Q.pr badEven :=
        FinProb.pr_union Q badOdd badEven
      _ ≤ N * ratio + N * ratio := add_le_add hoddUnionBound hevenUnionBound
      _ = 2 * N * ratio := by ring
      _ < 1 := by simpa [ratio] using S.tag_budget
  have hgood : ∃ t : S.Slice → S.Tag,
      (∀ y, oddAt y t < S.typThr) ∧ (∀ x, evenAt x t < S.typThr) := by
    by_contra hNo
    have hallBad : ∀ t : S.Slice → S.Tag, badOdd t ∨ badEven t := by
      intro t
      by_cases ho : badOdd t
      · exact Or.inl ho
      · right
        by_contra he
        apply hNo
        refine ⟨t, ?_, ?_⟩
        · intro y
          exact lt_of_not_ge (fun hy => ho ⟨y, by simpa [oddAt] using hy⟩)
        · intro x
          exact lt_of_not_ge (fun hx => he ⟨x, by simpa [evenAt] using hx⟩)
    have hprobOne : Q.pr (fun t => badOdd t ∨ badEven t) = 1 := by
      have hevent : (fun t => badOdd t ∨ badEven t) = fun _ => True := by
        funext t
        exact propext ⟨fun _ => True.intro, fun _ => hallBad t⟩
      rw [hevent]
      simp [FinProb.pr, Q.sum_eq_one]
    linarith [hbadBound, hprobOne]
  obtain ⟨t, hoddGood, hevenGood⟩ := hgood
  refine ⟨{
    core := S.core t
    oddThr := S.oddThr
    oddAvg := S.typThr
    meanAvg := S.typThr
    odd_avg := ?_
    mean_avg := ?_
    budget := S.core_budget t
  }⟩
  · intro y
    exact le_of_lt (hoddGood y)
  · intro x
    exact le_of_lt (hevenGood x)

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

set_option maxHeartbeats 4000000 in
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
  classical
  have hδ1 : δ < 1 / 2000 := by
    have : min (min η₀ ζ) 1 ≤ 1 := min_le_right _ _
    linarith
  obtain ⟨n2, h2⟩ := Lane_opus_s10_tagged.d2_valid_whp η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  obtain ⟨n3, h3⟩ := Lane_opus_s10_tagged.d3_tilt_caps η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  obtain ⟨n4, h4⟩ := Lane_opus_s10_tagged.d4_mask_strategy η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  obtain ⟨n5, h5⟩ := Lane_opus_s10_tagged.d5_odd_mean_cap η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  obtain ⟨n7a, h7a⟩ := Lane_opus_s10_tagged.d7a_predictive_failure η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  obtain ⟨n7b, h7b⟩ := Lane_opus_s10_tagged.d7b_even_row_cap η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  obtain ⟨n7c, h7c⟩ := Lane_opus_s10_tagged.d7c_even_mean_cap η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  obtain ⟨n8, h8⟩ := Lane_opus_s10_tagged.d8d_near_fractions δ hδ hδ1
  obtain ⟨n9, h9⟩ := Lane_opus_s10_tagged.d9_balanced_response η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  obtain ⟨n10, C10, h10⟩ := Lane_opus_s10_tagged.d10_budget η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ A
  refine ⟨max n10 (max n2 (max n3 (max n4 (max n5 (max n7a (max n7b (max n7c
    (max n8 n9)))))))), C10, ?_⟩
  intro n N E X Y G hlarge hdisc menu
  have hn0 := hlarge.1
  have hn10 : n10 ≤ n := by omega
  have hn2 : n2 ≤ n := by omega
  have hn3 : n3 ≤ n := by omega
  have hn4 : n4 ≤ n := by omega
  have hn5 : n5 ≤ n := by omega
  have hn7a : n7a ≤ n := by omega
  have hn7b : n7b ≤ n := by omega
  have hn7c : n7c ≤ n := by omega
  have hn8 : n8 ≤ n := by omega
  have hn9 : n9 ≤ n := by omega
  obtain ⟨⟨hnpos, h2n, hatom⟩, hbudget⟩ := h10 n N ⟨hn10, hlarge.2.1, hlarge.2.2⟩
  have hNle : N ≤ n * 2 ^ n := hlarge.2.2
  let M : Lane_opus_s10_tagged.MenuData n N E X Y G ζ δ κ :=
    { I := menu.I, μ := menu.μ, K := menu.K, lam := menu.lam, D := menu.D,
      μ_support := menu.μ_support, D_support := menu.D_support,
      lam_nonneg := menu.lam_nonneg, lam_sum := menu.lam_sum, μ_width := menu.μ_width,
      ν_width := menu.ν_width, D_atom := menu.D_atom, codegree := menu.codegree,
      avoid := menu.avoid }
  obtain ⟨σ, hσ⟩ := h4 n hn4 N E X Y G M h2n
  have hf := fun t => Lane_opus_s10_tagged.d1f_facts M σ t
  have h3' := fun t => h3 n hn3 N E X Y G M t h2n
  obtain ⟨hoddF, hevenF, htagF⟩ := h8 n hn8
  have hexp_le : Real.exp (-(n : ℝ) ^ ζ) ≤ Real.exp (-(n : ℝ) ^ ζ / 2) := by
    apply Real.exp_le_exp.mpr
    have := Real.rpow_nonneg (Nat.cast_nonneg n) ζ
    linarith
  have hcapOdd : ∀ t, Lane_opus_s10_tagged.oddCapOf M t ≤
      8 * Real.exp (2 * Lane_opus_s10_tagged.kT n δ *
        (Lane_opus_s10_tagged.TT n δ + Lane_opus_s10_tagged.mS n δ) + (n : ℝ) ^ δ) :=
    fun t => Real.iSup_le (fun p => (h3' t).1 p.1 p.2.1 p.2.2) (by positivity)
  have hcapOdd0 : ∀ t, 0 ≤ Lane_opus_s10_tagged.oddCapOf M t := fun t =>
    Real.iSup_nonneg fun p => mul_nonneg (Nat.cast_nonneg _) ((hf t).1 _ _ _)
  have hcapGroup : ∀ t, Lane_opus_s10_tagged.groupCapOf M t ≤
      Real.exp (-(n : ℝ) ^ ζ / 2) := fun t =>
    max_le (Real.iSup_le (fun p => (h3' t).2.2 p.1 p.2.1 p.2.2.1 p.2.2.2) (Real.exp_pos _).le)
      hexp_le
  have hcapGroup0 : ∀ t, 0 < Lane_opus_s10_tagged.groupCapOf M t := fun t =>
    lt_max_of_lt_right (Real.exp_pos _)
  have href : ∀ t, Lane_opus_s10_tagged.εRefOf M t σ ≤
      Real.exp (-(1 / 200 : ℝ) * Lane_opus_s10_tagged.aG n δ * Lane_opus_s10_tagged.kT n δ * n) :=
    fun t => Real.iSup_le (fun a => h7a n hn7a N E X Y G M σ h2n hNle t a) (Real.exp_pos _).le
  have href0 : ∀ t, 0 ≤ Lane_opus_s10_tagged.εRefOf M t σ := fun t =>
    Real.iSup_nonneg fun a => Lane_opus_s10_tagged.refFail_nonneg M t σ a
  have hrow : ∀ t, Lane_opus_s10_tagged.rowCapOf M t ≤
      Real.exp ((Real.log 2 - (1 / 100 : ℝ) * Lane_opus_s10_tagged.aG n δ) * n) := fun t =>
    Real.iSup_le (fun p => h7b n hn7b N E X Y G M t h2n p.1 p.2.1 p.2.2.1 p.2.2.2)
      (Real.exp_pos _).le
  have hrow0 : ∀ t, 0 ≤ Lane_opus_s10_tagged.rowCapOf M t := fun t =>
    Real.iSup_nonneg fun p => mul_nonneg (Nat.cast_nonneg _) ((hf t).2.2.1 _ _ _ _)
  have hoddF0 : 0 ≤ Lane_opus_s10_tagged.oddFracOf n δ :=
    Real.iSup_nonneg fun b => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hevenF0 : 0 ≤ Lane_opus_s10_tagged.evenFracOf n δ :=
    Real.iSup_nonneg fun a => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htagF0 : 0 ≤ Lane_opus_s10_tagged.tagFracOf n δ :=
    le_max_of_le_left (Real.iSup_nonneg fun b => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hmean0 : 0 ≤ Lane_opus_s10_tagged.meanCapOf M σ := le_max_left _ _
  have hmean : Lane_opus_s10_tagged.meanCapOf M σ ≤
      Real.exp ((Lane_opus_s10_tagged.mS n δ : ℝ) / 10) :=
    max_le (Real.exp_pos _).le (max_le
      (Real.iSup_le (fun p => h5 n hn5 N E X Y G M σ h2n hσ p.1 p.2.1 p.2.2) (Real.exp_pos _).le)
      (Real.iSup_le (fun p => h7c n hn7c N E X Y G M σ h2n hσ p.1 p.2.1 p.2.2)
        (Real.exp_pos _).le))
  have hB := fun t => hbudget
    ((Lane_opus_s10_tagged.historyLaw M σ t).pr (fun h => ¬ Lane_opus_s10_tagged.valid M t h))
    (Lane_opus_s10_tagged.oddCapOf M t) (Lane_opus_s10_tagged.groupCapOf M t)
    (Lane_opus_s10_tagged.εRefOf M t σ) (Lane_opus_s10_tagged.rowCapOf M t)
    (Lane_opus_s10_tagged.oddFracOf n δ) (Lane_opus_s10_tagged.evenFracOf n δ)
    (Lane_opus_s10_tagged.meanCapOf M σ) (Lane_opus_s10_tagged.tagFracOf n δ)
    (Lane_opus_s10_tagged.pr_nonneg' _ _) (h2 n hn2 N E X Y G M σ h2n hNle hdisc hσ t)
    (hcapOdd0 t) (hcapOdd t) (hcapGroup0 t) (hcapGroup t) (href0 t) (href t) (hrow0 t) (hrow t)
    hoddF0 hoddF hevenF0 hevenF hmean0 hmean htagF0 htagF
  let t₀ : Lane_opus_s10_tagged.Slice n δ → M.I := fun _ => Classical.arbitrary _
  refine ⟨{
    Slice := Lane_opus_s10_tagged.Slice n δ
    Tag := M.I
    core := fun t =>
      { H := Lane_opus_s10_tagged.History n N δ
        PH := Lane_opus_s10_tagged.historyLaw M σ t
        valid := Lane_opus_s10_tagged.valid M t
        ε_valid := (Lane_opus_s10_tagged.historyLaw M σ t).pr
          (fun h => ¬ Lane_opus_s10_tagged.valid M t h)
        valid_failure := le_rfl
        Grp := Lane_opus_s10_tagged.Site n δ
        grp := Lane_opus_s10_tagged.groupOf δ
        Cl := Lane_opus_s10_tagged.ClIdx M
        Kg := Lane_opus_s10_tagged.clusterLaw M t
        lab := Lane_opus_s10_tagged.labLaw M t
        oddRow := Lane_opus_s10_tagged.oddRow M t
        oddRow_nonneg := (hf t).1
        cluster_mean := (hf t).2.1
        groupCap := Lane_opus_s10_tagged.groupCapOf M t
        groupCap_pos := hcapGroup0 t
        group_cap := fun h _ g c y => le_max_of_le_left
          (Lane_opus_s10_tagged.le_iSup_fin
            (fun p : Lane_opus_s10_tagged.History n N δ × Lane_opus_s10_tagged.Site n δ ×
                Lane_opus_s10_tagged.ClIdx M × Fin N =>
              ∑ b ∈ Finset.univ.filter (fun b => Lane_opus_s10_tagged.groupOf δ b = p.2.1),
                (Lane_opus_s10_tagged.labLaw M t p.1 b p.2.2.1).w p.2.2.2) (h, g, c, y))
        atom_small := fun h _ b c y => ((h3' t).2.1 h b c y).trans hatom
        oddCap := Lane_opus_s10_tagged.oddCapOf M t
        oddCap_nonneg := hcapOdd0 t
        odd_cap := fun h _ b y => Lane_opus_s10_tagged.le_iSup_fin
          (fun p : Lane_opus_s10_tagged.History n N δ × _ × Fin N =>
            (N : ℝ) * Lane_opus_s10_tagged.oddRow M t p.1 p.2.1 p.2.2) (h, b, y)
        oddNear := Lane_opus_s10_tagged.oddNear δ
        oddNear_self := fun b => by simp [Lane_opus_s10_tagged.oddNear]
        oddFrac := Lane_opus_s10_tagged.oddFracOf n δ
        oddNear_card := fun b => Lane_opus_s10_tagged.card_le_ratio_mul _ _
          (Fintype.card_pos_iff.mpr ⟨b⟩)
          (Lane_opus_s10_tagged.le_iSup_fin
            (fun b => ((Lane_opus_s10_tagged.oddNear δ b).card : ℝ) /
              Fintype.card (Lane_opus_s10_tagged.OddRole n)) b)
        oddMean := Lane_opus_s10_tagged.oddMean M t σ
        oddMean_nonneg := (hf t).2.2.2.2.2.2.2.1
        odd_joint := Lane_opus_s10_tagged.d8a_odd_separated M σ hσ t
        predictive := Lane_opus_s10_tagged.predictive M t
        row := Lane_opus_s10_tagged.evenRow M t
        row_nonneg := (hf t).2.2.1
        row_sum := (hf t).2.2.2.1
        common_neighbor := (hf t).2.2.2.2.1
        predictive_local := fun a h ω ω' hω => (hf t).2.2.2.2.2.1 a h ω ω'
          (fun b hb => hω b (by simpa [star, Lane_opus_s10_tagged.starOf] using hb))
        row_local := fun a h x ω ω' hω => (hf t).2.2.2.2.2.2.1 a h x ω ω'
          (fun b hb => hω b (by simpa [star, Lane_opus_s10_tagged.starOf] using hb))
        rowCap := Lane_opus_s10_tagged.rowCapOf M t
        rowCap_nonneg := hrow0 t
        row_cap := fun h ω a x _ => Lane_opus_s10_tagged.le_iSup_fin
          (fun p : Lane_opus_s10_tagged.History n N δ × (_ → Fin N) × _ × Fin N =>
            (N : ℝ) * Lane_opus_s10_tagged.evenRow M t p.1 p.2.1 p.2.2.1 p.2.2.2) (h, ω, a, x)
        near := Lane_opus_s10_tagged.evenNear δ
        near_self := fun a => by simp [Lane_opus_s10_tagged.evenNear]
        nearFrac := Lane_opus_s10_tagged.evenFracOf n δ
        near_card := fun a => Lane_opus_s10_tagged.card_le_ratio_mul _ _
          (Fintype.card_pos_iff.mpr ⟨a⟩)
          (Lane_opus_s10_tagged.le_iSup_fin
            (fun a => ((Lane_opus_s10_tagged.evenNear δ a).card : ℝ) /
              Fintype.card (Lane_opus_s10_tagged.EvenRole n)) a)
        jointConst := 1
        jointConst_ge := le_rfl
        mean := Lane_opus_s10_tagged.evenMean M t σ
        mean_nonneg := (hf t).2.2.2.2.2.2.2.2
        ref_joint := Lane_opus_s10_tagged.d8b_even_separated M σ hσ t
        ε_ref := Lane_opus_s10_tagged.εRefOf M t σ
        ref_predictive := fun a =>
          Lane_opus_s10_tagged.le_iSup_fin (Lane_opus_s10_tagged.refFail M t σ) a
        n_pos := hnpos
        N_pos := lt_of_lt_of_le (Nat.two_pow_pos n) h2n }
    oddSlice := fun b => (Lane_opus_s10_tagged.groupOf δ b).1
    evenSlice := fun a => (Lane_opus_s10_tagged.evenSite δ a).1
    tagNbhd := Lane_opus_s10_tagged.tagNbhd δ
    tagNbhd_self := fun j => by simp [Lane_opus_s10_tagged.tagNbhd]
    odd_local := (Lane_opus_s10_tagged.d8c_tag_locality M σ hσ).1
    even_local := (Lane_opus_s10_tagged.d8c_tag_locality M σ hσ).2
    meanCap := Lane_opus_s10_tagged.meanCapOf M σ
    meanCap_nonneg := hmean0
    odd_mean_cap := fun t y b => le_max_of_le_right (le_max_of_le_left
      (Lane_opus_s10_tagged.le_iSup_fin
        (fun p : (Lane_opus_s10_tagged.Slice n δ → M.I) × Fin N × _ =>
          Lane_opus_s10_tagged.oddMean M p.1 σ p.2.1 p.2.2) (t, y, b)))
    even_mean_cap := fun t x a => le_max_of_le_right (le_max_of_le_right
      (Lane_opus_s10_tagged.le_iSup_fin
        (fun p : (Lane_opus_s10_tagged.Slice n δ → M.I) × Fin N × _ =>
          Lane_opus_s10_tagged.evenMean M p.1 σ p.2.1 p.2.2) (t, x, a)))
    tagFrac := Lane_opus_s10_tagged.tagFracOf n δ
    odd_tag_near := fun b => Lane_opus_s10_tagged.card_le_ratio_mul _ _
      (Fintype.card_pos_iff.mpr ⟨b⟩) (le_max_of_le_left
        (Lane_opus_s10_tagged.le_iSup_fin
          (fun b => ((Lane_opus_s10_tagged.oddTagNear δ b).card : ℝ) /
            Fintype.card (Lane_opus_s10_tagged.OddRole n)) b))
    even_tag_near := fun a => Lane_opus_s10_tagged.card_le_ratio_mul _ _
      (Fintype.card_pos_iff.mpr ⟨a⟩) (le_max_of_le_right
        (Lane_opus_s10_tagged.le_iSup_fin
          (fun a => ((Lane_opus_s10_tagged.evenTagNear δ a).card : ℝ) /
            Fintype.card (Lane_opus_s10_tagged.EvenRole n)) a))
    balConst := 4 / κ
    response := h9 n hn9 N E X Y G M σ h2n hσ
    typThr := 8 * (4 / κ + 1)
    typThr_pos := by positivity
    tag_budget := (hB t₀).1
    oddThr := 1 / 10 ^ 9
    core_budget := fun t => ⟨by norm_num, (hB t).2⟩ }⟩

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
