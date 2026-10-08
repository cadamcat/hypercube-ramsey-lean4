import HypercubeRamsey.S06.Stages
import HypercubeRamsey.S06.Prob
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.S06.Lane_sol_s06_ci

open Classical
open Filter
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 1000000

/-- Restricting an independent array along an injection preserves its product law. -/
theorem pi_pr_comp {α β Ω : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype Ω]
    (f : α ↪ β) (P : β → FinProb Ω) (A : (α → Ω) → Prop) :
    (FinProb.pi P).pr (fun o => A (fun i => o (f i))) =
      (FinProb.pi (fun i => P (f i))).pr A := by
  let s : Finset β := Finset.univ.image f
  let e : α ≃ {i // i ∈ s} := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => f.injective (congrArg Subtype.val h), by
      intro i
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp i.2
      exact ⟨a, Subtype.ext ha⟩⟩
  let g : ({i // i ∈ s} → Ω) → ℝ := fun o => if A (fun i => o (e i)) then 1 else 0
  rw [Lane_q_s06_stages.finprob_pr_eq_expect_indicator,
    Lane_q_s06_stages.finprob_pr_eq_expect_indicator]
  have h := FinProb.pi_marginal_expect P s g
  change (FinProb.pi P).expect (fun o => g (fun i => o i.1)) = _
  rw [h]
  unfold FinProb.expect
  let ep : ({i // i ∈ s} → Ω) ≃ (α → Ω) :=
    Equiv.arrowCongr e.symm (Equiv.refl Ω)
  rw [← Equiv.sum_comp ep.symm]
  apply Finset.sum_congr rfl
  intro o _
  have hw : (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w (ep.symm o) =
      (FinProb.pi (fun i => P (f i))).w o := by
    change (∏ i : {i // i ∈ s}, (P i.1).w (ep.symm o i)) = ∏ i, (P (f i)).w (o i)
    symm
    refine Fintype.prod_equiv e _ _ ?_
    intro i
    have hei : (e i).val = f i := rfl
    have hoi : ep.symm o (e i) = o i := by simp [ep, Equiv.arrowCongr]
    rw [hoi, hei]
  rw [hw]
  congr 1
  have ho : (fun i => ep.symm o (e i)) = o := by
    funext i
    simp [ep, Equiv.arrowCongr]
  change (if A (fun i => ep.symm o (e i)) then 1 else 0) = if A o then 1 else 0
  rw [ho]

theorem pr_prod_fst {α β : Type} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α → Prop) :
    (P.prod Q).pr (fun ω => A ω.1) = P.pr A := by
  exact pr_bind_fst6 P (fun _ => Q) A

theorem pr_prod_le {α β : Type} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α × β → Prop) (c : ℝ)
    (h : ∀ a, Q.pr (fun b => A (a,b)) ≤ c) : (P.prod Q).pr A ≤ c := by
  rw [show P.prod Q = FinProb.bind P (fun _ => Q) from rfl, pr_bind_eq6]
  calc
    _ ≤ ∑ a, P.w a * c := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (h a) (P.nonneg a)
    _ = c := by rw [← Finset.sum_mul, P.sum_eq_one, one_mul]

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- Step 3 reads ID names only through their distinct tuple coordinates. -/
theorem s3Fail_image {Id Id' : Type} [Fintype Id] [DecidableEq Id]
    [Fintype Id'] [DecidableEq Id'] (f : Id ↪ Id')
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o : X.Data Id') :
    X.S3Fail H b (D.image (fun e => (f e.1, e.2))) o ↔
      X.S3Fail H b D (fun e => o (f e.1, e.2)) := by
  let q : Id × X.Ty → Id' × X.Ty := fun e => (f e.1, e.2)
  have hq : Function.Injective q := by
    intro a b h
    have ha : f a.1 = f b.1 := congrArg (fun c : Id' × X.Ty => c.1) h
    have hb : a.2 = b.2 := congrArg (fun c : Id' × X.Ty => c.2) h
    exact Prod.ext (f.injective ha) hb
  have hLow (ξ : Fin N) : X.LowGate H b (D.image q) ξ ↔ X.LowGate H b D ξ := by
    unfold Ctx6.LowGate
    have hFor : (∀ e ∈ D.image q, X.Step2Tests (X.withHid H (X.tgt b) ξ) e.2) ↔
        ∀ e ∈ D, X.Step2Tests (X.withHid H (X.tgt b) ξ) e.2 := by
      rw [Finset.forall_mem_image]
    rw [hFor]
  have hHid : X.locHid (D.image q) = X.locHid D := by
    ext ℓ
    simp only [Ctx6.locHid, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨e, ⟨d, hd, rfl⟩, hℓ⟩
      exact ⟨d, hd, hℓ⟩
    · rintro ⟨d, hd, hℓ⟩
      exact ⟨q d, ⟨d, hd, rfl⟩, hℓ⟩
  have hKeys : X.locKeys (D.image q) = X.locKeys D := by
    rw [Ctx6.locKeys, Ctx6.locKeys, hHid]
    congr 1
    rw [Finset.image_image]
    rfl
  have hBins (nm : ParentName6 X.Bin) : X.locBins (D.image q) nm = X.locBins D nm := by
    simp [Ctx6.locBins, hKeys]
  have hDensity (nm : ParentName6 X.Bin) (ξ : Fin N) :
      X.locDensity H nm (D.image q) ξ = X.locDensity H nm D ξ := by
    simp only [Ctx6.locDensity, hBins, hKeys, hHid]
  have hHigh (ξ : Fin N) : X.HighGate H b (D.image q) ξ ↔ X.HighGate H b D ξ := by
    unfold Ctx6.HighGate
    rw [hHid, Finset.forall_mem_image]
  have hMass (drop : Option (Id × X.Ty)) :
      X.s3Mass H b (D.image q) o (drop.map q) =
        X.s3Mass H b D (fun e => o (q e)) drop := by
    unfold Ctx6.s3Mass
    apply Finset.sum_congr rfl
    intro ξ _
    have hd (e : Id × X.Ty) : drop.map q = some (q e) ↔ drop = some e := by
      cases drop with
      | none => simp
      | some c => simp [hq.eq_iff]
    cases hm : X.stMode b
    · simp only [Ctx6.s3Weight, hm, Ctx6.lowWeight, hLow]
      congr 1
      rw [Finset.prod_image (by intro a _ b _ h; exact hq h)]
      apply Finset.prod_congr rfl
      intro e _
      simp only [hd]
      rfl
    · simp only [Ctx6.s3Weight, hm, Ctx6.highWeight, hHigh, hDensity]
      congr 1
      rw [Finset.prod_image (by intro a _ b _ h; exact hq h)]
      apply Finset.prod_congr rfl
      intro e _
      simp only [hd]
      rfl
  have hGate : X.S3TrueGate H b (D.image q) ↔ X.S3TrueGate H b D := by
    cases hm : X.stMode b <;> simp [Ctx6.S3TrueGate, hm, hLow, hHigh]
  have hNone : X.s3Mass H b (D.image q) o none =
      X.s3Mass H b D (fun e => o (q e)) none := by
    simpa only [Option.map_none] using hMass none
  have hTests : X.S3Tests H b (D.image q) o ↔
      X.S3Tests H b D (fun e => o (q e)) := by
    constructor
    · rintro ⟨hpos, hthr, hdel⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hNone] using hpos
      · simpa only [hNone] using hthr
      · intro c hc hmatch
        have h := hdel (q c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩) hmatch
        change X.s3Thr * X.s3Mass H b (D.image q) o ((some c).map q) ≤
          X.s3Mass H b (D.image q) o (none.map q) at h
        rw [hMass (some c), hMass none] at h
        exact h
    · rintro ⟨hpos, hthr, hdel⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hNone] using hpos
      · simpa only [hNone] using hthr
      · intro c hc hmatch
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
        change X.s3Thr * X.s3Mass H b (D.image q) o ((some d).map q) ≤
          X.s3Mass H b (D.image q) o (none.map q)
        rw [hMass (some d), hMass none]
        exact hdel d hd hmatch
  exact and_congr hGate (not_congr hTests)

/-- Failure probability is unchanged by injectively renaming the IDs. -/
theorem s3Fail_pr_image {Id Id' : Type} [Fintype Id] [DecidableEq Id]
    [Fintype Id'] [DecidableEq Id'] (f : Id ↪ Id')
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) :
    (X.dataLaw Id' H).pr (fun o => X.S3Fail H b (D.image (fun e => (f e.1, e.2))) o) =
      (X.dataLaw Id H).pr (fun o => X.S3Fail H b D o) := by
  let q : Id × X.Ty ↪ Id' × X.Ty := f.prodMap (Function.Embedding.refl _)
  have h := pi_pr_comp q (fun e => X.tupleLaw H e.2) (fun o => X.S3Fail H b D o)
  calc
    _ = (X.dataLaw Id' H).pr (fun o => X.S3Fail H b D (fun e => o (q e))) := by
      apply Lane_q_s06_stages.pr_congr
      intro o
      exact s3Fail_image X f H b D o
    _ = _ := h

/-- HistSupport bounds descriptors on any finite ID space, via an abstract renaming. -/
theorem s3Fail_pr_le {Id : Type} [Fintype Id] [DecidableEq Id]
    (hSupp : X.HistSupport) (H : X.Hist) (hH : X.histLaw.w H ≠ 0)
    (b : X.State) (hb : b ∈ X.g.L.oddStates)
    (perm : X.g.L.stNbr b → Finset Id) (D : Finset (Id × X.Ty))
    (hD : D ∈ X.descsIn b perm) :
    (X.dataLaw Id H).pr (fun o => X.S3Fail H b D o) ≤ Real.exp (-c₂ * X.k) := by
  obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hD
  have hcard := (Finset.mem_filter.mp hφ).2.2
  let s : Finset Id := Finset.univ.image φ
  let φs : X.g.L.stNbr b → s := fun a => ⟨φ a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  let incl : s ↪ Id := ⟨Subtype.val, Subtype.val_injective⟩
  have hs : Fintype.card s ≤ Fintype.card (Fin X.T) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using hcard
  let f : s ↪ Fin X.T := Classical.choice (Function.Embedding.nonempty_iff_card_le.mpr hs)
  have hImage (Id' : Type) [Fintype Id'] [DecidableEq Id'] (g : s ↪ Id') :
      (X.descOf b φs).image (fun e => (g e.1, e.2)) = X.descOf b (fun a => g (φs a)) := by
    simp only [Ctx6.descOf, Finset.image_image]
    rfl
  have hAbs : X.descOf b (fun a => f (φs a)) ∈ X.absDescs b := by
    apply Finset.mem_image.mpr
    refine ⟨fun a => f (φs a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    refine ⟨fun _ => Finset.mem_univ _, ?_⟩
    exact le_trans (Finset.card_le_univ _) (by simp)
  have hActual : (X.descOf b φs).image (fun e => (incl e.1, e.2)) = X.descOf b φ := by
    rw [hImage Id incl]
    congr 1
  calc
    _ = (X.dataLaw s H).pr (fun o => X.S3Fail H b (X.descOf b φs) o) := by
      rw [← hActual]
      exact s3Fail_pr_image X incl H b _
    _ = (X.dataLaw (Fin X.T) H).pr (fun o => X.S3Fail H b (X.descOf b (fun a => f (φs a))) o) := by
      rw [← hImage (Fin X.T) f]
      exact (s3Fail_pr_image X f H b _).symm
    _ ≤ _ := (hSupp H hH).2.2.2.2.2 b hb _ hAbs

/-- Pairwise disjoint descriptor coordinates yield the product of their failure probabilities. -/
theorem pr_all_failures {Id I : Type} [Fintype Id] [DecidableEq Id] [DecidableEq I]
    (H : X.Hist) (b : X.State) (s : Finset I) (D : I → Finset (Id × X.Ty))
    (hDisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j)) :
    (X.dataLaw Id H).pr (fun o => ∀ i ∈ s, X.S3Fail H b (D i) o) =
      ∏ i ∈ s, (X.dataLaw Id H).pr (fun o => X.S3Fail H b (D i) o) := by
  revert hDisj
  induction s using Finset.induction_on with
  | empty => intro _; simp [FinProb.pr, (X.dataLaw Id H).sum_eq_one]
  | @insert i s hi ih =>
    intro hDisj
    have hrest := ih (fun a ha b hb hab => hDisj a (Finset.mem_insert_of_mem ha)
      b (Finset.mem_insert_of_mem hb) hab)
    have hdep : FinProb.DependsOn (fun o : X.Data Id => ∀ j ∈ s, X.S3Fail H b (D j) o)
        (s.biUnion D) := by
      intro o o' h
      apply propext
      have hlocal j hj := Lane_q_s06_stages.s3Fail_iff_of_data_agree X H b (D j) o o'
        (fun e he => h e (Finset.mem_biUnion.mpr ⟨j, hj, he⟩))
      exact ⟨fun ho j hj => (hlocal j hj).1 (ho j hj),
        fun ho j hj => (hlocal j hj).2 (ho j hj)⟩
    have hds : Disjoint (D i) (s.biUnion D) := by
      apply Finset.disjoint_left.mpr
      intro e he hs
      obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp hs
      exact Finset.disjoint_left.mp
        (hDisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (fun h => hi (h.symm ▸ hj))) he hej
    have hprob := Lane_q_s06_stages.pi_pr_and_of_disjoint_depends
      (fun e : Id × X.Ty => X.tupleLaw H e.2)
      (fun o => X.S3Fail H b (D i) o) (fun o => ∀ j ∈ s, X.S3Fail H b (D j) o)
      (D i) (s.biUnion D) (Lane_q_s06_stages.s3Fail_dependsOn_data X H b (D i)) hdep hds
    change (X.dataLaw Id H).pr (fun o => X.S3Fail H b (D i) o ∧
      ∀ j ∈ s, X.S3Fail H b (D j) o) =
      (X.dataLaw Id H).pr (fun o => X.S3Fail H b (D i) o) *
        (X.dataLaw Id H).pr (fun o => ∀ j ∈ s, X.S3Fail H b (D j) o) at hprob
    rw [hrest] at hprob
    simpa only [Finset.forall_mem_insert, Finset.prod_insert hi] using hprob

theorem topScale_fourth_eventually (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ n₀, ∀ n ≥ n₀,
      topScale n (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀)) ≤ n ^ 4 := by
  let α := α₆ p₀
  let σ := σ₆ α
  let ζ := ζ₆ α
  let q : ℕ := ⌈(1 - ζ) / σ⌉₊
  have hα : 0 < α := lt_min (by norm_num) (by linarith)
  have hαle : α ≤ 1 / 10 ^ 12 := min_le_left _ _
  have hσ : 0 < σ := by dsimp [σ, σ₆]; positivity
  have hζeq : ζ = 2 * σ := by simp [σ, ζ, σ₆, ζ₆]; ring
  have hσsmall : σ < 1 / 4 := by
    rw [show σ = α / (10 ^ 6 : ℝ) by rfl, div_lt_iff₀ (by norm_num)]
    nlinarith [hαle]
  have hratioPos : 0 ≤ (1 - ζ) / σ := by
    apply div_nonneg
    · rw [hζeq]
      linarith
    · exact le_of_lt hσ
  have hqLower : (1 - ζ) / σ ≤ (q : ℝ) := Nat.le_ceil _
  have hqUpper : (q : ℝ) < (1 - ζ) / σ + 1 := Nat.ceil_lt_add_one hratioPos
  have hσqLower : 1 - ζ ≤ σ * q := by
    simpa [mul_comm] using (div_le_iff₀ hσ).mp hqLower
  have hσqUpper : σ * q ≤ 1 := by
    have hmul : (q : ℝ) * σ < 1 - ζ + σ := by
      calc
        (q : ℝ) * σ < ((1 - ζ) / σ + 1) * σ := mul_lt_mul_of_pos_right hqUpper hσ
        _ = 1 - ζ + σ := by field_simp [ne_of_gt hσ]
    rw [hζeq] at hmul
    nlinarith
  have hnTrend : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpowTrend : Tendsto (fun n : ℕ => (n : ℝ) ^ σ) atTop atTop :=
    (tendsto_rpow_atTop hσ).comp hnTrend
  have hpowEvent := hpowTrend.eventually_ge_atTop (2 : ℝ)
  have hNEvent := eventually_ge_atTop (2 ^ (q + 1) : ℕ)
  have hAll : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ σ ≥ 2 ∧ 2 ^ (q + 1) ≤ n := by
    filter_upwards [hpowEvent, hNEvent] with n hpow hn
    exact ⟨hpow, hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hpowN, hNq⟩ := hn₀ n hn
  have hpowone : 1 ≤ 2 ^ (q + 1) := one_le_pow₀ (by norm_num)
  have hn1 : 1 ≤ n := le_trans hpowone hNq
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : 0 < (n : ℝ) := by positivity
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hceilM : 2 ≤ ⌈(n : ℝ) ^ σ⌉₊ := by
    have hcast : (2 : ℝ) ≤ ⌈(n : ℝ) ^ σ⌉₊ :=
      le_trans hpowN (Nat.le_ceil _)
    exact_mod_cast hcast
  have hMdef : M = ⌈(n : ℝ) ^ σ⌉₊ := by
    dsimp [M]
    exact max_eq_right hceilM
  have hMlow : (n : ℝ) ^ σ ≤ (M : ℝ) := by
    rw [hMdef]
    exact Nat.le_ceil _
  have hceilMupper : (⌈(n : ℝ) ^ σ⌉₊ : ℝ) ≤ (n : ℝ) ^ σ + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hMupper : (M : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
    rw [hMdef]
    linarith [hceilMupper]
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlognupper : Real.log n ≤ n := by
    exact (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
  have hlogsq : (Real.log n) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hlognupper)
      (add_nonneg (by positivity) hlogn)
    nlinarith [hprod]
  have hceilRupper : (⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) ≤ (Real.log n) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hRupper : (R₀ : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    dsimp [R₀]
    rw [Nat.cast_max]
    apply max_le_iff.mpr
    constructor
    · have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        calc
          1 = (1 : ℝ) ^ 2 := by norm_num
          _ ≤ (n : ℝ) ^ 2 := by gcongr
      have htwo : (2 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
        calc
          2 = 2 * (1 : ℝ) := by ring
          _ ≤ 2 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hnSq (by norm_num)
      simpa using (by norm_num : (1 : ℝ) ≤ 2).trans htwo
    · exact le_trans hceilRupper (by nlinarith [hlogsq, hnR])
  have hRlower : 1 ≤ R₀ := by dsimp [R₀]; omega
  have htargetReal : (n : ℝ) ^ (1 - ζ) ≤ (M : ℝ) ^ q := by
    calc
      (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) ^ (σ * q) :=
        Real.rpow_le_rpow_of_exponent_le hnR hσqLower
      _ ≤ (M : ℝ) ^ q := by
        have hpow := Real.rpow_le_rpow (by positivity) hMlow (by positivity : 0 ≤ (q : ℝ))
        calc
          (n : ℝ) ^ (σ * (q : ℝ)) = ((n : ℝ) ^ σ) ^ (q : ℝ) :=
            Real.rpow_mul (x := (n : ℝ)) (by positivity) σ (q : ℝ)
          _ ≤ (M : ℝ) ^ (q : ℝ) := hpow
          _ = (M : ℝ) ^ q := by rw [Real.rpow_natCast]
  have htargetNat : target ≤ M ^ q * R₀ := by
    change ⌈(n : ℝ) ^ (1 - ζ)⌉₊ ≤ M ^ q * R₀
    rw [Nat.ceil_le]
    have hRnat : 1 ≤ R₀ := hRlower
    have hpowNat : (M : ℝ) ^ q ≤ (M ^ q * R₀ : ℕ) := by
      exact_mod_cast (Nat.le_mul_of_pos_right (M ^ q) (Nat.pos_of_ne_zero (by omega : R₀ ≠ 0)))
    exact htargetReal.trans hpowNat
  have hscaleExists : ∃ i, target ≤ M ^ i * R₀ := ⟨q, htargetNat⟩
  have hfind : Nat.find hscaleExists ≤ q := Nat.find_min' hscaleExists htargetNat
  have htop : topScale n σ ζ ≤ M ^ q * R₀ := by
    unfold topScale
    dsimp [M, R₀, target]
    have hbase : 1 ≤ M := by omega
    exact Nat.mul_le_mul_right R₀ (pow_le_pow_right' hbase hfind)
  have hMpow : (M : ℝ) ^ q ≤ (2 : ℝ) ^ q * n := by
    have hEqpow : ((n : ℝ) ^ σ) ^ q = (n : ℝ) ^ (σ * (q : ℝ)) := by
      calc
        ((n : ℝ) ^ σ) ^ q = ((n : ℝ) ^ σ) ^ (q : ℝ) := by rw [Real.rpow_natCast]
        _ = (n : ℝ) ^ (σ * (q : ℝ)) :=
          (Real.rpow_mul (x := (n : ℝ)) (by positivity) σ (q : ℝ)).symm
    calc
      (M : ℝ) ^ q ≤ (2 * (n : ℝ) ^ σ) ^ q := by gcongr
      _ = (2 : ℝ) ^ q * ((n : ℝ) ^ σ) ^ q := by rw [mul_pow]
      _ = (2 : ℝ) ^ q * (n : ℝ) ^ (σ * (q : ℝ)) := by
        rw [hEqpow]
      _ ≤ (2 : ℝ) ^ q * (n : ℝ) := by
        have hnexp : (n : ℝ) ^ (σ * (q : ℝ)) ≤ n := by
          calc
            (n : ℝ) ^ (σ * (q : ℝ)) ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hnR hσqUpper
            _ = n := by rw [Real.rpow_one]
        exact mul_le_mul_of_nonneg_left hnexp (by positivity)
  have hcoeff : 2 * (2 : ℝ) ^ q ≤ n := by
    have hNqReal : (2 : ℝ) ^ (q + 1) ≤ n := by exact_mod_cast hNq
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hNqReal
  have htopReal : (topScale n σ ζ : ℝ) ≤ (n : ℝ) ^ 4 := by
    have htopCast : (topScale n σ ζ : ℝ) ≤ (M ^ q * R₀ : ℕ) := by exact_mod_cast htop
    calc
      (topScale n σ ζ : ℝ) ≤ (M ^ q * R₀ : ℕ) := htopCast
      _ = (M : ℝ) ^ q * R₀ := by simp [Nat.cast_mul, Nat.cast_pow]
      _ ≤ ((2 : ℝ) ^ q * n) * (2 * (n : ℝ) ^ 2) :=
        mul_le_mul hMpow hRupper (by positivity) (by positivity)
      _ = (2 * (2 : ℝ) ^ q) * (n : ℝ) ^ 3 := by ring
      _ ≤ (n : ℝ) ^ 4 := by
        calc
          (2 * (2 : ℝ) ^ q) * (n : ℝ) ^ 3 ≤ (n : ℝ) * (n : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right hcoeff (by positivity)
          _ = (n : ℝ) ^ 4 := by ring
  exact_mod_cast htopReal


theorem parameter_growth (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ n₀, ∀ n ≥ n₀,
      let m := m₆ p₀ n
      let J := J₆ m
      let T := T₆ m
      let k := k₆ n m
      J ≥ 200000000 ∧ (T : ℝ) ≤ (1 / 10 ^ 14 : ℝ) * J ∧
        Real.log (T + 2) ≤ 2 * α₆ p₀ * Real.log n ∧ m ≤ n ∧ 12000 ≤ k ∧ 10 ^ 10 ≤ n := by
  let α := α₆ p₀
  have hα : 0 < α := lt_min (by norm_num) (by linarith)
  have hαle : α ≤ 1 / 10 ^ 12 := min_le_left _ _
  have hnTrend : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmTrend : Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_ ((tendsto_rpow_atTop hα).comp hnTrend)
    filter_upwards [] with n
    exact_mod_cast Nat.le_ceil ((n : ℝ) ^ α)
  have hpow04Trend : Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ) ^ (1 / 25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 25 : ℝ))).comp hmTrend
  have hpow039Trend : Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ) ^ (39 / 1000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (39 / 1000 : ℝ))).comp hmTrend
  have hlogTrend : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnTrend
  have hαlogTrend : Tendsto (fun n : ℕ => α * Real.log (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hα hlogTrend
  have hlogOne := hlogTrend.eventually_ge_atTop (1 : ℝ)
  have hαlogTwo := hαlogTrend.eventually_ge_atTop (Real.log 2)
  have hpow04 := hpow04Trend.eventually_ge_atTop (400000000 : ℝ)
  have hpow039 := hpow039Trend.eventually_ge_atTop (4 * 10 ^ 14 : ℝ)
  have hmLarge := hmTrend.eventually_ge_atTop (16 : ℝ)
  have hnLarge := (eventually_ge_atTop (10 ^ 10 : ℕ))
  have hAll : ∀ᶠ n : ℕ in atTop,
      let m := m₆ p₀ n
      let J := J₆ m
      let T := T₆ m
      let k := k₆ n m
      J ≥ 200000000 ∧ (T : ℝ) ≤ (1 / 10 ^ 14 : ℝ) * J ∧
        Real.log (T + 2) ≤ 2 * α * Real.log n ∧ m ≤ n ∧ 12000 ≤ k ∧ 10 ^ 10 ≤ n := by
    filter_upwards [hlogOne, hαlogTwo, hpow04, hpow039, hmLarge, hnLarge]
      with n hlogn hαlogn h04 h039 hm16 hn10
    dsimp
    let m := m₆ p₀ n
    let J := J₆ m
    let T := T₆ m
    let k := k₆ n m
    have hn1 : 1 ≤ n := by omega
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : 0 < (n : ℝ) := by positivity
    have hmreal : (16 : ℝ) ≤ (m : ℝ) := hm16
    have hmpos : 0 < (m : ℝ) := by linarith
    have hJfloor : (m : ℝ) ^ (1 / 25 : ℝ) < (J : ℝ) + 1 := by
      exact Nat.lt_floor_add_one _
    have hJlarge : 200000000 ≤ J := by
      have h04' : (400000000 : ℝ) ≤ (m : ℝ) ^ (1 / 25 : ℝ) := h04
      have : (200000000 : ℝ) < J := by nlinarith [hJfloor, h04']
      exact_mod_cast this.le
    have hJlower : (m : ℝ) ^ (1 / 25 : ℝ) / 2 ≤ J := by
      have h04' : (2 : ℝ) ≤ (m : ℝ) ^ (1 / 25 : ℝ) := by linarith [h04]
      nlinarith [hJfloor, h04']
    have hTceil : (T : ℝ) < (m : ℝ) ^ (1 / 1000 : ℝ) + 1 := by
      exact Nat.ceil_lt_add_one (by positivity)
    have hmPowOne : 1 ≤ (m : ℝ) ^ (1 / 1000 : ℝ) := by
      rw [← Real.rpow_zero (m : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [hmreal]) (by norm_num)
    have hTupper : (T : ℝ) ≤ 2 * (m : ℝ) ^ (1 / 1000 : ℝ) := by linarith [hTceil, hmPowOne]
    have h039 : (4 * 10 ^ 14 : ℝ) ≤ (m : ℝ) ^ (39 / 1000 : ℝ) := h039
    have hpowRel : (m : ℝ) ^ (1 / 25 : ℝ) =
        (m : ℝ) ^ (1 / 1000 : ℝ) * (m : ℝ) ^ (39 / 1000 : ℝ) := by
      rw [← Real.rpow_add hmpos]
      norm_num
    have hTsmall : (T : ℝ) ≤ (1 / 10 ^ 14 : ℝ) * J := by
      have h039mul := mul_le_mul_of_nonneg_right h039
        (by positivity : 0 ≤ (m : ℝ) ^ (1 / 1000 : ℝ))
      calc
        (T : ℝ) ≤ 2 * (m : ℝ) ^ (1 / 1000 : ℝ) := hTupper
        _ ≤ (1 / 10 ^ 14 : ℝ) * ((m : ℝ) ^ (1 / 25 : ℝ) / 2) := by
          rw [hpowRel]
          nlinarith [h039mul]
        _ ≤ (1 / 10 ^ 14 : ℝ) * J := by
          exact mul_le_mul_of_nonneg_left hJlower (by positivity)
    have hmUpper : (m : ℝ) ≤ 2 * (n : ℝ) ^ α := by
      have hceil : (m : ℝ) < (n : ℝ) ^ α + 1 := Nat.ceil_lt_add_one (by positivity)
      have hnPowOne : 1 ≤ (n : ℝ) ^ α := by
        rw [← Real.rpow_zero (n : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le hnR (le_of_lt hα)
      linarith [hceil, hnPowOne]
    have hmle : m ≤ n := by
      change ⌈(n : ℝ) ^ α⌉₊ ≤ n
      rw [Nat.ceil_le]
      have hαle1 : α ≤ 1 := le_trans hαle (by norm_num)
      simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnR hαle1
    have hTplus : (T : ℝ) + 2 ≤ m := by
      have hsqrt : (m : ℝ) ^ (1 / 2 : ℝ) ≤ (m : ℝ) / 4 := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
        nlinarith [hmreal]
      have hlowpow : (m : ℝ) ^ (1 / 1000 : ℝ) ≤ (m : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hmreal]) (by norm_num)
      nlinarith [hTceil, hsqrt, hlowpow, hmreal]
    have hlogM : Real.log (m : ℝ) ≤ Real.log 2 + α * Real.log n := by
      calc
        Real.log (m : ℝ) ≤ Real.log (2 * (n : ℝ) ^ α) :=
          Real.log_le_log hmpos hmUpper
        _ = Real.log 2 + α * Real.log n := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hnpos]
    have hlogT' : Real.log (T + 2) ≤ 2 * α * Real.log n := by
      calc
        Real.log (T + 2) ≤ Real.log (m : ℝ) :=
          Real.log_le_log (by positivity) hTplus
        _ ≤ Real.log 2 + α * Real.log n := hlogM
        _ ≤ 2 * α * Real.log n := by nlinarith [hαlogn]
    have hkceil : κ₆ * (J : ℝ) * Real.log n ≤ (k : ℝ) := by
      dsimp [k, k₆]
      exact Nat.le_ceil _
    have hklarge : 12000 ≤ k := by
      have hJreal : (200000000 : ℝ) ≤ J := by exact_mod_cast hJlarge
      have hJlog : (200000000 : ℝ) ≤ (J : ℝ) * Real.log n := by
        calc
          200000000 = 200000000 * 1 := by ring
          _ ≤ (J : ℝ) * Real.log n :=
            mul_le_mul hJreal hlogn (by norm_num) (by exact_mod_cast (Nat.zero_le J))
      have hklower : (20000 : ℝ) ≤ (k : ℝ) := by
        have hk' := hkceil
        have hκ : κ₆ * 200000000 = 20000 := by norm_num [κ₆]
        nlinarith [hk', hJlog, hκ]
      exact_mod_cast (show (12000 : ℝ) ≤ (k : ℝ) by linarith)
    exact ⟨hJlarge, hTsmall, hlogT', hmle, hklarge, hn10⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hAll
  exact ⟨n₀, fun n hn => hn₀ n hn⟩


theorem descriptor_rate_of_growth {n J T k : ℕ} {α : ℝ}
    (hn : 2 ≤ n) (hJ : 200000000 ≤ J)
    (hT : (T : ℝ) ≤ (1 / 10 ^ 14 : ℝ) * J)
    (hlogT : Real.log (T + 2) ≤ 2 * α * Real.log n)
    (hk : κ₆ * (J : ℝ) * Real.log n ≤ k)
    (hα0 : 0 ≤ α)
    (hα : α ≤ 1 / 10 ^ 12) :
    10 ^ 4 * (T * Real.log (3 * n * (4 * n ^ 10) + 2) +
      (J + 1) * Real.log (T + 2)) ≤ c₂ / 2 * k := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have harg : (3 : ℝ) * n * (4 * (n : ℝ) ^ 10) + 2 ≤ 14 * (n : ℝ) ^ 11 := by
    have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ 11 := by
      exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
    nlinarith
  have hlogArg : Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) ≤ 15 * Real.log n := by
    have hmon := Real.log_le_log (by positivity) harg
    have h14 : Real.log (14 : ℝ) ≤ 4 * Real.log 2 := by
      have h := Real.log_le_log (by norm_num) (by norm_num : (14 : ℝ) ≤ 2 ^ 4)
      rw [Real.log_pow] at h
      norm_num at h ⊢
      nlinarith
    have h2n : Real.log (2 : ℝ) ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hmon
    have h14n : Real.log (14 : ℝ) ≤ 4 * Real.log n := by nlinarith [h14, h2n]
    have hsum : Real.log (14 : ℝ) + 11 * Real.log n ≤ 15 * Real.log n := by
      nlinarith [h14n]
    exact hmon.trans hsum
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
  have hJplus : (J : ℝ) + 1 ≤ 2 * J := by nlinarith
  have hTarg : (T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) ≤
      (15 / 10 ^ 14 : ℝ) * J * Real.log n := by
    calc
      (T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) ≤
          (T : ℝ) * (15 * Real.log n) :=
            mul_le_mul_of_nonneg_left hlogArg (by exact_mod_cast (Nat.zero_le T))
      _ ≤ ((1 / 10 ^ 14 : ℝ) * J) * (15 * Real.log n) :=
            mul_le_mul_of_nonneg_right hT (mul_nonneg (by norm_num) hlogn)
      _ = (15 / 10 ^ 14 : ℝ) * J * Real.log n := by ring
  have hTtail : ((J : ℝ) + 1) * Real.log (T + 2) ≤
      4 * α * J * Real.log n := by
    calc
      ((J : ℝ) + 1) * Real.log (T + 2) ≤ ((J : ℝ) + 1) * (2 * α * Real.log n) :=
        mul_le_mul_of_nonneg_left hlogT (by positivity)
      _ ≤ (2 * J) * (2 * α * Real.log n) :=
        mul_le_mul_of_nonneg_right hJplus
          (mul_nonneg (mul_nonneg (by norm_num) hα0) hlogn)
      _ = 4 * α * J * Real.log n := by ring
  have hS : 10 ^ 4 *
      ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
        ((J : ℝ) + 1) * Real.log (T + 2)) ≤ (c₂ / 2 : ℝ) * k := by
    have hα' : 0 ≤ α := hα0
    have hJreal : (200000000 : ℝ) ≤ J := by exact_mod_cast hJ
    have hJlog : (200000000 : ℝ) * Real.log n ≤ J * Real.log n :=
      mul_le_mul_of_nonneg_right hJreal hlogn
    have hcoeff : 10 ^ 4 * (15 / 10 ^ 14 + 4 * α) ≤
        (c₂ / 2 : ℝ) * κ₆ := by
      norm_num [κ₆, c₂] at hα ⊢
      nlinarith [hα]
    have hsumRate := add_le_add hTarg hTtail
    calc
      10 ^ 4 *
          ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
            ((J : ℝ) + 1) * Real.log (T + 2)) ≤
          10 ^ 4 * (15 / 10 ^ 14 * J * Real.log n + 4 * α * J * Real.log n) :=
            mul_le_mul_of_nonneg_left hsumRate (by norm_num)
      _ = 10 ^ 4 * ((15 / 10 ^ 14 + 4 * α) * J * Real.log n) := by ring
      _ = (10 ^ 4 * (15 / 10 ^ 14 + 4 * α)) * (J * Real.log n) := by ring
      _ ≤ ((c₂ / 2 : ℝ) * κ₆) * (J * Real.log n) :=
            mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (by positivity) hlogn)
      _ ≤ (c₂ / 2 : ℝ) * k := by
            have hk' := mul_le_mul_of_nonneg_left hk (by norm_num [c₂] : (0 : ℝ) ≤ c₂ / 2)
            nlinarith [hk']
  exact hS


end
end HypercubeRamsey.S06.Lane_sol_s06_ci
