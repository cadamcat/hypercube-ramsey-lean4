import HypercubeRamsey.S18.Nodes_q_s18_n3

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

/-- Retained-side support for every output, including abort and zero-mass
fallbacks, as required by the protocol. -/
def OutputSupported (P : TransferProtocol X) : Prop :=
  ∀ seed s, (P.output seed (P.replies seed s P.steps)).SupportedIn (T.Y k)

/-- The actual late pools used by the paper's masks lie in the retained side. -/
theorem latePool_subset_retained (D : LateData hPT) (j : Fin D.geom.r) :
    D.encoding.base.latePool j ⊆ T.Y k :=
  (D.encoding.base.latePool_reserve j).trans hPT.tiling_valid.reserveY_subset

theorem output_supported_of_latePool (P : TransferProtocol X)
    (h : ∀ seed s, ∃ j : Fin D.geom.r,
      (P.output seed (P.replies seed s P.steps)).SupportedIn (D.encoding.base.latePool j)) :
    OutputSupported P := by
  intro seed s
  obtain ⟨j, hj⟩ := h seed s
  intro y hy
  exact hj y (fun hmem => hy (latePool_subset_retained D j hmem))

private theorem pr_mono {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (A B : Ω → Prop) (h : ∀ s, A s → B s) : Q.pr A ≤ Q.pr B := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : A s
  · simp [hs, h s hs]
  · simp only [hs, ↓reduceIte]
    split_ifs <;> [exact Q.nonneg s; exact le_rfl]

/-- A supported broad replacement whose deviations contain the original event
preserves all protocol premises, including the pointwise reduction inequality. -/
noncomputable def replaceOutput (P : TransferProtocol X)
    (out : P.Seed → List P.Reply → Law (T.S.N k))
    (hb : ∀ seed s, (out seed (P.replies seed s P.steps)).WidthLE (κ.α * T.S.n k / 2))
    (hs : ∀ seed s, (out seed (P.replies seed s P.steps)).SupportedIn (T.Y k))
    (hd : ∀ seed s x z, X.allowed x z →
      X.deviates (P.output seed (P.replies seed s P.steps)) x z →
      X.deviates (out seed (P.replies seed s P.steps)) x z) : TransferProtocol X :=
  { P with
    output := out
    broad := hb
    output_supported := hs
    reduction := P.reduction.trans (mul_le_mul_of_nonneg_left
      (pr_mono (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)) _ _ (by
        rintro ⟨s, seed⟩ ⟨x, z, ha, hs, hdev⟩
        exact ⟨x, z, ha, hs, hd seed s x z ha hdev⟩)) (Real.exp_pos _).le) }

/-- Changing only the output cannot change the stopping estimates. -/
theorem stopFacts_replaceOutput (P : TransferProtocol X)
    (out : P.Seed → List P.Reply → Law (T.S.N k))
    (hb : ∀ seed s, (out seed (P.replies seed s P.steps)).WidthLE (κ.α * T.S.n k / 2))
    (hs : ∀ seed s, (out seed (P.replies seed s P.steps)).SupportedIn (T.Y k))
    (hd : ∀ seed s x z, X.allowed x z →
      X.deviates (P.output seed (P.replies seed s P.steps)) x z →
      X.deviates (out seed (P.replies seed s P.steps)) x z) (c : ℝ) :
    StopFacts (replaceOutput P out hb hs hd) c ↔ StopFacts P c := Iff.rfl

theorem witnessMean_mono (pair : Bool)
    (f g : Fin (T.S.N k) → Option (Fin (T.S.N k)) → ℝ)
    (h : ∀ x z, f x z ≤ g x z) : witnessMean X pair f ≤ witnessMean X pair g := by
  cases pair <;> simp only [witnessMean, Bool.false_eq_true, ↓reduceIte]
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum fun x _ => h x none
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => h x (some z)

theorem witnessMean_one (pair : Bool) : witnessMean X pair (fun _ _ => 1) = 1 := by
  have hM : (PT.tiling.P (D.geom.patchOf X.target)).M ≠ 0 := by
    rw [← (PT.tiling.P _).cardX]
    exact ne_of_gt (Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty _).1)
  cases pair <;> simp [witnessMean, (PT.tiling.P _).cardX, hM, pow_two]

theorem witnessMean_mul_left (pair : Bool) (a : ℝ)
    (f : Fin (T.S.N k) → Option (Fin (T.S.N k)) → ℝ) :
    witnessMean X pair (fun x z => a * f x z) = a * witnessMean X pair f := by
  cases pair <;> simp only [witnessMean, Bool.false_eq_true, ↓reduceIte]
  · rw [← mul_div_assoc, Finset.mul_sum]
  · rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]

theorem witnessMean_add (pair : Bool)
    (f g : Fin (T.S.N k) → Option (Fin (T.S.N k)) → ℝ) :
    witnessMean X pair (fun x z => f x z + g x z) =
      witnessMean X pair f + witnessMean X pair g := by
  cases pair <;> simp [witnessMean, Finset.sum_add_distrib, add_div]

/-- Even an output law entirely outside the retained side can satisfy the
protocol atom cap. This lemma has no bad-sequence hypotheses. -/
theorem uniform_width_of_card {N : ℕ} (B : Finset (Fin N)) (hB : B.Nonempty)
    (w : ℝ) (hcard : (N : ℝ) ≤ Real.exp w * B.card) :
    (Law.unif B hB).WidthLE w := by
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  have hNpos : (0 : ℝ) < N := by
    obtain ⟨b, _⟩ := hB
    exact_mod_cast (Nat.zero_lt_of_lt b.isLt)
  intro x
  change (if x ∈ B then (B.card : ℝ)⁻¹ else 0) ≤ _
  split_ifs
  · rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hBpos hNpos).2
    simpa using hcard
  · positivity

theorem uniform_not_supported {N : ℕ} (B Y : Finset (Fin N))
    (hB : B.Nonempty) (hdis : Disjoint B Y) :
    ¬ (Law.unif B hB).SupportedIn Y := by
  intro hs
  have hBcopy := hB
  obtain ⟨b, hb⟩ := hBcopy
  have hbY : b ∉ Y := fun h => Finset.disjoint_left.mp hdis hb h
  have hzero := hs b hbY
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  have hpos : 0 < (Law.unif B hB).w b := by
    change 0 < if b ∈ B then (B.card : ℝ)⁻¹ else 0
    simp [hb, hBpos]
  linarith

/-- The raw broad-law estimate used in both cylinder survival and the final
output estimate. Its second-side support hypothesis is explicit. -/
theorem broad_degree_exception (hdisc : TwoBudgetDisc T k
    (Real.rpow (T.S.n k : ℝ) κ.xs) (κ.α * T.S.n k) (bstar T k))
    (U : Law (T.S.N k)) (hU : U.SupportedIn (T.Y k))
    (hwidth : U.WidthLE (κ.α * T.S.n k / 2)) (hα : 0 ≤ κ.α) (i : Fin PT.tiling.m) :
    ∑ x ∈ Finset.univ.filter (fun x => bstar T k <
      |rowDeg (T.S.E k) PT.tiling.c x U - 1 / 2|),
      (Law.unif (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1).w x ≤
      2 * Real.exp (Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) -
        Real.rpow (T.S.n k : ℝ) κ.xs) := by
  let τ := Law.unif (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hτwidth : τ.WidthLE (Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M)) := by
    apply uniform_width_of_card
    rw [(PT.tiling.P i).cardX, Real.exp_log (div_pos hN hM)]
    exact le_of_eq (by field_simp)
  have hτsupport : τ.SupportedIn (T.X k) := by
    intro x hx
    have hnot : x ∉ (PT.tiling.P i).X := by
      intro hmem
      have hr := (hPT.tiling_valid.patch_supports i).2.1
        ((hPT.tiling_valid.patch_supports i).1 hmem)
      exact hx (Finset.mem_sdiff.mp hr).1
    change (if x ∈ (PT.tiling.P i).X then ((PT.tiling.P i).X.card : ℝ)⁻¹ else 0) = 0
    simp [hnot]
  have hp : (κ.α * T.S.n k / 2 ≤ κ.α * T.S.n k ∧
      Real.rpow (T.S.n k : ℝ) κ.xs ≤ Real.rpow (T.S.n k : ℝ) κ.xs) := by
    constructor
    · have hnonneg : 0 ≤ κ.α * (T.S.n k : ℝ) := mul_nonneg hα (by positivity)
      linarith
    · exact le_rfl
  have h := S15.Needs.exceptional_first hdisc PT.tiling.c (Or.inr hp)
    U τ hU hwidth hτsupport hτwidth
  simpa only [τ, rowDeg, deg, hit] using h

/-- A constant output with no hits produces singleton deviation with
probability one under every tilted law. -/
theorem constant_no_hits_deviates (U : Law (T.S.N k))
    (hb : 10 * bstar T k < 1 / 2) (x : Fin (T.S.N k))
    (hmiss : ∀ y, U.w y ≠ 0 → ¬ Hits (T.S.E k) PT.tiling.c x y) :
    X.deviates U x none := by
  have hdegree : rowDeg (T.S.E k) PT.tiling.c x U = 0 := by
    unfold rowDeg
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : U.w y = 0
    · simp [hy]
    · simp [hmiss y hy]
  change 10 * bstar T k < |rowDeg (T.S.E k) PT.tiling.c x U - 1 / 2|
  simpa [hdegree] using hb

theorem constant_no_hits_pair_deviates (U : Law (T.S.N k))
    (hb : 10 * bstar T k < 1 / 4) (x y : Fin (T.S.N k))
    (hmiss : ∀ u, U.w u ≠ 0 → ¬ Hits (T.S.E k) PT.tiling.c x u) :
    X.deviates U x (some y) := by
  have hpair : (∑ u, U.w u * (if Hits (T.S.E k) PT.tiling.c x u ∧
      Hits (T.S.E k) PT.tiling.c y u then (1 : ℝ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : U.w u = 0
    · simp [hu]
    · simp [hmiss u hu]
  change 10 * bstar T k < |(∑ u, U.w u * (if Hits (T.S.E k) PT.tiling.c x u ∧
      Hits (T.S.E k) PT.tiling.c y u then (1 : ℝ) else 0)) - 1 / 4|
  rw [hpair]
  norm_num
  exact hb

theorem tilted_constant_deviation_pr (U : Law (T.S.N k))
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hd : X.deviates U x z) :
    (tiltedLaw X x z).pr (fun _ => X.deviates U x z) = 1 := by
  simp [FinLaw.pr, hd, FinLaw.sum_one]

/-- Discrepancy against supported laws does not inspect edges outside the
retained second side. -/
theorem dens_agree_on_support {N : ℕ} (E E' : Fin N → Fin N → Prop)
    (c : Colour) (μ ν : Law N) (Y : Finset (Fin N)) (hν : ν.SupportedIn Y)
    (hE : ∀ x y, y ∈ Y → (E x y ↔ E' x y)) :
    dens E c μ ν = dens E' c μ ν := by
  unfold dens
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y ∈ Y
  · have hhit : Hits E c x y ↔ Hits E' c x y := by
      cases c <;> simp [Hits, hE x y hy]
    simp [hhit]
  · simp [hν y hy]

/-- A constant output which is bad for every allowed singleton contradicts
the desired singleton estimate whenever the allowed witness mass is larger
than its claimed bound. No assumption about raw survival is needed. -/
theorem constant_output_obstruction (P : TransferProtocol X) (U : Law (T.S.N k))
    (hout : ∀ seed transcript, P.output seed transcript = U)
    (hdev : ∀ x, X.allowed x none → X.deviates U x none)
    (c : ℝ) (seed : P.Seed)
    (hmass : Real.exp (-Real.rpow (T.S.n k : ℝ) c) <
      witnessMean X false (fun x z => if X.allowed x z then 1 else 0)) :
    ¬ TiltedDeviationBound P c := by
  intro hbound
  have hsingle := (hbound seed).1
  have hpr (x : Fin (T.S.N k)) (hx : X.allowed x none) :
      (tiltedLaw X x none).pr (fun s =>
        X.deviates (P.output seed (P.replies seed s P.steps)) x none) = 1 := by
    simp only [hout]
    exact tilted_constant_deviation_pr U x none (hdev x hx)
  have heq :
      ((∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
        if X.allowed x none then (tiltedLaw X x none).pr (fun s =>
          X.deviates (P.output seed (P.replies seed s P.steps)) x none) else 0) /
          (PT.tiling.P (D.geom.patchOf X.target)).M) =
      witnessMean X false (fun x z => if X.allowed x z then 1 else 0) := by
    simp only [witnessMean, Bool.false_eq_true, ↓reduceIte]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with hx
    · exact hpr x hx
    · rfl
  rw [heq] at hsingle
  exact (not_lt_of_ge hsingle) hmass

/-- A protocol with no observations always satisfies the stopping estimates,
independently of its output law. -/
theorem stopFacts_zero_steps (P : TransferProtocol X) (hsteps : P.steps = 0) (c : ℝ) :
    StopFacts P c := by
  have htau (seed : P.Seed) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k)))
      (s : X.Raw) : stoppingTime P seed x z s c = 0 := by
    exact Nat.eq_zero_of_le_zero (by
      simpa [hsteps] using Lane_q_s18_n3.stoppingTime_le_steps P seed x z s c)
  intro seed pair
  constructor
  · intro t
    calc
      _ ≤ witnessMean X pair (fun _ _ => 1) := by
        apply witnessMean_mono
        intro x z
        split_ifs
        · simp [htau, Lane_q_s18_n3.likelihood_one_at_zero, FinLaw.E, FinLaw.sum_one]
        · norm_num
      _ = 1 := witnessMean_one pair
      _ ≤ 2 := by norm_num
  · have hzero : witnessMean X pair (fun x z => if X.allowed x z then
        (tiltedLaw X x z).pr (fun s =>
          factorException P seed x z s (stoppingTime P seed x z s c)) else 0) = 0 := by
      simp [htau, factorException, FinLaw.pr, witnessMean]
    rw [hzero]
    exact (Real.exp_pos _).le

/-- A constant bad output can be attached to a protocol with zero actual
observations. The reduction premise remains true because every original
witness deviation is retained. -/
noncomputable def zeroOutputProtocol (P : TransferProtocol X) (U : Law (T.S.N k))
    (hb : U.WidthLE (κ.α * T.S.n k / 2))
    (hs : U.SupportedIn (T.Y k))
    (hd : ∀ x z, X.allowed x z → X.deviates U x z) : TransferProtocol X :=
  { P with
    steps := 0
    steps_bound := by simp only [Nat.cast_zero]; positivity
    calls_bound := by intro seed s a; simp
    output := fun _ _ => U
    broad := by intro seed s; exact hb
    output_supported := by intro seed s; exact hs
    reduction := P.reduction.trans (mul_le_mul_of_nonneg_left
      (pr_mono (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)) _ _ (by
        rintro ⟨s, seed⟩ ⟨x, z, ha, hs, _⟩
        exact ⟨x, z, ha, hs, hd x z ha⟩)) (Real.exp_pos _).le) }

/-- A conditional obstruction with explicit supported bad-law premises.
It does not construct a bad sequence or a LateData.Spec instance. -/
theorem bad_constant_protocol (P : TransferProtocol X) (U : Law (T.S.N k))
    (hb : U.WidthLE (κ.α * T.S.n k / 2))
    (hs : U.SupportedIn (T.Y k))
    (hd : ∀ x z, X.allowed x z → X.deviates U x z)
    (cstop ctilt : ℝ) (seed : P.Seed)
    (hmass : Real.exp (-Real.rpow (T.S.n k : ℝ) ctilt) <
      witnessMean X false (fun x z => if X.allowed x z then 1 else 0)) :
    ∃ Q : TransferProtocol X, StopFacts Q cstop ∧ ¬ TiltedDeviationBound Q ctilt := by
  let Q := zeroOutputProtocol P U hb hs hd
  refine ⟨Q, stopFacts_zero_steps Q rfl cstop, ?_⟩
  exact constant_output_obstruction Q U (by intros; rfl)
    (fun x hx => hd x none hx) ctilt seed hmass

private theorem replies_length (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) :
    ∀ n, (P.replies seed s n).length = n := by
  intro n
  induction n with
  | zero => simp [P.replies_zero]
  | succ n ih => simp [P.replies_step, ih]

theorem replies_take (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw)
    {i n : ℕ} (hin : i ≤ n) : (P.replies seed s n).take i = P.replies seed s i := by
  induction n with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      simp [P.replies_zero]
  | succ n ih =>
      rw [P.replies_step]
      by_cases hi : i ≤ n
      · rw [List.take_append_of_le_length (l₂ := [P.answer seed (P.replies seed s n) s])
          (by simpa [replies_length] using hi)]
        exact ih hi
      · have hi : i = n + 1 := by omega
        subst i
        simp [P.replies_step, replies_length]

theorem replies_prefix_eq (P : TransferProtocol X) (seed : P.Seed) (s s' : X.Raw)
    {i t : ℕ} (hit : i ≤ t) (ht : P.replies seed s t = P.replies seed s' t) :
    P.replies seed s i = P.replies seed s' i := by
  rw [← replies_take P seed s hit, ← replies_take P seed s' hit, ht]

theorem likelihood_prefix_eq (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s s' : X.Raw)
    {i t : ℕ} (hit : i ≤ t) (ht : P.replies seed s t = P.replies seed s' t) :
    likelihood P seed x z s i = likelihood P seed x z s' i := by
  simp only [likelihood, replies_prefix_eq P seed s s' hit ht]

theorem factorException_prefix_eq (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s s' : X.Raw)
    {i t : ℕ} (hit : i ≤ t) (ht : P.replies seed s t = P.replies seed s' t) :
    factorException P seed x z s i ↔ factorException P seed x z s' i := by
  simp only [factorException, likelihood_prefix_eq P seed x z s s' hit ht,
    likelihood_prefix_eq P seed x z s s' (Nat.le_trans (Nat.sub_le i 1) hit) ht]

private theorem finite_change_measure {Ω B : Type*} [Fintype Ω]
    (Q R : FinLaw Ω) (f : Ω → B) (r F : Ω → ℝ)
    (hr : ∀ s s', f s = f s' → r s = r s')
    (hF : ∀ s s', f s = f s' → F s = F s')
    (hm : ∀ s, Q.pr (fun s' => f s' = f s) * r s = R.pr (fun s' => f s' = f s)) :
    Q.E (fun s => r s * F s) = R.E F := by
  let values := Finset.univ.image f
  have hsplit (P : FinLaw Ω) (G : Ω → ℝ) :
      P.E G = ∑ a ∈ values, ∑ s ∈ Finset.univ.filter (fun s => f s = a), P.w s * G s := by
    exact (Finset.sum_fiberwise_of_maps_to
      (fun s hs => Finset.mem_image.mpr ⟨s, hs, rfl⟩) _).symm
  rw [hsplit, hsplit]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp ha
  have hleft :
      (∑ u ∈ Finset.univ.filter (fun u => f u = f s), Q.w u * (r u * F u)) =
      (∑ u ∈ Finset.univ.filter (fun u => f u = f s), Q.w u) * (r s * F s) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hr u s (Finset.mem_filter.mp hu).2, hF u s (Finset.mem_filter.mp hu).2]
  have hright :
      (∑ u ∈ Finset.univ.filter (fun u => f u = f s), R.w u * F u) =
      (∑ u ∈ Finset.univ.filter (fun u => f u = f s), R.w u) * F s := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hF u s (Finset.mem_filter.mp hu).2]
  have hprob (P : FinLaw Ω) :
      (∑ u ∈ Finset.univ.filter (fun u => f u = f s), P.w u) =
      P.pr (fun u => f u = f s) := by rw [Finset.sum_filter]; rfl
  rw [hleft, hright, hprob, hprob, ← mul_assoc, hm]

/-- Exact change of measure for any function of a transcript prefix. -/
theorem likelihood_change_measure (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (t : ℕ)
    (F : X.Raw → ℝ)
    (hF : ∀ s s', P.replies seed s t = P.replies seed s' t → F s = F s') :
    X.rawLaw.E (fun s => likelihood P seed x z s t * F s) = (tiltedLaw X x z).E F := by
  exact finite_change_measure X.rawLaw (tiltedLaw X x z) (fun s => P.replies seed s t)
    (fun s => likelihood P seed x z s t) F
    (fun s s' h => likelihood_prefix_eq P seed x z s s' le_rfl h) hF
    (fun s => Lane_q_s18_n3.likelihood_mul_raw_prefix P seed x z s t)

/-- The likelihood process has expectation one at every deterministic time. -/
theorem likelihood_mean_one (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (t : ℕ) :
    X.rawLaw.E (fun s => likelihood P seed x z s t) = 1 := by
  have h := likelihood_change_measure P seed x z t (fun _ => 1) (by intros; rfl)
  simpa [FinLaw.E, FinLaw.sum_one] using h

/-- The martingale identity against an arbitrary earlier-prefix test. -/
theorem likelihood_centered_increment (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) {i t : ℕ} (hit : i ≤ t)
    (F : X.Raw → ℝ)
    (hF : ∀ s s', P.replies seed s i = P.replies seed s' i → F s = F s') :
    X.rawLaw.E (fun s => (likelihood P seed x z s t - likelihood P seed x z s i) * F s) = 0 := by
  have ht := likelihood_change_measure P seed x z t F
    (fun s s' h => hF s s' (replies_prefix_eq P seed s s' hit h))
  have hi := likelihood_change_measure P seed x z i F hF
  have heq : X.rawLaw.E (fun s => (likelihood P seed x z s t -
      likelihood P seed x z s i) * F s) =
      X.rawLaw.E (fun s => likelihood P seed x z s t * F s) -
        X.rawLaw.E (fun s => likelihood P seed x z s i * F s) := by
    simp only [FinLaw.E, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [heq, ht, hi, sub_self]

private def stopTrigger (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) (c : ℝ) (t : ℕ) : Prop :=
  factorException P seed x z s t ∨
    Real.exp (Real.rpow (T.S.n k : ℝ) c) < likelihood P seed x z s t

private theorem stoppingTime_le_of_trigger (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) (c : ℝ)
    {t : ℕ} (ht : t ≤ P.steps) (h : stopTrigger P seed x z s c t) :
    stoppingTime P seed x z s c ≤ t := by
  let stops := (Finset.range (P.steps + 1)).filter (stopTrigger P seed x z s c)
  have hmem : t ∈ stops := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
  have hne : stops.Nonempty := ⟨t, hmem⟩
  dsimp only [stoppingTime]
  split_ifs with hn
  · exact Finset.min'_le _ t (by simpa only [stops, stopTrigger] using hmem)
  · exact False.elim (hn (by simpa only [stops, stopTrigger] using hne))

private theorem no_trigger_before_stoppingTime (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) (c : ℝ)
    {t : ℕ} (ht : t < stoppingTime P seed x z s c) :
    ¬ stopTrigger P seed x z s c t := by
  intro h
  have hsteps := Lane_q_s18_n3.stoppingTime_le_steps P seed x z s c
  have hle := stoppingTime_le_of_trigger P seed x z s c (by omega) h
  omega

/-- Being stopped at a specified level is determined by that prefix. -/
theorem stoppingTime_prefix_event (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ)
    (s s' : X.Raw) {t : ℕ} (ht : t ≤ P.steps)
    (heq : P.replies seed s t = P.replies seed s' t) :
    stoppingTime P seed x z s c = t ↔ stoppingTime P seed x z s' c = t := by
  have htrigger {i : ℕ} (hi : i ≤ t) :
      stopTrigger P seed x z s c i ↔ stopTrigger P seed x z s' c i := by
    simp only [stopTrigger, factorException_prefix_eq P seed x z s s' hi heq,
      likelihood_prefix_eq P seed x z s s' hi heq]
  have hforward (u u' : X.Raw)
      (hg : ∀ i, i ≤ t → (stopTrigger P seed x z u c i ↔ stopTrigger P seed x z u' c i))
      (hτ : stoppingTime P seed x z u c = t) : stoppingTime P seed x z u' c = t := by
    apply Nat.le_antisymm
    · by_cases hlast : t = P.steps
      · simpa [hlast] using Lane_q_s18_n3.stoppingTime_le_steps P seed x z u' c
      · have hlt : stoppingTime P seed x z u c < P.steps := by omega
        have hstop := Lane_q_s18_n3.stoppingTime_stop_condition P seed x z u c hlt
        have hu : stopTrigger P seed x z u c t := by simpa [stopTrigger, hτ] using hstop
        exact stoppingTime_le_of_trigger P seed x z u' c ht ((hg t le_rfl).mp hu)
    · by_contra hn
      have hlt : stoppingTime P seed x z u' c < t := by omega
      have hstop := Lane_q_s18_n3.stoppingTime_stop_condition P seed x z u' c
        (by omega : stoppingTime P seed x z u' c < P.steps)
      have hu' : stopTrigger P seed x z u' c (stoppingTime P seed x z u' c) := hstop
      have hu := (hg _ (by omega)).mpr hu'
      exact no_trigger_before_stoppingTime P seed x z u c (by omega) hu
  exact ⟨hforward s s' (fun i hi => htrigger hi),
    hforward s' s (fun i hi => (htrigger hi).symm)⟩

theorem stoppingTime_before_prefix_event (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ) (s s' : X.Raw) (t : ℕ)
    (heq : P.replies seed s (t - 1) = P.replies seed s' (t - 1)) :
    stoppingTime P seed x z s c < t ↔ stoppingTime P seed x z s' c < t := by
  have hf (u u' : X.Raw) (hpre : P.replies seed u (t - 1) = P.replies seed u' (t - 1))
      (ht : stoppingTime P seed x z u c < t) : stoppingTime P seed x z u' c < t := by
    have hj : stoppingTime P seed x z u c ≤ t - 1 := by omega
    have hp := replies_prefix_eq P seed u u' hj hpre
    have hs := stoppingTime_prefix_event P seed x z c u u'
      (Lane_q_s18_n3.stoppingTime_le_steps P seed x z u c) hp
    have hu' := hs.mp rfl
    omega
  exact ⟨hf s s' heq, hf s' s heq.symm⟩

/-- The linear term in the stopped second-moment recurrence vanishes. This
is the martingale step in 18:611, separate from the quantitative error term. -/
theorem stopped_linear_term_zero (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ) (t : ℕ) :
    X.rawLaw.E (fun s => (likelihood P seed x z s t - likelihood P seed x z s (t - 1)) *
      (if t ≤ stoppingTime P seed x z s c then likelihood P seed x z s (t - 1) else 0)) = 0 := by
  apply likelihood_centered_increment P seed x z (Nat.sub_le t 1)
  intro s s' heq
  have hτ := stoppingTime_before_prefix_event P seed x z c s s' t heq
  have htest : t ≤ stoppingTime P seed x z s c ↔ t ≤ stoppingTime P seed x z s' c := by
    omega
  have hr := likelihood_prefix_eq P seed x z s s' le_rfl heq
  simp only [htest, hr]

private theorem sum_stopping_levels (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ) (s : X.Raw)
    (G : ℕ → ℝ) :
    (∑ t ∈ Finset.range (P.steps + 1), if stoppingTime P seed x z s c = t then G t else 0) =
      G (stoppingTime P seed x z s c) := by
  rw [Finset.sum_eq_single (stoppingTime P seed x z s c)]
  · simp
  · intro t _ hne
    simp [Ne.symm hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Lane_q_s18_n3.stoppingTime_le_steps P seed x z s c))))

/-- Change of measure at the actual stopping time for functions measured by
the stopped prefix. This is the identity used for barrier stops in 18:617–620. -/
theorem stopped_change_measure (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ) (F : X.Raw → ℝ)
    (hF : ∀ t, t ≤ P.steps → ∀ s s',
      stoppingTime P seed x z s c = t → stoppingTime P seed x z s' c = t →
      P.replies seed s t = P.replies seed s' t → F s = F s') :
    X.rawLaw.E (fun s => likelihood P seed x z s (stoppingTime P seed x z s c) * F s) =
      (tiltedLaw X x z).E F := by
  let τ : X.Raw → ℕ := fun s => stoppingTime P seed x z s c
  have hpart (Q : FinLaw X.Raw) (G : X.Raw → ℝ) :
      Q.E G = ∑ t ∈ Finset.range (P.steps + 1), Q.E (fun s => if τ s = t then G s else 0) := by
    unfold FinLaw.E
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum]
    congr 1
    exact (sum_stopping_levels P seed x z c s (fun _ => G s)).symm
  rw [hpart, hpart]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ P.steps := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
  have hm := likelihood_change_measure P seed x z t (fun s => if τ s = t then F s else 0) (by
    intro s s' heq
    have hevent := stoppingTime_prefix_event P seed x z c s s' ht' heq
    change τ s = t ↔ τ s' = t at hevent
    by_cases hs : τ s = t
    · rw [if_pos hs, if_pos (hevent.mp hs)]
      exact hF t ht' s s' hs (hevent.mp hs) heq
    · rw [if_neg hs, if_neg (fun hs' => hs (hevent.mpr hs'))])
  rw [← hm]
  unfold FinLaw.E
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : τ s = t
  · have hτs : stoppingTime P seed x z s c = t := hs
    simp [hs, hτs]
  · simp [hs]

/-- Optional stopping preserves the first moment; this does not supply the
second-moment estimate required by L18_2l. -/
theorem stopped_likelihood_mean_one (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ) :
    X.rawLaw.E (fun s => likelihood P seed x z s (stoppingTime P seed x z s c)) = 1 := by
  have h := stopped_change_measure P seed x z c (fun _ => 1) (by intros; rfl)
  simpa [FinLaw.E, FinLaw.sum_one] using h

/-- The tilted probability of a barrier crossing is bounded by the raw
stopped second moment divided by the barrier. -/
theorem tilted_barrier_probability (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c B : ℝ) (hB : 0 < B) :
    B * (tiltedLaw X x z).pr (fun s =>
      B < likelihood P seed x z s (stoppingTime P seed x z s c)) ≤
    X.rawLaw.E (fun s => likelihood P seed x z s (stoppingTime P seed x z s c) ^ 2) := by
  let τ : X.Raw → ℕ := fun s => stoppingTime P seed x z s c
  let R : X.Raw → ℝ := fun s => likelihood P seed x z s (τ s)
  have hmeas : ∀ t, t ≤ P.steps → ∀ s s', τ s = t → τ s' = t →
      P.replies seed s t = P.replies seed s' t →
      (if B < R s then (1 : ℝ) else 0) = (if B < R s' then 1 else 0) := by
    intro t _ s s' hs hs' heq
    have hr : R s = R s' := by
      dsimp [R]
      rw [hs, hs']
      exact likelihood_prefix_eq P seed x z s s' le_rfl heq
    rw [hr]
  have hchange := stopped_change_measure P seed x z c
    (fun s => if B < R s then 1 else 0) hmeas
  have hprob : (tiltedLaw X x z).E (fun s => if B < R s then 1 else 0) =
      (tiltedLaw X x z).pr (fun s => B < R s) := by
    unfold FinLaw.E FinLaw.pr
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : B < R s <;> simp [hs]
  change B * (tiltedLaw X x z).pr (fun s => B < R s) ≤ X.rawLaw.E (fun s => R s ^ 2)
  rw [← hprob, ← hchange]
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have hR : 0 ≤ R s := Lane_q_s18_n3.likelihood_nonneg P seed x z s (τ s)
  by_cases hs : B < R s
  · simp only [hs, ↓reduceIte, mul_one]
    have hmul := mul_le_mul_of_nonneg_right hs.le hR
    have hw := mul_le_mul_of_nonneg_left hmul (X.rawLaw.nonneg s)
    nlinarith only [hw]
  · simp only [hs, ↓reduceIte, mul_zero]
    exact mul_nonneg (X.rawLaw.nonneg s) (sq_nonneg _)

/-- The first part of StopFacts controls barrier stops by 2/B. Together
with its exception bound this leaves a constant factor to absorb by reducing
the final exponent. -/
theorem stopFacts_barrier_bound (P : TransferProtocol X) (c : ℝ) (h : StopFacts P c)
    (seed : P.Seed) (pair : Bool) :
    witnessMean X pair (fun x z => if X.allowed x z then (tiltedLaw X x z).pr (fun s =>
      Real.exp (Real.rpow (T.S.n k : ℝ) c) <
        likelihood P seed x z s (stoppingTime P seed x z s c)) else 0) ≤
      2 / Real.exp (Real.rpow (T.S.n k : ℝ) c) := by
  let B := Real.exp (Real.rpow (T.S.n k : ℝ) c)
  have hB : 0 < B := Real.exp_pos _
  apply (le_div_iff₀ hB).2
  rw [mul_comm, ← witnessMean_mul_left]
  calc
    _ ≤ witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.E (fun s =>
        likelihood P seed x z s (min P.steps (stoppingTime P seed x z s c)) ^ 2) else 0) := by
      apply witnessMean_mono
      intro x z
      by_cases ha : X.allowed x z
      · simp only [ha, ↓reduceIte]
        have hm : ∀ s, min P.steps (stoppingTime P seed x z s c) =
            stoppingTime P seed x z s c := fun s =>
          Nat.min_eq_right (Lane_q_s18_n3.stoppingTime_le_steps P seed x z s c)
        simp only [hm]
        exact tilted_barrier_probability P seed x z c B hB
      · simp [ha]
    _ ≤ 2 := (h seed pair).1 P.steps

private theorem pr_three {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (A B C F : Ω → Prop) (h : ∀ s, F s → A s ∨ B s ∨ C s) :
    Q.pr F ≤ Q.pr A + Q.pr B + Q.pr C := by
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  by_cases hf : F s
  · have hs := h s hf
    rcases hs with ha | hb | hc
    · simp only [hf, ha, ↓reduceIte]
      split_ifs <;> nlinarith [Q.nonneg s]
    · simp only [hf, hb, ↓reduceIte]
      split_ifs <;> nlinarith [Q.nonneg s]
    · simp only [hf, hc, ↓reduceIte]
      split_ifs <;> nlinarith [Q.nonneg s]
  · simp only [hf, ↓reduceIte]
    split_ifs <;> nlinarith [Q.nonneg s]

/-- The probabilistic transfer part of L18_2m. A separate raw, uniform-witness
deviation estimate is essential; StopFacts alone does not supply it. -/
theorem tilted_deviation_from_raw (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (c : ℝ) :
    (tiltedLaw X x z).pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x z) ≤
    (tiltedLaw X x z).pr (fun s =>
      factorException P seed x z s (stoppingTime P seed x z s c)) +
    (tiltedLaw X x z).pr (fun s => Real.exp (Real.rpow (T.S.n k : ℝ) c) <
      likelihood P seed x z s (stoppingTime P seed x z s c)) +
    Real.exp (Real.rpow (T.S.n k : ℝ) c) * X.rawLaw.pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x z) := by
  let τ : X.Raw → ℕ := fun s => stoppingTime P seed x z s c
  let B := Real.exp (Real.rpow (T.S.n k : ℝ) c)
  let dev : X.Raw → Prop := fun s => X.deviates (P.output seed (P.replies seed s P.steps)) x z
  let good : X.Raw → Prop := fun s => dev s ∧ τ s = P.steps ∧ likelihood P seed x z s P.steps ≤ B
  have hcover : ∀ s, dev s → factorException P seed x z s (τ s) ∨
      B < likelihood P seed x z s (τ s) ∨ good s := by
    intro s hd
    by_cases ht : τ s < P.steps
    · exact (Lane_q_s18_n3.stoppingTime_stop_condition P seed x z s c ht).imp_right Or.inl
    · have heq : τ s = P.steps := Nat.le_antisymm
        (Lane_q_s18_n3.stoppingTime_le_steps P seed x z s c) (Nat.le_of_not_gt ht)
      by_cases hbar : B < likelihood P seed x z s P.steps
      · exact Or.inr (Or.inl (by simpa [heq] using hbar))
      · exact Or.inr (Or.inr ⟨hd, heq, le_of_not_gt hbar⟩)
  have hgmeas : ∀ s s', P.replies seed s P.steps = P.replies seed s' P.steps →
      (good s ↔ good s') := by
    intro s s' heq
    have ht := stoppingTime_prefix_event P seed x z c s s' le_rfl heq
    have hl := likelihood_prefix_eq P seed x z s s' le_rfl heq
    simp only [good, dev, τ, heq, ht, hl]
  have hchange := likelihood_change_measure P seed x z P.steps
    (fun s => if good s then 1 else 0) (by
      intro s s' heq
      simp only [hgmeas s s' heq])
  have hprob : (tiltedLaw X x z).E (fun s => if good s then 1 else 0) =
      (tiltedLaw X x z).pr good := by
    unfold FinLaw.E FinLaw.pr
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : good s <;> simp [hs]
  have hgood : (tiltedLaw X x z).pr good ≤ B * X.rawLaw.pr dev := by
    rw [← hprob, ← hchange]
    unfold FinLaw.E FinLaw.pr
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    by_cases hg : good s
    · simp only [hg, hg.1, ↓reduceIte, mul_one]
      have hw := mul_le_mul_of_nonneg_left hg.2.2 (X.rawLaw.nonneg s)
      simpa [mul_comm] using hw
    · simp only [hg, ↓reduceIte, mul_zero]
      by_cases hd : dev s
      · simp only [hd, ↓reduceIte]
        exact mul_nonneg (Real.exp_pos _).le (X.rawLaw.nonneg s)
      · simp [hd]
  exact (pr_three (tiltedLaw X x z) _ _ good dev hcover).trans (by linarith only [hgood])

theorem stopFacts_tilted_deviation_from_raw (P : TransferProtocol X) (c : ℝ)
    (h : StopFacts P c) (seed : P.Seed) (pair : Bool) :
    witnessMean X pair (fun x z => if X.allowed x z then (tiltedLaw X x z).pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x z) else 0) ≤
    3 / Real.exp (Real.rpow (T.S.n k : ℝ) c) +
    Real.exp (Real.rpow (T.S.n k : ℝ) c) *
      witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr (fun s =>
        X.deviates (P.output seed (P.replies seed s P.steps)) x z) else 0) := by
  let B := Real.exp (Real.rpow (T.S.n k : ℝ) c)
  let fE := fun x z => if X.allowed x z then (tiltedLaw X x z).pr (fun s =>
    factorException P seed x z s (stoppingTime P seed x z s c)) else 0
  let fB := fun x z => if X.allowed x z then (tiltedLaw X x z).pr (fun s =>
    B < likelihood P seed x z s (stoppingTime P seed x z s c)) else 0
  let fR := fun x z => if X.allowed x z then X.rawLaw.pr (fun s =>
    X.deviates (P.output seed (P.replies seed s P.steps)) x z) else 0
  have hpoint :
      witnessMean X pair (fun x z => if X.allowed x z then (tiltedLaw X x z).pr (fun s =>
        X.deviates (P.output seed (P.replies seed s P.steps)) x z) else 0) ≤
      witnessMean X pair (fun x z => fE x z + fB x z + B * fR x z) := by
    apply witnessMean_mono
    intro x z
    by_cases ha : X.allowed x z
    · simp only [fE, fB, fR, ha, ↓reduceIte]
      exact tilted_deviation_from_raw P seed x z c
    · simp [fE, fB, fR, ha]
  rw [witnessMean_add, witnessMean_add, witnessMean_mul_left] at hpoint
  have hex : witnessMean X pair fE ≤ 1 / B := by
    have he := (h seed pair).2
    have hexp : Real.exp (-Real.rpow (T.S.n k : ℝ) c) = 1 / B := by
      simp [B, Real.exp_neg, one_div]
    rw [hexp] at he
    exact he
  have hbar : witnessMean X pair fB ≤ 2 / B := stopFacts_barrier_bound P c h seed pair
  change _ ≤ 3 / B + B * witnessMean X pair fR
  have hsum : 1 / B + 2 / B = 3 / B := by rw [← add_div]; norm_num
  exact hpoint.trans (by
    calc
      _ ≤ 1 / B + 2 / B + B * witnessMean X pair fR :=
        add_le_add (add_le_add hex hbar) (le_refl _)
      _ = _ := by rw [hsum])

/-- Once the supported-output discrepancy argument supplies the raw bound,
the remaining transfer loses only a constant factor and half the exponent. -/
theorem tilted_bound_of_raw (P : TransferProtocol X) (c : ℝ) (hstop : StopFacts P c)
    (hslack : Real.log 4 + Real.rpow (T.S.n k : ℝ) (c / 2) ≤ Real.rpow (T.S.n k : ℝ) c)
    (hraw : ∀ seed pair,
      witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr (fun s =>
        X.deviates (P.output seed (P.replies seed s P.steps)) x z) else 0) ≤
        Real.exp (-2 * Real.rpow (T.S.n k : ℝ) c)) :
    TiltedDeviationBound P (c / 2) := by
  let a := Real.rpow (T.S.n k : ℝ) c
  have hnumeric : 3 / Real.exp a + Real.exp a * Real.exp (-2 * a) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) (c / 2)) := by
    have hprod : Real.exp a * Real.exp (-2 * a) = Real.exp (-a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hprod, Real.exp_neg]
    have hsum : 3 / Real.exp a + (Real.exp a)⁻¹ = 4 * Real.exp (-a) := by
      rw [Real.exp_neg]
      field_simp
      <;> ring
    rw [hsum]
    calc
      4 * Real.exp (-a) = Real.exp (Real.log 4 - a) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_neg]
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        dsimp [a]
        simp only [Real.rpow_eq_pow] at hslack ⊢
        linarith only [hslack])
  have hbound (seed : P.Seed) (pair : Bool) :
      witnessMean X pair (fun x z => if X.allowed x z then (tiltedLaw X x z).pr (fun s =>
        X.deviates (P.output seed (P.replies seed s P.steps)) x z) else 0) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) (c / 2)) := by
    have ht := stopFacts_tilted_deviation_from_raw P c hstop seed pair
    have hm := mul_le_mul_of_nonneg_left (hraw seed pair) (Real.exp_pos a).le
    exact ht.trans ((add_le_add (le_refl (3 / Real.exp a)) hm).trans hnumeric)
  intro seed
  exact ⟨by simpa only [witnessMean, Bool.false_eq_true, ↓reduceIte] using hbound seed false,
    by simpa only [witnessMean, ↓reduceIte] using hbound seed true⟩

theorem barrier_slack_eventually (T : Stage) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k in Filter.atTop,
      Real.log 4 + Real.rpow (T.S.n k : ℝ) (c / 2) ≤ Real.rpow (T.S.n k : ℝ) c := by
  have hn : Filter.Tendsto (fun k => (T.S.n k : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop
      Filter.atTop).comp T.S.n_tendsto
  have hp := (tendsto_rpow_atTop (show 0 < c / 2 by linarith)).comp hn
  filter_upwards [hp.eventually_ge_atTop 4] with k hk
  have hpow : Real.rpow (T.S.n k : ℝ) c = (Real.rpow (T.S.n k : ℝ) (c / 2)) ^ 2 := by
    calc
      _ = Real.rpow (T.S.n k : ℝ) ((c / 2) * (2 : ℝ)) := by congr 1; ring
      _ = Real.rpow (Real.rpow (T.S.n k : ℝ) (c / 2)) (2 : ℝ) :=
        Real.rpow_mul (by positivity) _ _
      _ = _ := Real.rpow_natCast _ 2
  have hlog : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  rw [hpow]
  change 4 ≤ Real.rpow (T.S.n k : ℝ) (c / 2) at hk
  simp only [Real.rpow_eq_pow] at *
  nlinarith

end HypercubeRamsey.S18.Lane_sol_s18_2lm
