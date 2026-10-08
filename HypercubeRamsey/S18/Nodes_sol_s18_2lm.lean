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

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm.Cylinder

set_option maxHeartbeats 400000

open Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem pr_nonneg {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω) (A : Ω → Prop) :
    0 ≤ Q.pr A := by
  classical
  exact Finset.sum_nonneg fun s _ => by split_ifs <;> simp [Q.nonneg s]

private theorem pr_le_one {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω) (A : Ω → Prop) :
    Q.pr A ≤ 1 := by
  classical
  rw [← Q.sum_one]
  exact Finset.sum_le_sum fun s _ => by split_ifs <;> simp [Q.nonneg s]

/-- Partition an event by a finite-valued observation. -/
theorem pr_partition {Ω B : Type*} [Fintype Ω] [Fintype B]
    (Q : FinLaw Ω) (f : Ω → B) (A : Ω → Prop) :
    (∑ p, Q.pr (fun s => f s = p ∧ A s)) = Q.pr A := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : A s <;> simp [h]

theorem map_mass {Ω B : Type*} [Fintype Ω] [Fintype B] [DecidableEq B]
    (Q : FinLaw Ω) (f : Ω → B) (p : B) :
    (FinLaw.map Q f).w p = Q.pr (fun s => f s = p) := by
  classical
  unfold FinLaw.map FinLaw.pr
  apply Finset.sum_congr rfl
  intro s _
  let d₁ : Decidable (f s = p) := inferInstance
  let d₂ : Decidable (f s = p) := Classical.propDecidable _
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  change @ite ℝ (f s = p) d₁ (Q.w s) 0 = @ite ℝ (f s = p) d₂ (Q.w s) 0
  rw [hd]

/-- The cylinder's next-coordinate law, including a harmless fallback on null
prefixes. No independence is assumed for the cylinder-conditioned law. -/
noncomputable def nextLaw {Ω B : Type*} [Fintype Ω] [Fintype B]
    {N : ℕ} (Q : FinLaw Ω) (f : Ω → B) (g : Ω → Fin N)
    (π : Law N) (p : B) : Law N :=
  if h : 0 < Q.pr (fun s => f s = p) then
    { w := fun y => Q.pr (fun s => f s = p ∧ g s = y) / Q.pr (fun s => f s = p)
      nonneg := fun y => div_nonneg (pr_nonneg Q _) h.le
      sum_eq_one := by
        rw [← Finset.sum_div]
        have heq : (∑ y, Q.pr (fun s => f s = p ∧ g s = y)) =
            Q.pr (fun s => f s = p) := by
          simpa only [and_comm] using pr_partition Q g (fun s => f s = p)
        rw [heq, div_self h.ne'] }
  else π

/-- Prefixes below a reference-density cutoff have at most the cutoff's total
mass. This is the first estimate in TeX 18:527–530. -/
theorem low_density_mass {B : Type*} [Fintype B] (Q R : FinLaw B)
    (ε : ℝ) (hε : 0 ≤ ε) :
    Q.pr (fun p => Q.w p < ε * R.w p) ≤ ε := by
  classical
  calc
    _ ≤ ∑ p, ε * R.w p := by
      apply Finset.sum_le_sum
      intro p _
      by_cases h : Q.w p < ε * R.w p
      · simp only [FinLaw.pr, h, ↓reduceIte]
        exact h.le
      · simp only [FinLaw.pr, h, ↓reduceIte]
        exact mul_nonneg hε (R.nonneg p)
    _ = ε := by rw [← Finset.mul_sum, R.sum_one, mul_one]

/-- Joint prefix/next-coordinate domination gives the advertised conditional
density cap off the low-density prefixes (TeX 18:530–533). -/
theorem nextLaw_domination {Ω B : Type*} [Fintype Ω] [Fintype B]
    {N : ℕ} (Q : FinLaw Ω) (f : Ω → B) (g : Ω → Fin N)
    (R : FinLaw B) (π : Law N) (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hdom : ∀ p y, Q.pr (fun s => f s = p ∧ g s = y) ≤ A * R.w p * π.w y)
    (p : B) (hp : 0 < Q.pr (fun s => f s = p))
    (hgood : ε * R.w p ≤ Q.pr (fun s => f s = p)) (y : Fin N) :
    (nextLaw Q f g π p).w y ≤ (A / ε) * π.w y := by
  classical
  simp only [nextLaw, hp, ↓reduceDIte]
  apply (div_le_iff₀ hp).2
  have hmul := mul_le_mul_of_nonneg_left hgood
    (mul_nonneg (div_nonneg hA hε.le) (π.nonneg y))
  have heq : (A / ε * π.w y) * (ε * R.w p) = A * R.w p * π.w y := by
    field_simp [hε.ne']
    <;> ring
  rw [heq] at hmul
  exact (hdom p y).trans hmul

/-- Domination preserves retained-side support and gives a width cap. The
scalar inequality is the exponent budget needed by the cylinder argument. -/
theorem nextLaw_broad {Ω B : Type*} [Fintype Ω] [Fintype B]
    {N : ℕ} (Q : FinLaw Ω) (f : Ω → B) (g : Ω → Fin N)
    (R : FinLaw B) (π : Law N) (Y : Finset (Fin N)) (A ε w : ℝ)
    (hA : 0 ≤ A) (hε : 0 < ε) (hπ : π.SupportedIn Y)
    (hπwidth : π.WidthLE w)
    (hcap : ∀ y, (A / ε) * π.w y ≤ Real.exp w / N)
    (hdom : ∀ p y, Q.pr (fun s => f s = p ∧ g s = y) ≤ A * R.w p * π.w y)
    (p : B) (hgood : ε * R.w p ≤ Q.pr (fun s => f s = p)) :
    (nextLaw Q f g π p).SupportedIn Y ∧ (nextLaw Q f g π p).WidthLE w := by
  classical
  by_cases hp : 0 < Q.pr (fun s => f s = p)
  · have hd := nextLaw_domination Q f g R π A ε hA hε hdom p hp hgood
    constructor
    · intro y hy
      exact le_antisymm (by simpa [hπ y hy] using hd y) ((nextLaw Q f g π p).nonneg y)
    · exact fun y => (hd y).trans (hcap y)
  · simpa only [nextLaw, hp, ↓reduceDIte] using And.intro hπ hπwidth

/-- Exact disintegration of survival across the next coordinate. -/
theorem nextLaw_event {Ω B : Type*} [Fintype Ω] [Fintype B]
    {N : ℕ} (Q : FinLaw Ω) (f : Ω → B) (g : Ω → Fin N)
    (π : Law N) (p : B) (H : Fin N → Prop) :
    Q.pr (fun s => f s = p ∧ H (g s)) =
      Q.pr (fun s => f s = p) * (nextLaw Q f g π p).pr H := by
  classical
  by_cases hp : 0 < Q.pr (fun s => f s = p)
  · simp only [nextLaw, hp, ↓reduceDIte, FinProb.pr]
    have hs : (∑ y, if H y then
        Q.pr (fun s => f s = p ∧ g s = y) / Q.pr (fun s => f s = p) else 0) =
        (∑ y, if H y then Q.pr (fun s => f s = p ∧ g s = y) else 0) /
          Q.pr (fun s => f s = p) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : H y <;> simp [hy]
    rw [hs, mul_div_cancel₀ _ hp.ne']
    rw [← pr_partition Q g (fun s => f s = p ∧ H (g s))]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : H y
    · simp only [hy, ↓reduceIte]
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro s _
      by_cases hg : g s = y <;> simp [hg, hy]
    · simp only [hy, ↓reduceIte]
      unfold FinLaw.pr
      apply Finset.sum_eq_zero
      intro s _
      by_cases hg : g s = y <;> simp [hg, hy]
  · have hzero : Q.pr (fun s => f s = p) = 0 :=
      le_antisymm (le_of_not_gt hp) (pr_nonneg Q _)
    rw [hzero, zero_mul]
    apply le_antisymm
    · calc
        _ ≤ Q.pr (fun s => f s = p) :=
          Lane_sol_s18_2lm.pr_mono Q _ _ (fun _ h => h.1)
        _ = 0 := hzero
    · exact pr_nonneg Q _

/-- One survival step with multiplicative degree error and the absolute mass
of exceptional value prefixes. -/
theorem survival_step {B : Type*} [Fintype B] (q : FinLaw B)
    (old : B → Prop) (next : B → ℝ) (p b : ℝ) (hb : 0 ≤ b)
    (hnext : ∀ v, 0 ≤ next v ∧ next v ≤ 1) (hp : 0 ≤ p ∧ p ≤ 1) :
    |q.E (fun v => if old v then next v else 0) - p * q.pr old| ≤
      b * q.pr old + q.pr (fun v => b < |next v - p|) := by
  classical
  have heq : q.E (fun v => if old v then next v else 0) - p * q.pr old =
      ∑ v, if old v then q.w v * (next v - p) else 0 := by
    unfold FinLaw.E FinLaw.pr
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : old v <;> simp [h] <;> ring
  rw [heq]
  calc
    _ ≤ ∑ v, |if old v then q.w v * (next v - p) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, (b * (if old v then q.w v else 0) +
        if b < |next v - p| then q.w v else 0) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases ho : old v <;> by_cases he : b < |next v - p|
      · simp only [ho, he, ↓reduceIte, abs_mul, abs_of_nonneg (q.nonneg v)]
        have hab : |next v - p| ≤ 1 := abs_le.mpr ⟨by linarith [(hnext v).1],
          by linarith [(hnext v).2]⟩
        nlinarith [mul_le_mul_of_nonneg_left hab (q.nonneg v), q.nonneg v]
      · simp only [ho, he, ↓reduceIte, abs_mul, abs_of_nonneg (q.nonneg v), add_zero]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (le_of_not_gt he) (q.nonneg v)
      · simp [ho, he, mul_nonneg hb (q.nonneg v), q.nonneg v]
      · simp [ho, he]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl

/-- Iterating the one-step estimate gives explicit upper and lower survival
windows. The additive error is total bad-prefix mass, not a per-transcript
union bound (TeX 18:550–570). -/
theorem survival_iteration (q : ℕ → ℝ) (p b ε : ℝ) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hlo : 0 ≤ p - b) (hhi : p + b ≤ 1) (hzero : q 0 = 1)
    (hstep : ∀ j, |q (j + 1) - p * q j| ≤ b * q j + ε) :
    ∀ m, (p - b) ^ m - m * ε ≤ q m ∧ q m ≤ (p + b) ^ m + m * ε := by
  classical
  intro m
  induction m with
  | zero => simp [hzero]
  | succ m ih =>
    have hs := abs_le.mp (hstep m)
    have hupper : q (m + 1) ≤ (p + b) * q m + ε := by nlinarith [hs.2]
    have hlower : (p - b) * q m - ε ≤ q (m + 1) := by nlinarith [hs.1]
    have hmulU := mul_le_mul_of_nonneg_left ih.2 (by linarith : 0 ≤ p + b)
    have hmulL := mul_le_mul_of_nonneg_left ih.1 hlo
    have heU : (p + b) * ((m : ℝ) * ε) ≤ (m : ℝ) * ε :=
      mul_le_of_le_one_left (mul_nonneg (by positivity) hε) hhi
    have heL : (p - b) * ((m : ℝ) * ε) ≤ (m : ℝ) * ε :=
      mul_le_of_le_one_left (mul_nonneg (by positivity) hε) (by linarith)
    rw [pow_succ, pow_succ, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith


open Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Fubini converts each fixed-prefix witness bound to an integrated
bad-prefix-mass bound. -/
theorem averaged_prefix_exceptions {B W : Type*} [Fintype B] [Fintype W]
    (q : FinLaw B) (τ : FinLaw W) (bad : B → W → Prop) (η : ℝ)
    (hbad : ∀ p, τ.pr (bad p) ≤ η) :
    τ.E (fun w => q.pr (fun p => bad p w)) ≤ η := by
  classical
  have heq : τ.E (fun w => q.pr (fun p => bad p w)) =
      q.E (fun p => τ.pr (bad p)) := by
    unfold FinLaw.E FinLaw.pr
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : bad p w <;> simp [h, mul_comm]
  rw [heq]
  calc
    _ ≤ ∑ p, q.w p * η :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hbad p) (q.nonneg p)
    _ = η := by rw [← Finset.sum_mul, q.sum_one, one_mul]

theorem mass_markov {W : Type*} [Fintype W] (τ : FinLaw W) (F : W → ℝ)
    (hF : ∀ w, 0 ≤ F w) (u : ℝ) (hu : 0 < u) :
    τ.pr (fun w => u < F w) ≤ τ.E F / u := by
  classical
  apply (le_div_iff₀ hu).2
  unfold FinLaw.pr FinLaw.E
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro w _
  by_cases h : u < F w
  · simp only [h, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left h.le (τ.nonneg w)
  · simp only [h, ↓reduceIte, zero_mul]
    exact mul_nonneg (τ.nonneg w) (hF w)

/-- Union over value coordinates and Markov over witnesses, with the exact
exception budget. There is no union over transcript values. -/
theorem coordinate_exception_markov {m : ℕ} {B : Fin m → Type*} {W : Type*}
    [∀ j, Fintype (B j)] [Fintype W] (q : ∀ j, FinLaw (B j)) (τ : FinLaw W)
    (bad : ∀ j, B j → W → Prop) (η u : ℝ) (hu : 0 < u)
    (hbad : ∀ j, τ.E (fun w => (q j).pr (fun p => bad j p w)) ≤ η) :
    τ.pr (fun w => u < ∑ j, (q j).pr (fun p => bad j p w)) ≤ m * η / u := by
  classical
  have hmean : τ.E (fun w => ∑ j, (q j).pr (fun p => bad j p w)) ≤ m * η := by
    have heq : τ.E (fun w => ∑ j, (q j).pr (fun p => bad j p w)) =
        ∑ j, τ.E (fun w => (q j).pr (fun p => bad j p w)) := by
      unfold FinLaw.E
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [heq]
    calc
      _ ≤ ∑ j : Fin m, η := Finset.sum_le_sum fun j _ => hbad j
      _ = m * η := by simp
  exact (mass_markov τ _ (fun w => Finset.sum_nonneg fun j _ => pr_nonneg (q j) _) u hu).trans
    (div_le_div_of_nonneg_right hmean hu.le)

/-- The explicit cylinder survival window after removing the Markov witness
exception. This is the quantitative finite form of TeX 18:550–570. -/
theorem survival_window_outside_exception {m : ℕ} {B : Fin m → Type*} {W : Type*}
    [∀ j, Fintype (B j)] [Fintype W] (q : ∀ j, FinLaw (B j)) (τ : FinLaw W)
    (bad : ∀ j, B j → W → Prop) (survival : W → ℕ → ℝ)
    (p b η u : ℝ) (hb : 0 ≤ b) (hu : 0 < u) (hlo : 0 ≤ p - b) (hhi : p + b ≤ 1)
    (hbad : ∀ j, τ.E (fun w => (q j).pr (fun v => bad j v w)) ≤ η)
    (hzero : ∀ w, survival w 0 = 1)
    (hstep : ∀ w (j : Fin m), |survival w (j.val + 1) - p * survival w j.val| ≤
      b * survival w j.val + (q j).pr (fun v => bad j v w)) :
    τ.pr (fun w => ¬ ((p - b) ^ m - m * u ≤ survival w m ∧
      survival w m ≤ (p + b) ^ m + m * u)) ≤ m * η / u := by
  classical
  have hgood : ∀ w, (∑ j, (q j).pr (fun v => bad j v w)) ≤ u →
      (p - b) ^ m - m * u ≤ survival w m ∧ survival w m ≤ (p + b) ^ m + m * u := by
    intro w hw
    have hstep' : ∀ j, j < m → |survival w (j + 1) - p * survival w j| ≤
        b * survival w j + u := by
      intro j hj
      let j' : Fin m := ⟨j, hj⟩
      have hjmass : (q j').pr (fun v => bad j' v w) ≤
          ∑ i, (q i).pr (fun v => bad i v w) :=
        Finset.single_le_sum (f := fun i : Fin m => (q i).pr (fun v => bad i v w))
          (fun i _ => pr_nonneg (q i) (fun v => bad i v w)) (Finset.mem_univ j')
      have hi := hstep w j'
      have he := hjmass.trans hw
      dsimp only [j'] at hi he
      linarith
    have hind : ∀ j, j ≤ m → (p - b) ^ j - j * u ≤ survival w j ∧
        survival w j ≤ (p + b) ^ j + j * u := by
      intro j
      induction j with
      | zero => intro _; simp [hzero]
      | succ j ih =>
        intro hj
        have hi := ih (by omega)
        have hs := abs_le.mp (hstep' j (by omega))
        have hmulU := mul_le_mul_of_nonneg_left hi.2 (by linarith : 0 ≤ p + b)
        have hmulL := mul_le_mul_of_nonneg_left hi.1 hlo
        have heU : (p + b) * ((j : ℝ) * u) ≤ (j : ℝ) * u :=
          mul_le_of_le_one_left (mul_nonneg (by positivity) hu.le) hhi
        have heL : (p - b) * ((j : ℝ) * u) ≤ (j : ℝ) * u :=
          mul_le_of_le_one_left (mul_nonneg (by positivity) hu.le) (by linarith)
        rw [pow_succ, pow_succ, Nat.cast_add, Nat.cast_one]
        constructor <;> nlinarith
    exact hind m le_rfl
  calc
    _ ≤ τ.pr (fun w => u < ∑ j, (q j).pr (fun v => bad j v w)) :=
      Lane_sol_s18_2lm.pr_mono τ _ _ (fun w hn => lt_of_not_ge (fun hw => hn (hgood w hw)))
    _ ≤ _ := coordinate_exception_markov q τ bad η u hu hbad


open Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem survival_disintegration {Ω B : Type*} [Fintype Ω] [Fintype B] [DecidableEq B]
    {N : ℕ} (Q : FinLaw Ω) (f : Ω → B) (g : Ω → Fin N) (π : Law N)
    (old : B → Prop) (H : Fin N → Prop) :
    Q.pr (fun s => old (f s) ∧ H (g s)) =
      (FinLaw.map Q f).E (fun p => if old p then (nextLaw Q f g π p).pr H else 0) := by
  classical
  rw [← pr_partition Q f (fun s => old (f s) ∧ H (g s))]
  unfold FinLaw.E
  apply Finset.sum_congr rfl
  intro p _
  rw [map_mass]
  by_cases ho : old p
  · simp only [ho, ↓reduceIte]
    rw [← nextLaw_event]
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro s _
    by_cases heq : f s = p <;> simp [heq, ho]
  · simp only [ho, ↓reduceIte, mul_zero]
    unfold FinLaw.pr
    apply Finset.sum_eq_zero
    intro s _
    by_cases heq : f s = p <;> simp [heq, ho]

theorem map_event {Ω B : Type*} [Fintype Ω] [Fintype B] [DecidableEq B]
    (Q : FinLaw Ω) (f : Ω → B) (H : B → Prop) :
    (FinLaw.map Q f).pr H = Q.pr (fun s => H (f s)) := by
  classical
  unfold FinLaw.pr FinLaw.map
  have heq : (∑ p, if H p then ∑ s, if f s = p then Q.w s else 0 else 0) =
      ∑ p, ∑ s, if H p ∧ f s = p then Q.w s else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : H p <;> simp [h]
  rw [heq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : H (f s)
  · rw [Finset.sum_eq_single (f s)]
    · simp [h]
    · intro v _ hv
      simp [Ne.symm hv]
    · simp
  · simp only [h, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro v _
    by_cases heq : f s = v
    · subst v; simp [h]
    · simp [heq]

/-- Discard low-density prefixes before Fubini. All retained prefixes have
uniform witness exception mass at most η. -/
theorem averaged_high_prefix_exceptions {B W : Type*} [Fintype B] [Fintype W]
    (q : FinLaw B) (τ : FinLaw W) (low : B → Prop) (bad : B → W → Prop)
    (ε η : ℝ) (hη : 0 ≤ η) (hlow : q.pr low ≤ ε)
    (hbad : ∀ p, ¬ low p → τ.pr (bad p) ≤ η) :
    τ.E (fun w => q.pr (fun p => bad p w)) ≤ ε + η := by
  classical
  let highbad := fun p w => ¬ low p ∧ bad p w
  have hhigh : ∀ p, τ.pr (highbad p) ≤ η := by
    intro p
    by_cases h : low p
    · simpa [highbad, h, FinLaw.pr] using hη
    · simpa only [highbad, h, not_false_eq_true, true_and] using hbad p h
  have hi := averaged_prefix_exceptions q τ highbad η hhigh
  have hpoint : ∀ w, q.pr (fun p => bad p w) ≤ q.pr low + q.pr (fun p => highbad p w) := by
    intro w
    unfold FinLaw.pr
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p _
    by_cases hl : low p <;> by_cases hb : bad p w <;> simp [highbad, hl, hb, q.nonneg p]
  calc
    _ ≤ τ.E (fun w => q.pr low + q.pr (fun p => highbad p w)) :=
      Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hpoint w) (τ.nonneg w)
    _ = q.pr low + τ.E (fun w => q.pr (fun p => highbad p w)) := by
      unfold FinLaw.E
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, τ.sum_one, one_mul]
    _ ≤ ε + η := add_le_add hlow hi


open Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {T : Stage} {k : ℕ}

/-- Uniform-witness discrepancy at a fixed value prefix. -/
theorem degree_exception_colour (c : Colour) (wS wL wU w : ℝ)
    (hdisc : TwoBudgetDisc T k wS wL (bstar T k))
    (τ U : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w)
    (hU : U.SupportedIn (T.Y k)) (hUw : U.WidthLE wU) (hw : wU ≤ wL) :
    τ.pr (fun x => bstar T k < |rowDeg (T.S.E k) c x U - 1 / 2|) ≤
      2 * Real.exp (w - wS) := by
  classical
  have h := S15.Needs.exceptional_first hdisc c
    (Or.inr ⟨hw, le_rfl⟩) U τ hU hUw hτ hτw
  simpa [FinProb.pr, Finset.sum_filter, rowDeg, deg, hit] using h

/-- Restricting a typical first hit costs at most log 4 in the width. -/
theorem hit_restrict_broad (c : Colour) (U : Law (T.S.N k)) (wU wL : ℝ)
    (hU : U.SupportedIn (T.Y k)) (hUw : U.WidthLE wU)
    (hslack : wU + Real.log 4 ≤ wL) (x : Fin (T.S.N k))
    (hx : |rowDeg (T.S.E k) c x U - 1 / 2| ≤ bstar T k)
    (hb : bstar T k ≤ 1 / 4) :
    ∃ V : Law (T.S.N k), V.SupportedIn (T.Y k) ∧ V.WidthLE wL ∧
      ∀ z, (∑ y, U.w y * (if Hits (T.S.E k) c x y ∧ Hits (T.S.E k) c z y
          then (1 : ℝ) else 0)) =
        rowDeg (T.S.E k) c x U * rowDeg (T.S.E k) c z V := by
  classical
  let H := Finset.univ.filter (fun y => Hits (T.S.E k) c x y)
  have hm : (∑ y ∈ H, U.w y) = rowDeg (T.S.E k) c x U := by
    simp only [H, Finset.sum_filter, rowDeg]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : Hits (T.S.E k) c x y <;> simp [h]
  have hlower : (1 / 4 : ℝ) ≤ ∑ y ∈ H, U.w y := by
    rw [hm]
    linarith [(abs_le.mp hx).1]
  have hmpos : 0 < ∑ y ∈ H, U.w y := lt_of_lt_of_le (by norm_num) hlower
  let V := U.restrict H hmpos
  refine ⟨V, ?_, ?_, ?_⟩
  · intro y hy
    simp [V, Law.restrict, hU y hy]
  · apply (Law.WidthLE.restrict hUw hmpos).mono
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hlower
    have heq : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [one_div, Real.log_inv]
    rw [heq] at hlog
    linarith
  · intro z
    rw [← hm]
    simp only [rowDeg, V, Law.restrict]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have hmem : (y ∈ H) ↔ Hits (T.S.E k) c x y := by simp [H]
    by_cases hx' : Hits (T.S.E k) c x y <;>
      by_cases hz' : Hits (T.S.E k) c z y <;>
      simp only [hmem, hx', hz', true_and, false_and, and_false, ↓reduceIte,
        mul_one, mul_zero, zero_mul]
    exact (mul_div_cancel₀ (U.w y) hmpos.ne').symm

private theorem pair_close (a d b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b) (hax : |a - 1 / 2| ≤ b) (hd : |d - 1 / 2| ≤ b) :
    |a * d - 1 / 4| ≤ 2 * b := by
  classical
  have heq : a * d - 1 / 4 = a * (d - 1 / 2) + (a - 1 / 2) / 2 := by ring
  rw [heq]
  calc
    _ ≤ |a * (d - 1 / 2)| + |(a - 1 / 2) / 2| := abs_add_le _ _
    _ ≤ b + b / 2 := by
      simp only [abs_mul, abs_of_nonneg ha.1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add ((mul_le_mul_of_nonneg_left hd ha.1).trans
        (mul_le_of_le_one_left hb ha.2)) (div_le_div_of_nonneg_right hax (by norm_num))
    _ ≤ 2 * b := by linarith

/-- Sequential hit restriction yields the pair exception bound, without a
codegree hypothesis and without requiring the witnesses to be allowed. -/
theorem pair_exception (c : Colour) (wS wL wU w : ℝ)
    (hdisc : TwoBudgetDisc T k wS wL (bstar T k))
    (τ U : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w)
    (hU : U.SupportedIn (T.Y k)) (hUw : U.WidthLE wU)
    (hslack : wU + Real.log 4 ≤ wL) (hb : bstar T k ≤ 1 / 4) :
    (∑ x, ∑ z, if 2 * bstar T k <
      |(∑ y, U.w y * (if Hits (T.S.E k) c x y ∧ Hits (T.S.E k) c z y
        then (1 : ℝ) else 0)) - 1 / 4| then τ.w x * τ.w z else 0) ≤
      4 * Real.exp (w - wS) := by
  classical
  let badx := fun x => bstar T k < |rowDeg (T.S.E k) c x U - 1 / 2|
  let badpair := fun x z => 2 * bstar T k <
    |(∑ y, U.w y * (if Hits (T.S.E k) c x y ∧ Hits (T.S.E k) c z y
      then (1 : ℝ) else 0)) - 1 / 4|
  let η := 2 * Real.exp (w - wS)
  have hbpos : 0 ≤ bstar T k := by unfold bstar; positivity
  have hlogpos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hbadx : τ.pr badx ≤ η := degree_exception_colour c wS wL wU w
    hdisc τ U hτ hτw hU hUw (by linarith)
  have hrow : ∀ x, (∑ z, if badpair x z then τ.w z else 0) ≤
      (if badx x then 1 else 0) + η := by
    intro x
    by_cases hx : badx x
    · have hs : (∑ z, if badpair x z then τ.w z else 0) ≤ 1 := by
        calc
          _ ≤ ∑ z, τ.w z := by
            apply Finset.sum_le_sum
            intro z _
            split_ifs <;> simp [τ.nonneg z]
          _ = 1 := τ.sum_eq_one
      simp only [hx, ↓reduceIte]
      linarith [Real.exp_pos (w - wS)]
    · obtain ⟨V, hV, hVw, hidentity⟩ := hit_restrict_broad c U wU wL hU hUw hslack x
        (le_of_not_gt hx) hb
      have hVex := degree_exception_colour c wS wL wL w hdisc τ V hτ hτw hV hVw le_rfl
      have hdeg : 0 ≤ rowDeg (T.S.E k) c x U ∧ rowDeg (T.S.E k) c x U ≤ 1 := by
        constructor
        · unfold rowDeg
          exact Finset.sum_nonneg fun y _ => mul_nonneg (U.nonneg y) (by split_ifs <;> norm_num)
        · rw [← U.sum_eq_one]
          apply Finset.sum_le_sum
          intro y _
          split_ifs <;> simp [U.nonneg y]
      simp only [hx, ↓reduceIte, zero_add]
      calc
        _ ≤ τ.pr (fun z => bstar T k < |rowDeg (T.S.E k) c z V - 1 / 2|) := by
          apply Finset.sum_le_sum
          intro z _
          by_cases hz : bstar T k < |rowDeg (T.S.E k) c z V - 1 / 2|
          · simp only [hz, ↓reduceIte]
            split_ifs <;> simp [τ.nonneg z]
          · have hn : ¬ badpair x z := by
              dsimp [badpair]
              rw [hidentity z]
              exact not_lt_of_ge (pair_close _ _ _ hdeg hbpos (le_of_not_gt hx)
                (le_of_not_gt hz))
            simp only [hn, ↓reduceIte]
            split_ifs <;> first | exact τ.nonneg z | exact le_rfl
        _ ≤ η := hVex
  calc
    _ = ∑ x, τ.w x * (∑ z, if badpair x z then τ.w z else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : badpair x z <;> simp [badpair, h]
    _ ≤ ∑ x, τ.w x * ((if badx x then 1 else 0) + η) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hrow x) (τ.nonneg x)
    _ = τ.pr badx + η := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, τ.sum_eq_one, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : badx x <;> simp [h]
    _ ≤ 4 * Real.exp (w - wS) := by dsimp [η] at *; linarith

noncomputable def allHits {m N : ℕ} {Ω W : Type*} (g : Fin m → Ω → Fin N)
    (H : W → Fin N → Prop) (w : W) (j : ℕ) (s : Ω) : Prop :=
  ∀ i : Fin m, i.val < j → H w (g i s)

/-- Quantitative survival under any dominated cylinder. Reference prefix laws
are arbitrary; only the next-coordinate joint domination is used. The full
survival probability lies in an explicit multiplicative/additive window off
witness mass at most m(ε+η)/u. -/
theorem cylinder_survival_window {m N : ℕ} {Ω W : Type*} {B : Fin m → Type*}
    [Fintype Ω] [Fintype W] [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
    (Q : FinLaw Ω) (τ : FinLaw W) (π : Law N) (Y : Finset (Fin N))
    (g : Fin m → Ω → Fin N) (f : ∀ j, Ω → B j) (R : ∀ j, FinLaw (B j))
    (old : ∀ j, B j → W → Prop) (H : W → Fin N → Prop)
    (A ε η u p b w : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) (hη : 0 ≤ η) (hu : 0 < u)
    (hp : 0 ≤ p ∧ p ≤ 1) (hb : 0 ≤ b) (hlo : 0 ≤ p - b) (hhi : p + b ≤ 1)
    (hπ : π.SupportedIn Y) (hπw : π.WidthLE w)
    (hcap : ∀ y, A / ε * π.w y ≤ Real.exp w / N)
    (hdom : ∀ j v y, Q.pr (fun s => f j s = v ∧ g j s = y) ≤ A * (R j).w v * π.w y)
    (hOld : ∀ j s x, old j (f j s) x ↔ allHits g H x j.val s)
    (hdisc : ∀ U : Law N, U.SupportedIn Y → U.WidthLE w →
      τ.pr (fun x => b < |U.pr (H x) - p|) ≤ η) :
    τ.pr (fun x => ¬ ((p - b) ^ m - m * u ≤ Q.pr (fun s => ∀ i, H x (g i s)) ∧
      Q.pr (fun s => ∀ i, H x (g i s)) ≤ (p + b) ^ m + m * u)) ≤ m * (ε + η) / u := by
  classical
  let q := fun j => FinLaw.map Q (f j)
  let next := fun j v => nextLaw Q (f j) (g j) π v
  let bad := fun j v x => b < |(next j v).pr (H x) - p|
  let surv := fun x j => Q.pr (allHits g H x j)
  have hbad : ∀ j, τ.E (fun x => (q j).pr (fun v => bad j v x)) ≤ ε + η := by
    intro j
    let low := fun v => (q j).w v < ε * (R j).w v
    apply averaged_high_prefix_exceptions (q j) τ low (bad j) ε η hη
    · exact low_density_mass (q j) (R j) ε hε.le
    · intro v hv
      have hgood : ε * (R j).w v ≤ Q.pr (fun s => f j s = v) := by
        simpa only [low, q, map_mass] using le_of_not_gt hv
      have hnext := nextLaw_broad Q (f j) (g j) (R j) π Y A ε w hA hε hπ hπw hcap
        (hdom j) v hgood
      exact hdisc (next j v) hnext.1 hnext.2
  have hzero : ∀ x, surv x 0 = 1 := by
    intro x
    simp [surv, allHits, FinLaw.pr, Q.sum_one]
  have hstep : ∀ x (j : Fin m), |surv x (j.val + 1) - p * surv x j.val| ≤
      b * surv x j.val + (q j).pr (fun v => bad j v x) := by
    intro x j
    have hsucc : ∀ s, allHits g H x (j.val + 1) s ↔
        old j (f j s) x ∧ H x (g j s) := by
      intro s
      rw [hOld]
      constructor
      · intro h
        exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
      · rintro ⟨h, hj⟩ i hi
        by_cases heq : i = j
        · simpa only [heq] using hj
        · exact h i (by have hv : i.val ≠ j.val := fun he => heq (Fin.ext he); omega)
    have hnew : surv x (j.val + 1) =
        (q j).E (fun v => if old j v x then (next j v).pr (H x) else 0) := by
      change Q.pr (allHits g H x (j.val + 1)) = _
      have heq : allHits g H x (j.val + 1) =
          (fun s => old j (f j s) x ∧ H x (g j s)) := funext fun s => propext (hsucc s)
      rw [heq]
      exact survival_disintegration Q (f j) (g j) π (fun v => old j v x) (H x)
    have hprev : (q j).pr (fun v => old j v x) = surv x j.val := by
      rw [map_event]
      have heq : (fun s => old j (f j s) x) = allHits g H x j.val :=
        funext fun s => propext (hOld j s x)
      rw [heq]
    have hnext_range : ∀ v, 0 ≤ (next j v).pr (H x) ∧ (next j v).pr (H x) ≤ 1 := by
      intro v
      constructor
      · unfold FinProb.pr
        apply Finset.sum_nonneg
        intro y _
        split_ifs <;> [exact (next j v).nonneg y; exact le_rfl]
      · calc
          _ ≤ ∑ y, (next j v).w y := by
            apply Finset.sum_le_sum
            intro y _
            split_ifs <;> [exact le_rfl; exact (next j v).nonneg y]
          _ = 1 := (next j v).sum_eq_one
    have hs := survival_step (q j) (fun v => old j v x) (fun v => (next j v).pr (H x))
      p b hb hnext_range hp
    rw [hprev, ← hnew] at hs
    exact hs
  have hwindow := survival_window_outside_exception q τ bad surv p b (ε + η) u
    hb hu hlo hhi hbad hzero hstep
  have hfinal : ∀ x, allHits g H x m = (fun s => ∀ i, H x (g i s)) := by
    intro x
    funext s
    apply propext
    exact ⟨fun h i => h i i.isLt, fun h i _ => h i⟩
  simpa only [surv, hfinal] using hwindow

/-- Independent whole-cell labels have a product atom bound before a
cylinder is imposed. -/
theorem pi_event {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i)) (H : ∀ i, Ω i → Prop) :
    (FinLaw.pi P).pr (fun s => ∀ i, H i (s i)) = ∏ i, (P i).pr (H i) := by
  classical
  unfold FinLaw.pr FinLaw.pi
  have hpoint : ∀ s : ∀ i, Ω i,
      (if ∀ i, H i (s i) then ∏ i, (P i).w (s i) else 0) =
        ∏ i, if H i (s i) then (P i).w (s i) else 0 := by
    intro s
    by_cases h : ∀ i, H i (s i)
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hz : (∏ j, if H j (s j) then (P j).w (s j) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      simp [h, hz]
  simp_rw [hpoint]
  exact (Fintype.prod_sum (fun i s => if H i s then (P i).w s else 0)).symm

theorem pi_labels_domination {m N : ℕ} {Ω : Fin m → Type*}
    [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i)) (g : ∀ i, Ω i → Fin N)
    (π : Law N) (a : ℝ) (ha : 0 ≤ a)
    (hatom : ∀ i y, (P i).pr (fun s => g i s = y) ≤ a * π.w y)
    (ys : Fin m → Fin N) :
    (FinLaw.map (FinLaw.pi P) (fun s i => g i (s i))).w ys ≤
      a ^ m * ∏ i, π.w (ys i) := by
  classical
  rw [map_mass]
  have heq : (fun s : ∀ i, Ω i => (fun i => g i (s i)) = ys) =
      (fun s : ∀ i, Ω i => ∀ i, g i (s i) = ys i) := funext fun s => propext funext_iff
  rw [heq, pi_event P (fun i s => g i s = ys i)]
  calc
    _ ≤ ∏ i, a * π.w (ys i) := Finset.prod_le_prod₀
      (fun i _ => pr_nonneg (P i) _) (fun i _ => hatom i (ys i))
    _ = a ^ m * ∏ i, π.w (ys i) := by rw [Finset.prod_mul_distrib]; simp

theorem conditioned_atom_domination {Ω B : Type*} [Fintype Ω] [Fintype B]
    [DecidableEq B] (Q : FinLaw Ω) (C : Finset Ω) (hC : 0 < ∑ s ∈ C, Q.w s)
    (g : Ω → B) (R : FinLaw B) (A : ℝ) (hdom : ∀ v, (FinLaw.map Q g).w v ≤ A * R.w v)
    (v : B) :
    (FinLaw.map (FinLaw.cond Q C hC) g).w v ≤
      (A / (∑ s ∈ C, Q.w s)) * R.w v := by
  classical
  simp only [map_mass] at *
  have hmass : (FinLaw.cond Q C hC).pr (fun s => g s = v) =
      Q.pr (fun s => s ∈ C ∧ g s = v) / (∑ s ∈ C, Q.w s) := by
    unfold FinLaw.pr FinLaw.cond
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s ∈ C <;> by_cases hg : g s = v <;> simp [hs, hg]
  rw [hmass]
  calc
    _ ≤ Q.pr (fun s => g s = v) / (∑ s ∈ C, Q.w s) :=
      div_le_div_of_nonneg_right (Lane_sol_s18_2lm.pr_mono Q _ _ (fun _ h => h.2)) hC.le
    _ ≤ A * R.w v / (∑ s ∈ C, Q.w s) := div_le_div_of_nonneg_right (hdom v) hC.le
    _ = _ := by ring

/-- Singleton discrepancy in the form consumed by cylinder_survival_window. -/
theorem single_hit_exception {T : Stage} {k : ℕ} (c : Colour) (wS wL wU w : ℝ)
    (hdisc : TwoBudgetDisc T k wS wL (bstar T k))
    (τ U : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w)
    (hU : U.SupportedIn (T.Y k)) (hUw : U.WidthLE wU) (hw : wU ≤ wL) :
    (⟨τ.w, τ.nonneg, τ.sum_eq_one⟩ : FinLaw (Fin (T.S.N k))).pr
      (fun x => bstar T k < |U.pr (Hits (T.S.E k) c x) - 1 / 2|) ≤
        2 * Real.exp (w - wS) := by
  classical
  have h := degree_exception_colour c wS wL wU w hdisc τ U hτ hτw hU hUw hw
  simpa [FinLaw.pr, FinProb.pr, rowDeg, mul_ite] using h

private theorem pr_pair_hits {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (U : Law N) (x z : Fin N) :
    U.pr (fun y => Hits E c x y ∧ Hits E c z y) =
      ∑ y, U.w y * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0) := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : Hits E c x y ∧ Hits E c z y <;> simp [h]

theorem pair_hit_exception {T : Stage} {k : ℕ} (c : Colour) (wS wL wU w : ℝ)
    (hdisc : TwoBudgetDisc T k wS wL (bstar T k))
    (τ U : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w)
    (hU : U.SupportedIn (T.Y k)) (hUw : U.WidthLE wU)
    (hslack : wU + Real.log 4 ≤ wL) (hb : bstar T k ≤ 1 / 4) :
    (FinLaw.bind (⟨τ.w, τ.nonneg, τ.sum_eq_one⟩ : FinLaw (Fin (T.S.N k)))
      (fun _ => ⟨τ.w, τ.nonneg, τ.sum_eq_one⟩)).pr (fun xz => 2 * bstar T k <
        |U.pr (fun y => Hits (T.S.E k) c xz.1 y ∧ Hits (T.S.E k) c xz.2 y) - 1 / 4|) ≤
      4 * Real.exp (w - wS) := by
  classical
  have h := pair_exception c wS wL wU w hdisc τ U hτ hτw hU hUw hslack hb
  have heq :
      (FinLaw.bind (⟨τ.w, τ.nonneg, τ.sum_eq_one⟩ : FinLaw (Fin (T.S.N k)))
        (fun _ => ⟨τ.w, τ.nonneg, τ.sum_eq_one⟩)).pr (fun xz => 2 * bstar T k <
          |U.pr (fun y => Hits (T.S.E k) c xz.1 y ∧ Hits (T.S.E k) c xz.2 y) - 1 / 4|) =
        ∑ x, ∑ z, if 2 * bstar T k <
          |(∑ y, U.w y * (if Hits (T.S.E k) c x y ∧ Hits (T.S.E k) c z y
            then (1 : ℝ) else 0)) - 1 / 4| then τ.w x * τ.w z else 0 := by
    unfold FinLaw.pr FinLaw.bind
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    simp_rw [pr_pair_hits]
  rw [heq]
  exact h

/-- The explicit survival window implies the paper's relative O(m b) estimate
when m b/p ≤ 1; the exponentially small additive error stays visible. -/
theorem relative_survival_window (m : ℕ) (p b u v : ℝ) (hp : 0 < p)
    (hb : 0 ≤ b) (hbp : b ≤ p) (hu : 0 ≤ u) (hsmall : (m : ℝ) * (b / p) ≤ 1)
    (hwindow : (p - b) ^ m - m * u ≤ v ∧ v ≤ (p + b) ^ m + m * u) :
    |v / p ^ m - 1| ≤ 2 * m * b / p + m * u / p ^ m := by
  classical
  let t := b / p
  have ht : 0 ≤ t := div_nonneg hb hp.le
  have htone : t ≤ 1 := (div_le_one hp).2 hbp
  have hpow (s : ℝ) : (p + s * b) ^ m = p ^ m * (1 + s * t) ^ m := by
    rw [← mul_pow]
    congr 1
    dsimp [t]
    field_simp [hp.ne']
    <;> ring
  have hupper : (p + b) ^ m ≤ p ^ m * (1 + 2 * (m : ℝ) * t) := by
    have hexp := Real.abs_exp_sub_one_le (x := (m : ℝ) * t) (by
      rw [abs_of_nonneg (mul_nonneg (by positivity) ht)]
      exact hsmall)
    have hpows : (1 + t) ^ m ≤ Real.exp ((m : ℝ) * t) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) m
    have heU : Real.exp ((m : ℝ) * t) ≤ 1 + 2 * (m : ℝ) * t := by
      rw [abs_of_nonneg (mul_nonneg (by positivity) ht)] at hexp
      linarith [(le_abs_self (Real.exp ((m : ℝ) * t) - 1)).trans hexp]
    have heq : (p + b) ^ m = p ^ m * (1 + t) ^ m := by simpa using hpow 1
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hpows.trans heU) (pow_nonneg hp.le m)
  have hlower : p ^ m * (1 - (m : ℝ) * t) ≤ (p - b) ^ m := by
    have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -t by linarith) m
    have heq : (p - b) ^ m = p ^ m * (1 - t) ^ m := by simpa [sub_eq_add_neg] using hpow (-1)
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hp.le m)
    simpa [sub_eq_add_neg] using hbern
  have hdiff : |v - p ^ m| ≤ p ^ m * (2 * (m : ℝ) * t) + (m : ℝ) * u := by
    apply abs_le.mpr
    constructor <;> nlinarith [hwindow.1, hwindow.2,
      mul_nonneg (pow_nonneg hp.le m) (mul_nonneg (by positivity) ht)]
  have hpPow : 0 < p ^ m := pow_pos hp m
  calc
    _ = |v - p ^ m| / p ^ m := by
      rw [← div_self hpPow.ne', ← sub_div, abs_div, abs_of_pos hpPow]
    _ ≤ (p ^ m * (2 * (m : ℝ) * t) + (m : ℝ) * u) / p ^ m :=
      div_le_div_of_nonneg_right hdiff hpPow.le
    _ = _ := by dsimp [t]; field_simp [hp.ne', hpPow.ne'] <;> ring

private theorem lowGeom_syndrome_flip_sub {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (v : Pos T k)
    (a : Fin (T.S.n k)) :
    G.syndrome (flipPos v a) = G.ids a - G.syndrome v := by
  classical
  let f : Fin (T.S.n k) → (Fin G.Hdim → ZMod 2) := fun j =>
    if v j = true then G.ids j else 0
  let f' : Fin (T.S.n k) → (Fin G.Hdim → ZMod 2) := fun j =>
    if flipPos v a j = true then G.ids j else 0
  have herase : (∑ j ∈ Finset.univ.erase a, f' j) =
      ∑ j ∈ Finset.univ.erase a, f j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hne : j ≠ a := (Finset.mem_erase.mp hj).1
    simp [f, f', flipPos, hne]
  have hf := Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)
  have hf' := Finset.add_sum_erase Finset.univ f' (Finset.mem_univ a)
  change (∑ j, f' j) = G.ids a - (∑ j, f j)
  rw [← hf', herase, ← hf]
  cases hv : v a
  · ext i
    simp [f, f', flipPos, hv, ZModModule.sub_eq_add]
  · ext i
    simp [f, f', flipPos, hv, ZModModule.sub_eq_add]
    rw [← add_assoc, ZModModule.add_self, zero_add]

private theorem patchOf_flip_bulk {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (G : LowGeom PT) (v : Pos T k)
    (a : Fin (T.S.n k))
    (ha : a ∈ PT.tiling.bulkCoords (G.patchOf v)) :
    G.patchOf (flipPos v a) = G.patchOf v := by
  classical
  let i := G.patchOf v
  have hv := G.patchOf_leaf v
  have hflip : flipPos v a ∈ PT.tiling.leaf i := by
    change ∀ j, j.val < (PT.tiling.P i).ℓ → flipPos v a j = PT.tiling.w i j
    intro j hj
    have ha' := Finset.mem_filter.mp ha
    have hle : (PT.tiling.P i).ℓ ≤ a.val := ha'.2.1
    have hne : j ≠ a := by
      intro he
      subst j
      omega
    have hv' : v j = PT.tiling.w i j := hv j hj
    simpa [flipPos, hne] using hv'
  obtain ⟨i', hi', huniq⟩ := hPT.tiling_valid.prefix_complete (flipPos v a)
  have h₁ : i = i' := huniq i hflip
  have h₂ : G.patchOf (flipPos v a) = i' :=
    huniq (G.patchOf (flipPos v a)) (G.patchOf_leaf _)
  exact h₂.trans h₁.symm

private theorem critical_target_even {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) : IsEvenRole X.target := by
  classical
  let b := X.failure.2.1.1
  have hbClass : D.geom.classOf b = some X.failure.1 :=
    (D.encoding.base.class_of_spec b X.failure.1).1 X.failure.2.1.2
  have hbOdd : ¬ IsEvenRole b := by
    have htest : ¬ IsEvenRole b ∧ D.geom.syndrome b ∈ D.geom.Lsub := by
      by_contra h
      simp [LowGeom.classOf, h] at hbClass
    exact htest.1
  change IsEvenRole (flipPos b X.failure.2.2.2.2)
  exact (HypercubeRamsey.S15.evenRole_flipPos b X.failure.2.2.2.2).2 hbOdd

private theorem critical_label_geometry {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) {a : Fin (T.S.n k)} (ha : a ∈ X.criticalCoords) :
    ¬ IsEvenRole (flipPos X.target a) ∧
      D.geom.patchOf (flipPos X.target a) = D.geom.patchOf X.target ∧
      D.geom.classOf (flipPos X.target a) = none := by
  classical
  have htarget := critical_target_even X
  have hodd : ¬ IsEvenRole (flipPos X.target a) := by
    intro hflip
    exact ((HypercubeRamsey.S15.evenRole_flipPos X.target a).mp hflip) htarget
  have ha' := Finset.mem_filter.mp ha
  have hbulk : a ∈ PT.tiling.bulkCoords (D.geom.patchOf X.target) := ha'.1
  have hpatch := patchOf_flip_bulk hPT D.geom X.target a hbulk
  have hnot : D.geom.ids a - D.geom.syndrome X.target ∉ D.geom.Lsub := ha'.2.1
  have hclass : D.geom.classOf (flipPos X.target a) = none := by
    unfold LowGeom.classOf
    have hs : D.geom.syndrome (flipPos X.target a) ∉ D.geom.Lsub := by
      rw [lowGeom_syndrome_flip_sub]
      exact hnot
    by_cases h : ¬ IsEvenRole (flipPos X.target a) ∧
        D.geom.syndrome (flipPos X.target a) ∈ D.geom.Lsub
    · exact (hs h.2).elim
    · simp [h]
  exact ⟨hodd, hpatch, hclass⟩

/-- Actual critical-label atom domination by the target patch's comparison
law. This supplies the individual-cell premise of pi_labels_domination. -/
theorem critical_label_atom_domination {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hD : D.Spec) {a : Fin (T.S.n k)}
    (ha : a ∈ X.criticalCoords) (y : Fin (T.S.N k)) :
    (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
      D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a) = y) ≤
        (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) * (PT.π (D.geom.patchOf X.target)).w y := by
  classical
  obtain ⟨hodd, hpatch, hclass⟩ := critical_label_geometry X ha
  simpa only [hpatch] using hD.fresh_singleton (flipPos X.target a) hodd hclass y

/-- Any selected critical labels have exactly their independent whole-cell
marginals, including the pools. -/
theorem critical_subset_event_probability {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hgeom : TransferGeometry X)
    (J : Finset (Fin (T.S.n k))) (hJ : J ⊆ X.criticalCoords)
    (H : Fin (T.S.n k) → Fin (T.S.N k) → Prop) :
    X.rawLaw.pr (fun s => ∀ a ∈ J, H a (X.criticalLabel s a)) =
      ∏ a ∈ J, (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
        H a (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a))) := by
  classical
  let cells := J.image (fun a => D.geom.cellOf (flipPos X.target a))
  let factors := fun C => if C ∈ X.criticalCells then D.typicalFresh C
    else FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)
  let event := fun (C : D.geom.Cell) (Ps : D.fresh.Pool C × D.fresh.State C) =>
    ∀ a ∈ J, D.geom.cellOf (flipPos X.target a) = C →
      H a (D.fresh.label C Ps.2 (flipPos X.target a))
  have heq : (fun s => ∀ a ∈ J, H a (X.criticalLabel s a)) =
      (fun s => ∀ C, event C (s C)) := by
    funext s
    apply propext
    constructor
    · intro h C a ha he
      have h' := h a ha
      change H a (D.fresh.label (D.geom.cellOf (flipPos X.target a))
        (s (D.geom.cellOf (flipPos X.target a))).2 (flipPos X.target a)) at h'
      subst C
      exact h'
    · intro h a ha
      exact h (D.geom.cellOf (flipPos X.target a)) a ha rfl
  rw [heq]
  change (FinLaw.pi factors).pr _ = _
  rw [pi_event factors event]
  have hout : ∀ C, C ∉ cells → (factors C).pr (event C) = 1 := by
    intro C hC
    have htrue : ∀ Ps, event C Ps := by
      intro Ps a ha he
      exact False.elim (hC (Finset.mem_image.mpr ⟨a, ha, he⟩))
    simp only [FinLaw.pr, if_pos (htrue _), (factors C).sum_one]
  rw [← Finset.prod_subset (Finset.subset_univ cells) (fun C _ hC => hout C hC)]
  rw [Finset.prod_image (fun a ha a' ha' he => hgeom.distinct_cells a (hJ ha) a' (hJ ha') he)]
  apply Finset.prod_congr rfl
  intro a ha
  have hC : D.geom.cellOf (flipPos X.target a) ∈ X.criticalCells :=
    Finset.mem_image.mpr ⟨a, hJ ha, rfl⟩
  simp only [factors, hC, ↓reduceIte]
  have hevent : event (D.geom.cellOf (flipPos X.target a)) =
      (fun Ps => H a (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2
        (flipPos X.target a))) := by
    funext Ps
    apply propext
    constructor
    · exact fun h => h a ha rfl
    · intro h a' ha' he
      have hsame := hgeom.distinct_cells a' (hJ ha') a (hJ ha) he
      subst a'
      exact h
  rw [hevent]

theorem critical_tuple_probability {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hgeom : TransferGeometry X)
    (J : Finset (Fin (T.S.n k))) (hJ : J ⊆ X.criticalCoords)
    (ys : Fin (T.S.n k) → Fin (T.S.N k)) :
    X.rawLaw.pr (fun s => ∀ a ∈ J, X.criticalLabel s a = ys a) =
      ∏ a ∈ J, (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
        D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a) = ys a) := by
  exact critical_subset_event_probability hgeom J hJ (fun a y => y = ys a)

/-- The cutoff gives the raw denominator bound for every selected block. -/
theorem critical_subset_survival_lower {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (J : Finset (Fin (T.S.n k))) (hJ : J ⊆ X.criticalCoords)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (ha : X.allowed x z) :
    (0.15 : ℝ) ^ J.card ≤ X.rawLaw.pr (fun s => ∀ a ∈ J,
      Hits (T.S.E k) PT.tiling.c x (X.criticalLabel s a) ∧
      ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y (X.criticalLabel s a)) := by
  classical
  let H := fun (_ : Fin (T.S.n k)) u => Hits (T.S.E k) PT.tiling.c x u ∧
    ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y u
  rw [critical_subset_event_probability hgeom J hJ H]
  have h := Finset.prod_le_prod₀ (s := J) (f := fun _ => (0.15 : ℝ))
    (fun _ _ => by norm_num) (fun a ha' => hsurv.1 a (hJ ha') x z ha)
  simpa only [Finset.prod_const] using h

theorem critical_tuple_domination {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hD : D.Spec) (hgeom : TransferGeometry X)
    (J : Finset (Fin (T.S.n k))) (hJ : J ⊆ X.criticalCoords)
    (ys : Fin (T.S.n k) → Fin (T.S.N k)) :
    X.rawLaw.pr (fun s => ∀ a ∈ J, X.criticalLabel s a = ys a) ≤
      (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ J.card *
        ∏ a ∈ J, (PT.π (D.geom.patchOf X.target)).w (ys a) := by
  classical
  rw [critical_tuple_probability hgeom J hJ ys]
  calc
    _ ≤ ∏ a ∈ J, (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
        (PT.π (D.geom.patchOf X.target)).w (ys a) := Finset.prod_le_prod₀
      (fun a _ => pr_nonneg _ _) (fun a ha => critical_label_atom_domination hD (hJ ha) (ys a))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

end HypercubeRamsey.S18.Lane_sol_s18_2lm.Cylinder
