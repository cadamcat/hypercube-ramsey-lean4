import HypercubeRamsey.S18.Endpoints
import HypercubeRamsey.S18.Nodes_q_s18_n6
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Data.List.Permutation
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import HypercubeRamsey.S16.Comparisons_q_s16_comp2

namespace HypercubeRamsey.S18.Lane_sol_s18_6b

open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

abbrev Outcome (D : LateData hPT) :=
  (D.encoding.InitInput × D.encoding.base.History (Fin.last D.geom.r)) × PairAssignment T k

theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (E : Ω → Prop) :
    0 ≤ P.pr E := by
  unfold FinLaw.pr
  exact Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact P.nonneg x
    · exact le_rfl

theorem pr_or_le {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (E F : Ω → Prop) :
    P.pr (fun x => E x ∨ F x) ≤ P.pr E + P.pr F := by
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf, P.nonneg x]

theorem pr_exists_mem_le {ι Ω : Type*} [Fintype Ω] [DecidableEq ι]
    (P : FinLaw Ω) (s : Finset ι) (E : ι → Ω → Prop) :
    P.pr (fun x => ∃ i ∈ s, E i x) ≤ ∑ i ∈ s, P.pr (E i) := by
  have h := S16.Lane_q_s16_comp2.pr_exists_le_sum P (fun i : s => E i.1)
  calc
    _ ≤ ∑ i : s, P.pr (E i.1) := by
      simpa only [Subtype.exists, exists_prop] using h
    _ = _ := Finset.sum_coe_sort s (fun i => P.pr (E i))

noncomputable def connectedPr (D : LateData hPT) {δ εterm εrun : ℝ}
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (S : Finset (Pos T k)) (violating : Bool) : ℝ :=
  (pairExperiment D C H).pr fun out =>
    D.full δ out.1.1 out.1.2 ∧ (endpointGraph S out.2).Connected ∧
      (violating = true → (endpointVertices S out.2).card < S.card)

theorem obstruction_union_bound (D : LateData hPT) {δ εterm εrun : ℝ}
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (t : ℕ) :
    (pairExperiment D C H).pr (fun out =>
      D.full δ out.1.1 out.1.2 ∧ HallObstruction D t out.2) ≤
    ∑ palette : PaletteIndex D,
      ((∑ S ∈ (D.paletteRows palette).powersetCard t, connectedPr D C H S false) +
        ∑ q ∈ Finset.range t, if 3 ≤ q then
          ∑ S ∈ (D.paletteRows palette).powersetCard q, connectedPr D C H S true else 0) := by
  let P := pairExperiment D C H
  let large (palette : PaletteIndex D) (out : Outcome D) :=
    ∃ S ∈ (D.paletteRows palette).powersetCard t, (endpointGraph S out.2).Connected
  let small (palette : PaletteIndex D) (out : Outcome D) :=
    ∃ q ∈ Finset.range t, 3 ≤ q ∧ ∃ S ∈ (D.paletteRows palette).powersetCard q,
      (endpointGraph S out.2).Connected ∧ (endpointVertices S out.2).card < S.card
  calc
    _ ≤ P.pr (fun out => ∃ palette,
        (D.full δ out.1.1 out.1.2 ∧ large palette out) ∨
          (D.full δ out.1.1 out.1.2 ∧ small palette out)) := by
      apply S16.Lane_q_s16_comp2.pr_mono
      intro out hout
      obtain ⟨palette, S, hsub, hconn, hsize⟩ := hout.2
      refine ⟨palette, ?_⟩
      rcases hsize with hsize | ⟨hthree, hlt, hbad⟩
      · exact Or.inl ⟨hout.1, S, Finset.mem_powersetCard.mpr ⟨hsub, hsize⟩, hconn⟩
      · exact Or.inr ⟨hout.1, S.card, Finset.mem_range.mpr hlt, hthree,
          S, Finset.mem_powersetCard.mpr ⟨hsub, rfl⟩, hconn, hbad⟩
    _ ≤ ∑ palette : PaletteIndex D, P.pr (fun out =>
        (D.full δ out.1.1 out.1.2 ∧ large palette out) ∨
          (D.full δ out.1.1 out.1.2 ∧ small palette out)) :=
      S16.Lane_q_s16_comp2.pr_exists_le_sum P _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro palette _
      apply le_trans (pr_or_le P _ _)
      apply add_le_add
      · have h := pr_exists_mem_le P ((D.paletteRows palette).powersetCard t)
          (fun S out => D.full δ out.1.1 out.1.2 ∧ (endpointGraph S out.2).Connected)
        apply le_trans ?_ (by simpa [connectedPr, P] using h)
        apply S16.Lane_q_s16_comp2.pr_mono
        intro out hout
        obtain ⟨hf, S, hS, hc⟩ := hout
        exact ⟨S, Finset.mem_powersetCard.mp hS, hf, hc⟩
      · have h := pr_exists_mem_le P (Finset.range t) (fun q out =>
          3 ≤ q ∧ D.full δ out.1.1 out.1.2 ∧
          ∃ S ∈ (D.paletteRows palette).powersetCard q,
            (endpointGraph S out.2).Connected ∧ (endpointVertices S out.2).card < S.card)
        apply le_trans ?_ (le_trans h ?_)
        · apply S16.Lane_q_s16_comp2.pr_mono
          intro out hout
          obtain ⟨hf, q, hq, hthree, S, hS, hc, hb⟩ := hout
          exact ⟨q, hq, hthree, hf, S, hS, hc, hb⟩
        · apply Finset.sum_le_sum
          intro q _
          by_cases hthree : 3 ≤ q
          · simp only [if_pos hthree]
            have h' := pr_exists_mem_le P ((D.paletteRows palette).powersetCard q)
              (fun S out => D.full δ out.1.1 out.1.2 ∧
                (endpointGraph S out.2).Connected ∧ (endpointVertices S out.2).card < S.card)
            apply le_trans ?_ (by simpa [connectedPr, P] using h')
            apply S16.Lane_q_s16_comp2.pr_mono
            intro out hout
            obtain ⟨_, hf, S, hS, hc, hb⟩ := hout
            exact ⟨S, Finset.mem_powersetCard.mp hS, hf, hc, hb⟩
          · simp [hthree, FinLaw.pr]

theorem full_supported_pairs (D : LateData hPT) {δ εterm εrun K : ℝ}
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (hPair : PairInitialFacts D δ K)
    (out : Outcome D)
    (hfull : D.full δ out.1.1 out.1.2)
    (hweight : 0 < (pairExperiment D C H).w out) :
    ∀ v, IsEvenRole v →
      (out.2 v).1 ≠ (out.2 v).2 ∧ (out.2 v).1 ∈ D.palette v ∧
        (out.2 v).2 ∈ D.palette v := by
  have hprod : 0 <
      (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
        (fun x => D.encoding.base.runFull H.samplers.act (D.encoding.initialState x))).w out.1 *
          (D.pairSampler out.1.2).w out.2 := hweight
  have hsample : 0 < (D.pairSampler out.1.2).w out.2 := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) ((D.pairSampler out.1.2).nonneg out.2)
    rw [hz, mul_zero] at hprod
    exact (lt_irrefl 0) hprod
  intro v hv
  have hfactor : 0 < (D.pairLaw out.1.2 v).w (out.2 v) := by
    have hprod' : 0 < ∏ w, (D.pairLaw out.1.2 w).w (out.2 w) := hsample
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) ((D.pairLaw out.1.2 v).nonneg (out.2 v))
    rw [Finset.prod_eq_zero (Finset.mem_univ v) hz] at hprod'
    exact (lt_irrefl 0) hprod'
  exact ⟨((hPair.2.2.2.2 out.1.1 out.1.2 hfull v hv).2 (out.2 v) hfactor).1,
    ((hPair.2.2.2.2 out.1.1 out.1.2 hfull v hv).2 (out.2 v) hfactor).2.1,
    ((hPair.2.2.2.2 out.1.1 out.1.2 hfull v hv).2 (out.2 v) hfactor).2.2.1⟩

theorem weighted_average_sum_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (h : (∑ x ∈ s, f x) / s.card ≤ 2) :
    (∑ x ∈ s, f x) ≤ 2 * s.card := by
  by_cases hs : s.Nonempty
  · exact (div_le_iff₀ (by exact_mod_cast Finset.card_pos.mpr hs)).mp h
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

theorem factorial_choose_le_pow (L q : ℕ) :
    (q.factorial : ℝ) * (L.choose q : ℝ) ≤ (L : ℝ) ^ q := by
  exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose L q ▸ Nat.descFactorial_le_pow L q)

theorem weighted_subsets_le {ι : Type*} [DecidableEq ι] (rows : Finset ι)
    (q : ℕ) (f : Finset ι → ℝ) (B K M density : ℝ)
    (hB : 0 ≤ B) (hM : 0 < M) (hdensity : 0 < density)
    (hrows : (rows.card : ℝ) ≤ K * M / density)
    (haverage : (∑ S ∈ rows.powersetCard q, f S) / (rows.powersetCard q).card ≤ 2) :
    (∑ S ∈ rows.powersetCard q, f S * (q.factorial : ℝ) * (B / M) ^ q) ≤
      2 * (B * K / density) ^ q := by
  have hcoef : 0 ≤ (B / M) ^ q := pow_nonneg (div_nonneg hB hM.le) _
  have hfac : 0 ≤ (q.factorial : ℝ) := by positivity
  have hsum := weighted_average_sum_le (rows.powersetCard q) f haverage
  have hcard : ((rows.powersetCard q).card : ℝ) = (rows.card.choose q : ℝ) := by
    rw [Finset.card_powersetCard]
  have hbase : (rows.card : ℝ) * (B / M) ≤ B * K / density := by
    calc
      _ ≤ (K * M / density) * (B / M) :=
        mul_le_mul_of_nonneg_right hrows (div_nonneg hB hM.le)
      _ = B * K / density := by field_simp
  calc
    _ = (∑ S ∈ rows.powersetCard q, f S) * (q.factorial : ℝ) * (B / M) ^ q := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ (2 * (rows.card.choose q : ℝ)) * (q.factorial : ℝ) * (B / M) ^ q := by
      apply mul_le_mul_of_nonneg_right _ hcoef
      apply mul_le_mul_of_nonneg_right _ hfac
      simpa only [hcard] using hsum
    _ ≤ 2 * (rows.card : ℝ) ^ q * (B / M) ^ q := by
      apply mul_le_mul_of_nonneg_right _ hcoef
      have h := factorial_choose_le_pow rows.card q
      nlinarith
    _ = 2 * ((rows.card : ℝ) * (B / M)) ^ q := by rw [mul_pow]; ring
    _ ≤ 2 * (B * K / density) ^ q := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hB hM.le)) hbase _

noncomputable def correction (D : LateData hPT) (Cp : ℝ) (S : Finset (Pos T k)) : ℝ :=
  Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card + Cp * S.card * D.rank S)

theorem correction_nonneg (D : LateData hPT) (Cp : ℝ) (S : Finset (Pos T k)) :
    0 ≤ correction D Cp S := (Real.exp_pos _).le

theorem paletteScale_pos (D : LateData hPT) (palette : PaletteIndex D) :
    0 < D.paletteScale palette := by
  have hM : 0 < (PT.tiling.P palette.1).M := by
    rw [← (PT.tiling.P palette.1).cardX]
    exact Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty palette.1).1
  exact div_pos (Nat.cast_pos.mpr hM) (Nat.cast_pos.mpr (D.chi_pos palette.1))

theorem stage_prefactor (D : LateData hPT) (Cs : ℝ) :
    2 * Real.exp (Cs * D.geom.r) ≤ Real.exp ((Cs + 10) * D.geom.r) := by
  have hr : (1 : ℝ) ≤ D.geom.r := by exact_mod_cast D.l16_valid.r_pos
  have hexp := Real.add_one_le_exp (10 * (D.geom.r : ℝ))
  have htwo : (2 : ℝ) ≤ Real.exp (10 * (D.geom.r : ℝ)) := by linarith
  calc
    _ ≤ Real.exp (Cs * D.geom.r) * Real.exp (10 * (D.geom.r : ℝ)) := by
      nlinarith [Real.exp_pos (Cs * D.geom.r)]
    _ = Real.exp ((Cs + 10) * D.geom.r) := by rw [← Real.exp_add]; congr 1; ring

/-- Integrate a sequence of new tree vertices, each joined to an already
assigned parent. The terminal test can retain the two remaining edges. -/
noncomputable def treeIntegral {ι α : Type*} [Fintype α]
    (kernel : ι → α → α → ℝ) (fallback : α) (test : List α → ℝ) :
    List (ι × ℕ) → List α → ℝ
  | [], labels => test labels
  | (row, parent) :: edges, labels =>
      ∑ y, kernel row (labels.getD parent fallback) y *
        treeIntegral kernel fallback test edges (y :: labels)

theorem treeIntegral_nonneg {ι α : Type*} [Fintype α]
    (kernel : ι → α → α → ℝ) (fallback : α) (test : List α → ℝ)
    (hk : ∀ i x y, 0 ≤ kernel i x y) (htest : ∀ labels, 0 ≤ test labels)
    (edges : List (ι × ℕ)) (labels : List α) :
    0 ≤ treeIntegral kernel fallback test edges labels := by
  induction edges generalizing labels with
  | nil => exact htest labels
  | cons edge edges ih =>
      exact Finset.sum_nonneg fun y _ => mul_nonneg (hk _ _ _) (ih _)

theorem treeIntegral_le {ι α : Type*} [Fintype α]
    (kernel : ι → α → α → ℝ) (fallback : α) (test : List α → ℝ)
    (s cap : ℝ) (hs : 0 ≤ s) (hcap : 0 ≤ cap)
    (hk : ∀ i x y, 0 ≤ kernel i x y)
    (hrow : ∀ i x, ∑ y, kernel i x y ≤ s)
    (htest : ∀ labels, test labels ≤ cap)
    (edges : List (ι × ℕ)) (labels : List α) :
    treeIntegral kernel fallback test edges labels ≤ cap * s ^ edges.length := by
  induction edges generalizing labels with
  | nil => simpa only [treeIntegral, List.length_nil, pow_zero, mul_one] using htest labels
  | cons edge edges ih =>
      rcases edge with ⟨row, parent⟩
      calc
        _ ≤ ∑ y, kernel row (labels.getD parent fallback) y * (cap * s ^ edges.length) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih _) (hk _ _ _)
        _ = (∑ y, kernel row (labels.getD parent fallback) y) * (cap * s ^ edges.length) := by
          rw [Finset.sum_mul]
        _ ≤ s * (cap * s ^ edges.length) :=
          mul_le_mul_of_nonneg_right (hrow _ _) (mul_nonneg hcap (pow_nonneg hs _))
        _ = cap * s ^ ((row, parent) :: edges).length := by
          simp only [List.length_cons, pow_succ]
          ring

theorem rooted_treeIntegral_le {ι α : Type*} [Fintype α] [DecidableEq α]
    (palette : Finset α) (kernel : ι → α → α → ℝ) (fallback : α)
    (test : List α → ℝ) (s cap : ℝ) (hs : 0 ≤ s) (hcap : 0 ≤ cap)
    (hk : ∀ i x y, 0 ≤ kernel i x y)
    (hrow : ∀ i x, ∑ y, kernel i x y ≤ s)
    (htest : ∀ labels, test labels ≤ cap) (edges : List (ι × ℕ)) :
    (∑ root ∈ palette, treeIntegral kernel fallback test edges [root]) ≤
      palette.card * (cap * s ^ edges.length) := by
  calc
    _ ≤ ∑ root ∈ palette, cap * s ^ edges.length :=
      Finset.sum_le_sum fun root _ => treeIntegral_le kernel fallback test s cap hs hcap
        hk hrow htest edges [root]
    _ = _ := by simp

theorem sum_tuple_bounds {ι : Type*} [DecidableEq ι] (rows : Finset ι)
    (q : ℕ) (f b : Finset ι → ℝ) (B K M density prefactor : ℝ)
    (hB : 0 ≤ B) (hM : 0 < M) (hdensity : 0 < density) (hprefactor : 0 ≤ prefactor)
    (hrows : (rows.card : ℝ) ≤ K * M / density)
    (haverage : (∑ S ∈ rows.powersetCard q, f S) / (rows.powersetCard q).card ≤ 2)
    (htuple : ∀ S ∈ rows.powersetCard q,
      b S ≤ prefactor * (f S * (q.factorial : ℝ) * (B / M) ^ q)) :
    (∑ S ∈ rows.powersetCard q, b S) ≤ prefactor * (2 * (B * K / density) ^ q) := by
  calc
    _ ≤ ∑ S ∈ rows.powersetCard q,
        prefactor * (f S * (q.factorial : ℝ) * (B / M) ^ q) :=
      Finset.sum_le_sum htuple
    _ = prefactor * ∑ S ∈ rows.powersetCard q,
        f S * (q.factorial : ℝ) * (B / M) ^ q := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_subsets_le rows q f B K M density hB hM hdensity hrows haverage) hprefactor

theorem obstruction_le_of_tuple_diagrams (D : LateData hPT) {δ εterm εrun : ℝ}
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (K Cp Cs η B : ℝ) (hK : 0 < K) (hη : 0 < η) (hB : 0 ≤ B)
    (hPair : PairInitialFacts D δ K)
    (haverage : ∀ palette : PaletteIndex D, ∀ q : ℕ, (q : ℝ) ≤ η * T.S.n k →
      (∑ S ∈ (D.paletteRows palette).powersetCard q,
        Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card + Cp * q * D.rank S)) /
          ((D.paletteRows palette).powersetCard q).card ≤ 2)
    (ht : 3 ≤ ⌊η * (T.S.n k : ℝ)⌋₊)
    (hdiagrams : ∀ palette : PaletteIndex D, ∀ S : Finset (Pos T k),
      S ⊆ D.paletteRows palette → 3 ≤ S.card → S.card ≤ ⌊η * (T.S.n k : ℝ)⌋₊ →
      connectedPr D C H S false ≤
        (Real.exp (Cs * D.geom.r) * D.paletteScale palette) *
          (correction D Cp S * (S.card.factorial : ℝ) * (B / D.paletteScale palette) ^ S.card) ∧
      connectedPr D C H S true ≤
        (Real.exp (Cs * D.geom.r) * (D.paletteScale palette)⁻¹ *
          Real.exp (0.02 * (T.S.n k : ℝ)) * (S.card : ℝ) ^ 4) *
          (correction D Cp S * (S.card.factorial : ℝ) * (B / D.paletteScale palette) ^ S.card)) :
    (pairExperiment D C H).pr (fun out =>
      D.full δ out.1.1 out.1.2 ∧ HallObstruction D ⌊η * (T.S.n k : ℝ)⌋₊ out.2) ≤
      Real.exp ((Cs + 10) * D.geom.r) * ∑ palette : PaletteIndex D,
        (D.paletteScale palette * (B * K / densityScale T k) ^ ⌊η * (T.S.n k : ℝ)⌋₊ +
          (D.paletteScale palette)⁻¹ * Real.exp (0.02 * (T.S.n k : ℝ)) *
            ∑ q ∈ Finset.range ⌊η * (T.S.n k : ℝ)⌋₊,
              if 3 ≤ q then (q : ℝ) ^ 4 * (B * K / densityScale T k) ^ q else 0) := by
  let t := ⌊η * (T.S.n k : ℝ)⌋₊
  let rate := B * K / densityScale T k
  let stage := Real.exp ((Cs + 10) * D.geom.r)
  have hdensity : 0 < densityScale T k := by
    unfold densityScale
    have hN : 0 < (T.S.N k : ℝ) := Nat.cast_pos.mpr (T.S.N_pos k)
    positivity
  have hrate : 0 ≤ rate := by dsimp [rate]; positivity
  have hfloor : (t : ℝ) ≤ η * (T.S.n k : ℝ) :=
    Nat.floor_le (mul_nonneg hη.le (Nat.cast_nonneg _))
  have havg (palette : PaletteIndex D) (q : ℕ) (hq : q ≤ t) :
      (∑ S ∈ (D.paletteRows palette).powersetCard q, correction D Cp S) /
        ((D.paletteRows palette).powersetCard q).card ≤ 2 := by
    have hqreal : (q : ℝ) ≤ η * (T.S.n k : ℝ) := (by exact_mod_cast hq : (q : ℝ) ≤ t).trans hfloor
    have hc : (∑ S ∈ (D.paletteRows palette).powersetCard q, correction D Cp S) =
        ∑ S ∈ (D.paletteRows palette).powersetCard q,
          Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card + Cp * q * D.rank S) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [correction, (Finset.mem_powersetCard.mp hS).2]
    rw [hc]
    exact haverage palette q hqreal
  have hlarge (palette : PaletteIndex D) :
      (∑ S ∈ (D.paletteRows palette).powersetCard t, connectedPr D C H S false) ≤
        stage * (D.paletteScale palette * rate ^ t) := by
    have hM := paletteScale_pos D palette
    have h := sum_tuple_bounds (D.paletteRows palette) t (correction D Cp)
      (fun S => connectedPr D C H S false) B K (D.paletteScale palette) (densityScale T k)
      (Real.exp (Cs * D.geom.r) * D.paletteScale palette) hB hM hdensity (by positivity)
      (hPair.1 palette) (havg palette t le_rfl) (by
        intro S hS
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
        simpa only [hcard] using (hdiagrams palette S hsub (hcard ▸ ht) (by omega)).1)
    calc
      _ ≤ (Real.exp (Cs * D.geom.r) * D.paletteScale palette) * (2 * rate ^ t) := h
      _ = (2 * Real.exp (Cs * D.geom.r)) * (D.paletteScale palette * rate ^ t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (stage_prefactor D Cs) (by positivity)
  have hsmall (palette : PaletteIndex D) (q : ℕ) (hq : q ∈ Finset.range t) :
      (if 3 ≤ q then ∑ S ∈ (D.paletteRows palette).powersetCard q,
        connectedPr D C H S true else 0) ≤
      stage * ((D.paletteScale palette)⁻¹ * Real.exp (0.02 * (T.S.n k : ℝ))) *
        (if 3 ≤ q then (q : ℝ) ^ 4 * rate ^ q else 0) := by
    by_cases hthree : 3 ≤ q
    · simp only [if_pos hthree]
      have hM := paletteScale_pos D palette
      have hqt : q ≤ t := (Finset.mem_range.mp hq).le
      have h := sum_tuple_bounds (D.paletteRows palette) q (correction D Cp)
        (fun S => connectedPr D C H S true) B K (D.paletteScale palette) (densityScale T k)
        (Real.exp (Cs * D.geom.r) * (D.paletteScale palette)⁻¹ *
          Real.exp (0.02 * (T.S.n k : ℝ)) * (q : ℝ) ^ 4) hB hM hdensity (by positivity)
        (hPair.1 palette) (havg palette q hqt) (by
          intro S hS
          obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
          simpa only [hcard] using (hdiagrams palette S hsub (hcard ▸ hthree) (by omega)).2)
      calc
        _ ≤ (Real.exp (Cs * D.geom.r) * (D.paletteScale palette)⁻¹ *
            Real.exp (0.02 * (T.S.n k : ℝ)) * (q : ℝ) ^ 4) * (2 * rate ^ q) := h
        _ = (2 * Real.exp (Cs * D.geom.r)) *
            ((D.paletteScale palette)⁻¹ * Real.exp (0.02 * (T.S.n k : ℝ)) *
              (q : ℝ) ^ 4 * rate ^ q) := by ring
        _ ≤ stage * ((D.paletteScale palette)⁻¹ * Real.exp (0.02 * (T.S.n k : ℝ)) *
              (q : ℝ) ^ 4 * rate ^ q) :=
          mul_le_mul_of_nonneg_right (stage_prefactor D Cs) (by positivity)
        _ = _ := by ring
    · simp [hthree]
  calc
    _ ≤ ∑ palette : PaletteIndex D,
        ((∑ S ∈ (D.paletteRows palette).powersetCard t, connectedPr D C H S false) +
          ∑ q ∈ Finset.range t, if 3 ≤ q then
            ∑ S ∈ (D.paletteRows palette).powersetCard q, connectedPr D C H S true else 0) :=
      obstruction_union_bound D C H t
    _ ≤ ∑ palette : PaletteIndex D,
        (stage * (D.paletteScale palette * rate ^ t) +
          ∑ q ∈ Finset.range t, stage * ((D.paletteScale palette)⁻¹ *
            Real.exp (0.02 * (T.S.n k : ℝ))) *
              (if 3 ≤ q then (q : ℝ) ^ 4 * rate ^ q else 0)) := by
      apply Finset.sum_le_sum
      intro palette _
      exact add_le_add (hlarge palette) (Finset.sum_le_sum (hsmall palette))
    _ = _ := by
      simp only [Finset.mul_sum, mul_add, mul_assoc, stage, rate, t]


noncomputable def planeLabels {ι : Type*} : BinaryTree ι → List ι
  | .nil => []
  | .node v l r => v :: (planeLabels l ++ planeLabels r)

noncomputable def planeValid {ι : Type*} (G : SimpleGraph ι) (root : ι) : BinaryTree ι → Prop
  | .nil => True
  | .node v l r => G.Adj root v ∧ planeValid G v l ∧ planeValid G root r

lemma planeLabels_length {ι : Type*} (tree : BinaryTree ι) :
    (planeLabels tree).length = tree.numNodes := by
  induction tree with
  | nil => rfl
  | node v l r il ir => simp [planeLabels, BinaryTree.numNodes, il, ir]

lemma plane_graft {ι : Type*} (G : SimpleGraph ι) (root leaf target : ι)
    (tree : BinaryTree ι) (hvalid : planeValid G root tree)
    (htarget : target = root ∨ target ∈ planeLabels tree)
    (hlink : G.Adj target leaf) :
    ∃ newTree : BinaryTree ι, planeValid G root newTree ∧
      (planeLabels newTree).Perm (leaf :: planeLabels tree) := by
  induction tree generalizing root target with
  | nil =>
      have heq : target = root := htarget.resolve_right (by simp [planeLabels])
      subst target
      exact ⟨.node leaf .nil .nil, ⟨hlink, trivial, trivial⟩, List.Perm.refl _⟩
  | node v left right ihl ihr =>
      rcases htarget with rfl | hm
      · exact ⟨.node leaf .nil (.node v left right), ⟨hlink, trivial, hvalid⟩,
          List.Perm.refl _⟩
      · simp only [planeLabels, List.mem_cons, List.mem_append] at hm
        rcases hm with heq | hm | hm
        · subst target
          refine ⟨.node v (.node leaf .nil left) right,
            ⟨hvalid.1, ⟨hlink, trivial, hvalid.2.1⟩, hvalid.2.2⟩, ?_⟩
          simpa [planeLabels] using (List.perm_middle (a := leaf) (l₁ := [v]) (l₂ := planeLabels left ++ planeLabels right))
        · obtain ⟨newLeft, hnew, hperm⟩ := ihl v target hvalid.2.1 (Or.inr hm) hlink
          refine ⟨.node v newLeft right, ⟨hvalid.1, hnew, hvalid.2.2⟩, ?_⟩
          exact ((hperm.append_right (planeLabels right)).cons v).trans
            (by simpa [planeLabels] using
              (List.perm_middle (a := leaf) (l₁ := [v]) (l₂ := planeLabels left ++ planeLabels right)))
        · obtain ⟨newRight, hnew, hperm⟩ := ihr root target hvalid.2.2 (Or.inr hm) hlink
          refine ⟨.node v left newRight, ⟨hvalid.1, hvalid.2.1, hnew⟩, ?_⟩
          apply ((hperm.append_left (planeLabels left)).cons v).trans
          simpa [planeLabels, List.cons_append] using
            (List.perm_middle (a := leaf) (l₁ := v :: planeLabels left) (l₂ := planeLabels right))

lemma planeLabels_map {ι υ : Type*} (f : ι → υ) (tree : BinaryTree ι) :
    planeLabels (tree.map f) = (planeLabels tree).map f := by
  induction tree with
  | nil => rfl
  | node v l r il ir => simp [BinaryTree.map, planeLabels, il, ir]

lemma planeValid_map {ι υ : Type*} (G : SimpleGraph ι) (H : SimpleGraph υ)
    (f : ι → υ) (hf : ∀ x y, G.Adj x y → H.Adj (f x) (f y))
    (root : ι) (tree : BinaryTree ι) (ht : planeValid G root tree) :
    planeValid H (f root) (tree.map f) := by
  induction tree generalizing root with
  | nil => trivial
  | node v l r il ir => exact ⟨hf _ _ ht.1, il _ ht.2.1, ir _ ht.2.2⟩

set_option backward.isDefEq.respectTransparency.types false in
private theorem plane_tree_card (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι] (G : SimpleGraph ι), Fintype.card ι = n → G.IsTree →
      ∀ root : ι, ∃ tree : BinaryTree ι, planeValid G root tree ∧
        (root :: planeLabels tree).Nodup ∧ (root :: planeLabels tree).toFinset = Finset.univ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro ι _ G hn hG root
      by_cases hsmall : Fintype.card ι ≤ 1
      · haveI : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hsmall
        refine ⟨.nil, trivial, by simp [planeLabels], ?_⟩
        ext x
        simp [planeLabels, Subsingleton.elim x root]
      · haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (lt_of_not_ge hsmall)
        obtain ⟨u, v, huv, hu, hv⟩ := hG.exists_ne_and_degree_eq_one
        have hex : ∃ leaf : ι, leaf ≠ root ∧ G.degree leaf = 1 := by
          by_cases hur : u = root
          · exact ⟨v, fun hvr => huv (hur.trans hvr.symm), hv⟩
          · exact ⟨u, hur, hu⟩
        obtain ⟨leaf, hlr, hdegree⟩ := hex
        obtain ⟨parent, hlink, hparent⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegree
        let W := {x : ι // x ≠ leaf}
        let root' : W := ⟨root, hlr.symm⟩
        have hG' : (G.induce {x | x ≠ leaf}).IsTree :=
          ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hdegree,
            hG.isAcyclic.induce _⟩
        have hc : Fintype.card W < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (p := fun x => x ≠ leaf) (x := leaf) (by simp)
        obtain ⟨tree', ht', hnodup', hcover'⟩ := ih (Fintype.card W) hc
          (G.induce {x | x ≠ leaf}) rfl hG' root'
        let tree := tree'.map Subtype.val
        have hvalid : planeValid G root tree := planeValid_map _ _ Subtype.val (fun _ _ h => h) _ _ ht'
        have hlabels : root :: planeLabels tree = (root' :: planeLabels tree').map Subtype.val := by
          simp [tree, planeLabels_map, root']
        have hnodup : (root :: planeLabels tree).Nodup := by
          rw [hlabels]
          exact hnodup'.map Subtype.val_injective
        have hcover : (root :: planeLabels tree).toFinset = Finset.univ.erase leaf := by
          rw [hlabels]
          ext x
          simp only [List.mem_toFinset, List.mem_map, Finset.mem_erase, Finset.mem_univ, and_true]
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact y.2
          · intro hne
            refine ⟨⟨x, hne⟩, ?_, rfl⟩
            have hmem := congrArg (fun F => (⟨x, hne⟩ : W) ∈ F) hcover'
            simp only [List.mem_toFinset, Finset.mem_univ] at hmem
            exact of_eq_true hmem
        have hparentmem : parent ∈ root :: planeLabels tree := by
          apply List.mem_toFinset.mp
          rw [hcover]
          simp [hlink.ne.symm]
        obtain ⟨newTree, hnew, hperm⟩ := plane_graft G root leaf parent tree hvalid
          (by simpa only [List.mem_cons] using hparentmem) hlink.symm
        have hperm' : (root :: planeLabels newTree).Perm (leaf :: root :: planeLabels tree) :=
          (hperm.cons root).trans (by
            simpa using (List.perm_middle (a := leaf) (l₁ := [root]) (l₂ := planeLabels tree)))
        refine ⟨newTree, hnew, ?_, ?_⟩
        · apply hperm'.nodup_iff.mpr
          apply List.nodup_cons.mpr
          refine ⟨?_, hnodup⟩
          intro hleaf
          have := List.mem_toFinset.mpr hleaf
          rw [hcover] at this
          exact (Finset.notMem_erase leaf Finset.univ) this
        · rw [List.toFinset_eq_of_perm _ _ hperm', List.toFinset_cons, hcover,
            Finset.insert_erase (Finset.mem_univ leaf)]

 theorem exists_plane_spanning_tree {ι : Type*} [Fintype ι] (G : SimpleGraph ι)
    (hG : G.Connected) (root : ι) :
    ∃ tree : BinaryTree ι, planeValid G root tree ∧
      (root :: planeLabels tree).Nodup ∧ (root :: planeLabels tree).toFinset = Finset.univ := by
  obtain ⟨H, hHG, hH⟩ := hG.exists_isTree_le
  obtain ⟨tree, ht, hn, hc⟩ := plane_tree_card (Fintype.card ι) H rfl hH root
  exact ⟨tree, by simpa only [BinaryTree.id_map, id_eq] using planeValid_map H G id (fun _ _ h => hHG h) root tree ht, hn, hc⟩



abbrev HostVertices (S : Finset (Pos T k)) (a : PairAssignment T k) :=
  {x : Fin (T.S.N k) // x ∈ endpointVertices S a}

noncomputable def hostFirst (S : Finset (Pos T k)) (a : PairAssignment T k)
    (v : S) : HostVertices S a :=
  ⟨(a v).1, Finset.mem_biUnion.mpr ⟨v, v.2, by simp⟩⟩

noncomputable def hostSecond (S : Finset (Pos T k)) (a : PairAssignment T k)
    (v : S) : HostVertices S a :=
  ⟨(a v).2, Finset.mem_biUnion.mpr ⟨v, v.2, by simp⟩⟩

noncomputable def hostGraph (S : Finset (Pos T k)) (a : PairAssignment T k) :
    SimpleGraph (HostVertices S a) where
  Adj x y := x ≠ y ∧ ∃ v : S,
    (x.1 = (a v).1 ∧ y.1 = (a v).2) ∨ (x.1 = (a v).2 ∧ y.1 = (a v).1)
  symm := by
    constructor
    rintro x y ⟨hne, v, hv⟩
    refine ⟨hne.symm, v, ?_⟩
    rcases hv with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inr ⟨hy, hx⟩
    · exact Or.inl ⟨hy, hx⟩
  loopless := by constructor; intro v h; exact h.1 rfl

lemma hostRow_reachable (S : Finset (Pos T k)) (a : PairAssignment T k) (v : S) :
    (hostGraph S a).Reachable (hostFirst S a v) (hostSecond S a v) := by
  by_cases heq : hostFirst S a v = hostSecond S a v
  · rw [heq]
  · exact (show (hostGraph S a).Adj (hostFirst S a v) (hostSecond S a v) from
      ⟨heq, v, Or.inl ⟨rfl, rfl⟩⟩).reachable

lemma host_adj_rows_reachable (S : Finset (Pos T k)) (a : PairAssignment T k)
    (v w : S) (hadj : (endpointGraph S a).Adj v w) :
    (hostGraph S a).Reachable (hostFirst S a v) (hostFirst S a w) := by
  rcases hadj.2 with h | h | h | h
  · have heq : hostFirst S a v = hostFirst S a w := Subtype.ext h
    rw [heq]
  · have heq : hostFirst S a v = hostSecond S a w := Subtype.ext h
    rw [heq]
    exact (hostRow_reachable S a w).symm
  · have heq : hostSecond S a v = hostFirst S a w := Subtype.ext h
    rw [← heq]
    exact hostRow_reachable S a v
  · have heq : hostSecond S a v = hostSecond S a w := Subtype.ext h
    have hw := (hostRow_reachable S a w).symm
    rw [← heq] at hw
    exact (hostRow_reachable S a v).trans hw

lemma host_rows_reachable (S : Finset (Pos T k)) (a : PairAssignment T k)
    {v w : S} (h : (endpointGraph S a).Reachable v w) :
    (hostGraph S a).Reachable (hostFirst S a v) (hostFirst S a w) := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj walk ih => exact (host_adj_rows_reachable S a _ _ hadj).trans ih

lemma host_member_reachable (S : Finset (Pos T k)) (a : PairAssignment T k)
    (x : HostVertices S a) :
    ∃ v : S, (hostGraph S a).Reachable (hostFirst S a v) x := by
  obtain ⟨v, hv, hx⟩ := Finset.mem_biUnion.mp x.2
  let v' : S := ⟨v, hv⟩
  refine ⟨v', ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx
  · have heq : x = hostFirst S a v' := Subtype.ext hx
    rw [heq]
  · have heq : x = hostSecond S a v' := Subtype.ext hx
    rw [heq]
    exact hostRow_reachable S a v'

 theorem hostGraph_connected (S : Finset (Pos T k)) (a : PairAssignment T k)
    (hc : (endpointGraph S a).Connected) : (hostGraph S a).Connected := by
  obtain ⟨v⟩ := hc.nonempty
  haveI : Nonempty (HostVertices S a) := ⟨hostFirst S a v⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨v, hv⟩ := host_member_reachable S a x
  obtain ⟨w, hw⟩ := host_member_reachable S a y
  exact hv.symm.trans ((host_rows_reachable S a (hc.preconnected v w)).trans hw)

lemma hostGraph_edges_le (S : Finset (Pos T k)) (a : PairAssignment T k) :
    (hostGraph S a).edgeFinset.card ≤ S.card := by
  let edge (v : S) : Sym2 (HostVertices S a) := s(hostFirst S a v, hostSecond S a v)
  have hsub : (hostGraph S a).edgeFinset ⊆ Finset.univ.image edge := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have h : (hostGraph S a).Adj x y := by simpa using he
      obtain ⟨hne, v, hv⟩ := h
      refine Finset.mem_image.mpr ⟨v, Finset.mem_univ _, ?_⟩
      rcases hv with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hx' : x = hostFirst S a v := Subtype.ext hx
        have hy' : y = hostSecond S a v := Subtype.ext hy
        rw [hx', hy']
      · have hx' : x = hostSecond S a v := Subtype.ext hx
        have hy' : y = hostFirst S a v := Subtype.ext hy
        rw [hx', hy']
        exact Sym2.eq_swap
  calc
    _ ≤ (Finset.univ.image edge).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset S).card := Finset.card_image_le
    _ = S.card := by simp

 theorem connected_vertices_le (S : Finset (Pos T k)) (a : PairAssignment T k)
    (hc : (endpointGraph S a).Connected) :
    (endpointVertices S a).card ≤ S.card + 1 := by
  have h := (hostGraph_connected S a hc).card_vert_le_card_edgeSet_add_one
  have h' : (endpointVertices S a).card ≤ (hostGraph S a).edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, ← SimpleGraph.edgeFinset_card] using h
  exact h'.trans (Nat.add_le_add_right (hostGraph_edges_le S a) 1)



section KernelTrees
attribute [local instance] Classical.decEq Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

@[reducible] def NodePos : BinaryTree Unit → Type
  | .nil => Empty
  | .node _ left right => Unit ⊕ (NodePos left ⊕ NodePos right)

@[reducible] noncomputable def nodePosFintype : (shape : BinaryTree Unit) → Fintype (NodePos shape)
  | .nil => inferInstanceAs (Fintype Empty)
  | .node _ left right => by
      letI := nodePosFintype left
      letI := nodePosFintype right
      exact inferInstanceAs (Fintype (Unit ⊕ (NodePos left ⊕ NodePos right)))
attribute [instance] nodePosFintype

lemma nodePos_card (shape : BinaryTree Unit) : Fintype.card (NodePos shape) = shape.numNodes := by
  induction shape with
  | nil => rfl
  | node v l r il ir => simp [NodePos, Fintype.card_sum, il, ir, BinaryTree.numNodes] <;> omega

def parent : (shape : BinaryTree Unit) → NodePos shape → Option (NodePos shape)
  | .nil, i => Empty.elim i
  | .node _ l r, .inl _ => none
  | .node _ l r, .inr (.inl i) =>
      (parent l i).elim (some (.inl ())) (fun j => some (.inr (.inl j)))
  | .node _ l r, .inr (.inr i) =>
      (parent r i).map (fun j => .inr (.inr j))

def vertexValue {shape : BinaryTree Unit} {α : Type*} (root : α) (f : NodePos shape → α) :
    Option (NodePos shape) → α := fun i => i.elim root f

noncomputable def kernelWeight {α : Type*} (shape : BinaryTree Unit)
    (kernel : NodePos shape → α → α → ℝ) (root : α) (f : NodePos shape → α) : ℝ :=
  ∏ i, kernel i (vertexValue root f (parent shape i)) (f i)

lemma vertexValue_left {α : Type*} (l r : BinaryTree Unit) (root : α)
    (f : NodePos (.node () l r) → α) (i : NodePos l) :
    vertexValue root f (parent (.node () l r) (.inr (.inl i))) =
      vertexValue (f (.inl ())) (fun j => f (.inr (.inl j))) (parent l i) := by
  cases h : parent l i <;> simp [parent, vertexValue, h]

lemma vertexValue_right {α : Type*} (l r : BinaryTree Unit) (root : α)
    (f : NodePos (.node () l r) → α) (i : NodePos r) :
    vertexValue root f (parent (.node () l r) (.inr (.inr i))) =
      vertexValue root (fun j => f (.inr (.inr j))) (parent r i) := by
  cases h : parent r i <;> simp [parent, vertexValue, h]

lemma kernelWeight_node {α : Type*} (l r : BinaryTree Unit)
    (kernel : NodePos (.node () l r) → α → α → ℝ) (root : α)
    (f : NodePos (.node () l r) → α) :
    kernelWeight (.node () l r) kernel root f =
      kernel (.inl ()) root (f (.inl ())) *
        kernelWeight l (fun i => kernel (.inr (.inl i))) (f (.inl ()))
          (fun i => f (.inr (.inl i))) *
        kernelWeight r (fun i => kernel (.inr (.inr i))) root
          (fun i => f (.inr (.inr i))) := by
  unfold kernelWeight
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Fintype.prod_unique, parent, vertexValue, Option.elim_none]
  rw [mul_assoc]
  congr 1
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun x => kernel (.inr (.inl i)) x (f (.inr (.inl i))))
      (vertexValue_left l r root f i)
  · apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun x => kernel (.inr (.inr i)) x (f (.inr (.inr i))))
      (vertexValue_right l r root f i)

noncomputable def nodeAssignmentEquiv {α : Type*} (l r : BinaryTree Unit) :
    (NodePos (.node () l r) → α) ≃ α × ((NodePos l → α) × (NodePos r → α)) where
  toFun f := ⟨f (.inl ()), (fun i => f (.inr (.inl i))), (fun i => f (.inr (.inr i)))⟩
  invFun z := Sum.elim (fun _ => z.1) (Sum.elim z.2.1 z.2.2)
  left_inv f := by
    funext i
    rcases i with u | (i | i)
    · cases u; rfl
    · rfl
    · rfl
  right_inv z := rfl

lemma kernelWeight_nonneg {α : Type*} (shape : BinaryTree Unit)
    (kernel : NodePos shape → α → α → ℝ) (root : α) (f : NodePos shape → α)
    (hk : ∀ i x y, 0 ≤ kernel i x y) : 0 ≤ kernelWeight shape kernel root f :=
  Finset.prod_nonneg fun i _ => hk _ _ _

lemma kernelWeight_sum_node {α : Type*} [Fintype α] (l r : BinaryTree Unit)
    (kernel : NodePos (.node () l r) → α → α → ℝ) (root : α) :
    (∑ f, kernelWeight (.node () l r) kernel root f) =
      ∑ y, kernel (.inl ()) root y *
        (∑ fl, kernelWeight l (fun i => kernel (.inr (.inl i))) y fl) *
        (∑ fr, kernelWeight r (fun i => kernel (.inr (.inr i))) root fr) := by
  rw [← (nodeAssignmentEquiv l r).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Fintype.sum_prod_type]
  simp only [kernelWeight_node]
  change (∑ fl, ∑ fr, kernel (.inl ()) root y *
    kernelWeight l (fun i => kernel (.inr (.inl i))) y fl *
    kernelWeight r (fun i => kernel (.inr (.inr i))) root fr) = _
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  congr 1
  exact (Finset.mul_sum _ _ _).symm

 theorem kernelWeight_sum_le {α : Type*} [Fintype α] (shape : BinaryTree Unit)
    (kernel : NodePos shape → α → α → ℝ) (root : α) (s : ℝ) (hs : 0 ≤ s)
    (hk : ∀ i x y, 0 ≤ kernel i x y) (hrow : ∀ i x, ∑ y, kernel i x y ≤ s) :
    (∑ f, kernelWeight shape kernel root f) ≤ s ^ shape.numNodes := by
  induction shape generalizing root with
  | nil => simp [kernelWeight, NodePos, BinaryTree.numNodes]
  | node u l r il ir =>
      cases u
      refine Eq.trans_le ?_ ((kernelWeight_sum_node l r kernel root).trans_le ?_)
      · apply Finset.sum_congr
        · ext f; simp
        · intro f _; rfl
      have hl (y : α) := il (fun i => kernel (.inr (.inl i))) y
        (fun i x y => hk _ _ _) (fun i x => hrow _ _)
      have hr := ir (fun i => kernel (.inr (.inr i))) root
        (fun i x y => hk _ _ _) (fun i x => hrow _ _)
      calc
        _ ≤ ∑ y, kernel (.inl ()) root y * s ^ l.numNodes * s ^ r.numNodes := by
          apply Finset.sum_le_sum
          intro y _
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (hl y) (hk _ _ _)
          · exact hr
          · exact Finset.sum_nonneg fun f _ => kernelWeight_nonneg _ _ _ _ (fun i x y => hk _ _ _)
          · exact mul_nonneg (hk _ _ _) (pow_nonneg hs _)
        _ = (∑ y, kernel (.inl ()) root y) * s ^ l.numNodes * s ^ r.numNodes := by
          rw [Finset.sum_mul, Finset.sum_mul]
        _ ≤ s * s ^ l.numNodes * s ^ r.numNodes := by
          gcongr
          exact hrow _ _
        _ = s ^ (BinaryTree.node () l r).numNodes := by
          simp only [BinaryTree.numNodes]
          rw [pow_add, pow_add, pow_one]
          ring


end KernelTrees


abbrev RowAssignment (S : Finset (Pos T k)) := S → Fin (T.S.N k) × Fin (T.S.N k)

noncomputable def extendRowAssignment (D : LateData hPT) (S : Finset (Pos T k))
    (a : RowAssignment S) : PairAssignment T k := fun v =>
  if hv : v ∈ S then a ⟨v, hv⟩ else (D.fallback, D.fallback)

lemma endpointGraph_congr (S : Finset (Pos T k)) (a b : PairAssignment T k)
    (h : ∀ v ∈ S, a v = b v) : endpointGraph S a = endpointGraph S b := by
  ext v w
  change (v ≠ w ∧ ((a v).1 = (a w).1 ∨ (a v).1 = (a w).2 ∨
    (a v).2 = (a w).1 ∨ (a v).2 = (a w).2)) ↔ _
  rw [h v v.2, h w w.2]
  rfl

lemma endpointVertices_congr (S : Finset (Pos T k)) (a b : PairAssignment T k)
    (h : ∀ v ∈ S, a v = b v) : endpointVertices S a = endpointVertices S b := by
  unfold endpointVertices
  apply Finset.biUnion_congr rfl
  intro v hv
  rw [h v hv]

lemma palette_of_mem (D : LateData hPT) (palette : PaletteIndex D) (v : Pos T k)
    (hv : v ∈ D.paletteRows palette) : D.palette v = D.palettes palette.1 palette.2 := by
  have h := (Finset.mem_filter.mp hv).2.2
  exact congrArg (fun p : PaletteIndex D => D.palettes p.1 p.2) h

lemma pr_weight_pos {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (E : Ω → Prop) :
    P.pr E = P.pr (fun x => E x ∧ 0 < P.w x) := by
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : E x
  · by_cases hp : 0 < P.w x
    · simp [he, hp]
    · have hz := le_antisymm (le_of_not_gt hp) (P.nonneg x)
      simp [he, hp, hz]
  · simp [he]

noncomputable def rowPredicate (D : LateData hPT) (palette : PaletteIndex D)
    (S : Finset (Pos T k)) (violating : Bool) (a : RowAssignment S) : Prop :=
  (∀ v : S, (a v).1 ≠ (a v).2 ∧ (a v).1 ∈ D.palettes palette.1 palette.2 ∧
    (a v).2 ∈ D.palettes palette.1 palette.2) ∧
    (endpointGraph S (extendRowAssignment D S a)).Connected ∧
      (violating = true → (endpointVertices S (extendRowAssignment D S a)).card < S.card)

noncomputable def kernelSum (D : LateData hPT) (palette : PaletteIndex D)
    (S : Finset (Pos T k)) (violating : Bool)
    (kernel : Pos T k → Fin (T.S.N k) → Fin (T.S.N k) → ℝ) : ℝ :=
  ∑ a : RowAssignment S, if rowPredicate D palette S violating a then
    ∏ v : S, kernel v (a v).1 (a v).2 else 0

 theorem connectedPr_le_kernelSum (D : LateData hPT) {δ εterm εrun K : ℝ}
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (hPair : PairInitialFacts D δ K) (A : InitialPairData D) (violating : Bool)
    (kernel : Pos T k → Fin (T.S.N k) → Fin (T.S.N k) → ℝ) (F : ℝ)
    (hjoint : ∀ assignment, endpointProbability D C H A assignment ≤
      F * ∏ v ∈ A.rows, kernel v (assignment v).1 (assignment v).2) :
    connectedPr D C H A.rows violating ≤ F * kernelSum D A.paletteIndex A.rows violating kernel := by
  let P := pairExperiment D C H
  let E (out : Outcome D) := D.full δ out.1.1 out.1.2 ∧
    (endpointGraph A.rows out.2).Connected ∧
      (violating = true → (endpointVertices A.rows out.2).card < A.rows.card)
  let pred := rowPredicate D A.paletteIndex A.rows violating
  let rowEvent (a : RowAssignment A.rows) (out : Outcome D) :=
    pred a ∧ D.full δ out.1.1 out.1.2 ∧ ∀ v ∈ A.rows,
      out.2 v = extendRowAssignment D A.rows a v
  change P.pr E ≤ F * ∑ a : RowAssignment A.rows,
    if pred a then ∏ v : A.rows, kernel v (a v).1 (a v).2 else 0
  calc
    _ = P.pr (fun out => E out ∧ 0 < P.w out) := pr_weight_pos P E
    _ ≤ P.pr (fun out => ∃ a : RowAssignment A.rows, rowEvent a out) := by
      apply S16.Lane_q_s16_comp2.pr_mono
      intro out hout
      let a : RowAssignment A.rows := fun v => out.2 v
      have heq : ∀ v ∈ A.rows, extendRowAssignment D A.rows a v = out.2 v := by
        intro v hv
        simp only [extendRowAssignment, dif_pos hv, a]
      refine ⟨a, ⟨?_, hout.1.1, fun v hv => (heq v hv).symm⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · intro v
        have hvp := A.rows_subset v.2
        have heven := (Finset.mem_filter.mp hvp).2.1
        have hs := full_supported_pairs D C H hPair out hout.1.1 hout.2 v heven
        change (out.2 v).1 ≠ (out.2 v).2 ∧ _
        rw [← palette_of_mem D A.paletteIndex v hvp]
        exact hs
      · rw [endpointGraph_congr A.rows _ _ heq]
        exact hout.1.2.1
      · intro hv
        rw [endpointVertices_congr A.rows _ _ heq]
        exact hout.1.2.2 hv
    _ ≤ ∑ a : RowAssignment A.rows, P.pr (rowEvent a) :=
      S16.Lane_q_s16_comp2.pr_exists_le_sum P rowEvent
    _ ≤ ∑ a : RowAssignment A.rows, if pred a then
        F * ∏ v : A.rows, kernel v (a v).1 (a v).2 else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : pred a
      · have hprod : (∏ v ∈ A.rows, kernel v (extendRowAssignment D A.rows a v).1
            (extendRowAssignment D A.rows a v).2) =
          ∏ v : A.rows, kernel v (a v).1 (a v).2 := by
          rw [← Finset.prod_coe_sort]
          apply Finset.prod_congr rfl
          intro v _
          simp only [extendRowAssignment, dif_pos v.2]
        have h := hjoint (extendRowAssignment D A.rows a)
        rw [hprod] at h
        simpa [rowEvent, ha, endpointProbability, P] using h
      · simp [rowEvent, ha, FinLaw.pr]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp


 theorem eventually_chordRate_le_one {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, ∀ δ : ℝ, PairInitialFacts D δ K →
        ∀ palette : PaletteIndex D, ∀ p : ℕ, p ≤ T.S.n k →
          4 * (p : ℝ) ^ 2 * Real.exp (0.01 * (T.S.n k : ℝ)) /
            ((K + 1) * D.paletteScale palette) ≤ 1 := by
  have hr := HypercubeRamsey.Lane_q_s18_n6.eventually_overlapRate_le_half hκ T
    (1 / 2) 0.02 (by norm_num) (by nlinarith [Real.log_two_gt_d9])
  have hd : Filter.Tendsto (fun k => densityScale T k) Filter.atTop Filter.atTop := by
    simpa [densityScale] using T.S.ratio_tendsto
  filter_upwards [hr, hd.eventually_ge_atTop 1, T.S.n_tendsto.eventually_ge_atTop 2]
    with k hr hd hn
  intro PT hPT D δ hPair palette p hp
  let n : ℝ := T.S.n k
  let U := D.paletteRows palette
  let Δ : ℕ := ⌈n ^ ((κ.Ac : ℝ) + 5)⌉₊
  have hn2 : (2 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn1 : 1 ≤ n := by linarith
  have hn0 : 0 ≤ n := by positivity
  have hM := paletteScale_pos D palette
  have hU : 0 < (U.card : ℝ) := lt_of_lt_of_le
    (Real.rpow_pos_of_pos (by norm_num) _) (hPair.2.1 palette)
  have hden : (U.card : ℝ) ≤ (K + 1) * D.paletteScale palette := by
    have hdpos : 0 < densityScale T k := lt_of_lt_of_le (by norm_num) hd
    have hmul := (le_div_iff₀ hdpos).mp (hPair.1 palette)
    have hUdens : (U.card : ℝ) ≤ (U.card : ℝ) * densityScale T k :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) hd
    nlinarith
  have hrate : Real.exp (0.02 * n) * (Δ : ℝ) / (U.card : ℝ) ≤ 1 / 2 := by
    have h := hr U (hPair.2.1 palette) 1 (by
      have h : (1 : ℝ) ≤ (1 / 2) * n := by nlinarith
      simpa only [n, Nat.cast_one] using h)
    simpa [n, Δ] using h
  have hΔ : n ^ 5 ≤ (Δ : ℝ) := by
    have hexp := Real.rpow_le_rpow_of_exponent_le hn1
      (show (5 : ℝ) ≤ (κ.Ac : ℝ) + 5 by
        have h : 0 ≤ (κ.Ac : ℝ) := by positivity
        linarith)
    calc
      n ^ 5 = n ^ (5 : ℝ) := by norm_cast
      _ ≤ n ^ ((κ.Ac : ℝ) + 5) := hexp
      _ ≤ (Δ : ℝ) := Nat.le_ceil _
  have h3 : (4 : ℝ) ≤ n ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 3
    norm_num at h
    linarith
  have h4 : 4 * (p : ℝ) ^ 2 ≤ (Δ : ℝ) := by
    have hpR : (p : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hp
    have hp2 := pow_le_pow_left₀ (Nat.cast_nonneg p) hpR 2
    have h5 : 4 * n ^ 2 ≤ n ^ 5 := by
      have h := mul_le_mul_of_nonneg_right h3 (pow_nonneg hn0 2)
      nlinarith
    nlinarith
  have hnum : 4 * (p : ℝ) ^ 2 * Real.exp (0.01 * n) ≤
      Real.exp (0.02 * n) * (Δ : ℝ) := by
    have he := Real.exp_le_exp.mpr (show 0.01 * n ≤ 0.02 * n by nlinarith)
    have h := mul_le_mul h4 he (Real.exp_pos _).le (Nat.cast_nonneg Δ)
    nlinarith
  calc
    _ ≤ (4 * (p : ℝ) ^ 2 * Real.exp (0.01 * n)) / (U.card : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hU hden
    _ ≤ Real.exp (0.02 * n) * (Δ : ℝ) / (U.card : ℝ) :=
      div_le_div_of_nonneg_right hnum hU.le
    _ ≤ 1 / 2 := hrate
    _ ≤ 1 := by norm_num


section EncodingTrees
attribute [local instance] Classical.decEq Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
def treeShape {α : Type*} : BinaryTree α → BinaryTree Unit
  | .nil => .nil
  | .node _ l r => .node () (treeShape l) (treeShape r)

def nodeLabel {α : Type*} : (tree : BinaryTree α) → NodePos (treeShape tree) → α
  | .nil, i => Empty.elim i
  | .node v _ _, .inl _ => v
  | .node _ l _, .inr (.inl i) => nodeLabel l i
  | .node _ _ r, .inr (.inr i) => nodeLabel r i

lemma nodeLabel_mem {α : Type*} (tree : BinaryTree α) (i : NodePos (treeShape tree)) :
    nodeLabel tree i ∈ planeLabels tree := by
  induction tree with
  | nil => exact Empty.elim i
  | node v l r il ir =>
      rcases i with u | (i | i)
      · simp [nodeLabel, planeLabels]
      · exact List.mem_cons_of_mem v (List.mem_append_left _ (il i))
      · exact List.mem_cons_of_mem v (List.mem_append_right _ (ir i))

lemma nodeLabel_injective {α : Type*} (tree : BinaryTree α)
    (hn : (planeLabels tree).Nodup) : Function.Injective (nodeLabel tree) := by
  induction tree with
  | nil => intro i; exact Empty.elim i
  | node v l r il ir =>
      obtain ⟨hv, hrest⟩ := List.nodup_cons.mp hn
      obtain ⟨hl, hr, hd⟩ := List.nodup_append.mp hrest
      intro i j hij
      rcases i with u | (i | i) <;> rcases j with w | (j | j)
      · cases u; cases w; rfl
      · have hj := nodeLabel_mem l j
        have hEq : v = nodeLabel l j := hij
        exact False.elim (hv (List.mem_append_left _ (hEq ▸ hj)))
      · have hj := nodeLabel_mem r j
        have hEq : v = nodeLabel r j := hij
        exact False.elim (hv (List.mem_append_right _ (hEq ▸ hj)))
      · have hi := nodeLabel_mem l i
        have hEq : nodeLabel l i = v := hij
        exact False.elim (hv (List.mem_append_left _ (hEq ▸ hi)))
      · have heq : i = j := il hl hij
        subst j; rfl
      · have hi := nodeLabel_mem l i
        have hj := nodeLabel_mem r j
        have hEq : nodeLabel l i = nodeLabel r j := hij
        exact False.elim (hd _ hi _ hj hEq)
      · have hi := nodeLabel_mem r i
        have hEq : nodeLabel r i = v := hij
        exact False.elim (hv (List.mem_append_right _ (hEq ▸ hi)))
      · have hi := nodeLabel_mem r i
        have hj := nodeLabel_mem l j
        have hEq : nodeLabel r i = nodeLabel l j := hij
        exact False.elim (hd _ hj _ hi hEq.symm)
      · have heq : i = j := ir hr hij
        subst j; rfl

def vertexLabels {α : Type*} (root : α) (tree : BinaryTree α) :
    Option (NodePos (treeShape tree)) → α := fun i => i.elim root (nodeLabel tree)

lemma vertexLabels_injective {α : Type*} (root : α) (tree : BinaryTree α)
    (hn : (root :: planeLabels tree).Nodup) : Function.Injective (vertexLabels root tree) := by
  obtain ⟨hroot, hnodes⟩ := List.nodup_cons.mp hn
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j =>
          have hEq : root = nodeLabel tree j := hij
          exact False.elim (hroot (hEq ▸ nodeLabel_mem tree j))
  | some i =>
      cases j with
      | none =>
          have hEq : nodeLabel tree i = root := hij
          exact False.elim (hroot (hEq ▸ nodeLabel_mem tree i))
      | some j => exact congrArg some (nodeLabel_injective tree hnodes hij)

def nodeDepth : (shape : BinaryTree Unit) → NodePos shape → ℕ
  | .nil, i => Empty.elim i
  | .node _ _ _, .inl _ => 1
  | .node _ l _, .inr (.inl i) => nodeDepth l i + 1
  | .node _ _ r, .inr (.inr i) => nodeDepth r i

def depthValue {shape : BinaryTree Unit} : Option (NodePos shape) → ℕ :=
  fun i => i.elim 0 (nodeDepth shape)

lemma nodeDepth_pos (shape : BinaryTree Unit) (i : NodePos shape) : 0 < nodeDepth shape i := by
  induction shape with
  | nil => exact Empty.elim i
  | node v l r il ir =>
      rcases i with u | (i | i)
      · exact Nat.zero_lt_one
      · exact Nat.succ_pos _
      · exact ir i

lemma parent_depth_lt (shape : BinaryTree Unit) (i : NodePos shape) :
    depthValue (parent shape i) < nodeDepth shape i := by
  induction shape with
  | nil => exact Empty.elim i
  | node v l r il ir =>
      rcases i with u | (i | i)
      · exact Nat.zero_lt_one
      · have h := il i
        have hp := nodeDepth_pos l i
        cases he : parent l i <;> simp [parent, depthValue, nodeDepth, he] at * <;> omega
      · have h := ir i
        cases he : parent r i <;> simp [parent, depthValue, nodeDepth, he] at * <;> omega


lemma treeShape_numNodes {α : Type*} (tree : BinaryTree α) :
    (treeShape tree).numNodes = tree.numNodes := by
  induction tree <;> simp [treeShape, BinaryTree.numNodes, *]

noncomputable def labelledEdge {α : Type*} (root : α) (tree : BinaryTree α)
    (i : NodePos (treeShape tree)) : Sym2 α :=
  s(vertexLabels root tree (parent (treeShape tree) i), nodeLabel tree i)

lemma labelledEdge_injective {α : Type*} (root : α) (tree : BinaryTree α)
    (hn : (root :: planeLabels tree).Nodup) : Function.Injective (labelledEdge root tree) := by
  have hv := vertexLabels_injective root tree hn
  intro i j hij
  rcases Sym2.eq_iff.mp hij with ⟨hparent, hchild⟩ | ⟨hcross₁, hcross₂⟩
  · have heq : some i = some j := hv hchild
    exact Option.some.inj heq
  · have h₁ : parent (treeShape tree) i = some j := hv hcross₁
    have h₂ : some i = parent (treeShape tree) j := hv hcross₂
    have hD₁ := parent_depth_lt (treeShape tree) i
    have hD₂ := parent_depth_lt (treeShape tree) j
    have heq₁ := congrArg (depthValue (shape := treeShape tree)) h₁
    have heq₂ := congrArg (depthValue (shape := treeShape tree)) h₂
    simp only [depthValue, Option.elim_some] at heq₁ heq₂ hD₁ hD₂
    omega


lemma exists_nodeLabel {α : Type*} (tree : BinaryTree α) (x : α)
    (hx : x ∈ planeLabels tree) : ∃ i, nodeLabel tree i = x := by
  induction tree with
  | nil => simp [planeLabels] at hx
  | node v l r il ir =>
      simp only [planeLabels, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact ⟨.inl (), rfl⟩
      · obtain ⟨i, hi⟩ := il hx
        exact ⟨.inr (.inl i), hi⟩
      · obtain ⟨i, hi⟩ := ir hx
        exact ⟨.inr (.inr i), hi⟩

lemma vertexLabels_surjective {α : Type*} [Fintype α] (root : α) (tree : BinaryTree α)
    (hcover : (root :: planeLabels tree).toFinset = Finset.univ) :
    Function.Surjective (vertexLabels root tree) := by
  intro x
  have hmem := congrArg (fun F => x ∈ F) hcover
  simp only [List.mem_toFinset, Finset.mem_univ] at hmem
  have hx := of_eq_true hmem
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨none, rfl⟩
  · obtain ⟨i, hi⟩ := exists_nodeLabel tree x hx
    exact ⟨some i, hi⟩

lemma parent_node_adj {α : Type*} (G : SimpleGraph α) (root : α) (tree : BinaryTree α)
    (hv : planeValid G root tree) : ∀ i : NodePos (treeShape tree),
      G.Adj (vertexLabels root tree (parent (treeShape tree) i)) (nodeLabel tree i) := by
  induction tree generalizing root with
  | nil => intro i; exact Empty.elim i
  | node v l r il ir =>
      intro i
      rcases i with u | (i | i)
      · exact hv.1
      · have h := il v hv.2.1 i
        cases he : parent (treeShape l) i <;>
          simpa [treeShape, parent, vertexLabels, nodeLabel, he] using h
      · have h := ir root hv.2.2 i
        cases he : parent (treeShape r) i <;>
          simpa [treeShape, parent, vertexLabels, nodeLabel, he] using h

 theorem exists_tree_row_embedding {α Row : Type*} (G : SimpleGraph α)
    (pairs : Row → α × α)
    (hw : ∀ x y, G.Adj x y → ∃ row, s(x, y) = s((pairs row).1, (pairs row).2))
    (root : α) (tree : BinaryTree α) (hv : planeValid G root tree)
    (hn : (root :: planeLabels tree).Nodup) :
    ∃ e : NodePos (treeShape tree) ↪ Row,
      ∀ i, labelledEdge root tree i = s((pairs (e i)).1, (pairs (e i)).2) := by
  let row : NodePos (treeShape tree) → Row := fun i =>
    Classical.choose (hw _ _ (parent_node_adj G root tree hv i))
  have hrep (i : NodePos (treeShape tree)) :
      labelledEdge root tree i = s((pairs (row i)).1, (pairs (row i)).2) :=
    Classical.choose_spec (hw _ _ (parent_node_adj G root tree hv i))
  have hinj : Function.Injective row := by
    intro i j hij
    apply labelledEdge_injective root tree hn
    rw [hrep i, hrep j, hij]
  exact ⟨⟨row, hinj⟩, hrep⟩


end EncodingTrees


section DiagramCounts

abbrev ExtraRows {Row : Type*} {q : ℕ} (e : Fin (q - 1) ↪ Row) :=
  {r : Row // r ∉ Set.range e}

abbrev EndpointDiagram (Row : Type*) (q : ℕ) :=
  (BinaryTree.treesOfNumNodesEq (q - 1)) ×
    Σ e : Fin (q - 1) ↪ Row,
      (Fin (q - 1) → Bool) × (ExtraRows e → Fin q × Fin q)

lemma extraRows_card {Row : Type*} [Fintype Row] {q : ℕ} (e : Fin (q - 1) ↪ Row) :
    Fintype.card (ExtraRows e) = Fintype.card Row - (q - 1) := by
  change Fintype.card ↥((Set.range e)ᶜ : Set Row) = _
  rw [Fintype.card_compl_set, Fintype.card_range, Fintype.card_fin]

 theorem endpointDiagram_card {Row : Type*} [Fintype Row] (q : ℕ) :
    Fintype.card (EndpointDiagram Row q) =
      catalan (q - 1) * (Fintype.card Row).descFactorial (q - 1) * 2 ^ (q - 1) *
        (q * q) ^ (Fintype.card Row - (q - 1)) := by
  rw [Fintype.card_prod, Fintype.card_coe, BinaryTree.treesOfNumNodesEq_card_eq_catalan,
    Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    extraRows_card]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq,
    Fintype.card_fin]
  simp only [Nat.cast_id]
  ring

lemma catalan_le_four_pow (q : ℕ) : catalan q ≤ 4 ^ q := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow q)

lemma descFactorial_le_factorial (p d : ℕ) (h : d ≤ p) : p.descFactorial d ≤ p.factorial := by
  calc
    _ ≤ (p - d).factorial * p.descFactorial d :=
      Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    _ = p.factorial := Nat.factorial_mul_descFactorial h

 theorem endpointDiagram_card_le {Row : Type*} [Fintype Row] (q : ℕ)
    (hq : q - 1 ≤ Fintype.card Row) :
    Fintype.card (EndpointDiagram Row q) ≤
      8 ^ (q - 1) * (Fintype.card Row).factorial *
        (q * q) ^ (Fintype.card Row - (q - 1)) := by
  rw [endpointDiagram_card]
  calc
    _ ≤ 4 ^ (q - 1) * (Fintype.card Row).factorial * 2 ^ (q - 1) *
        (q * q) ^ (Fintype.card Row - (q - 1)) := by
      gcongr
      · exact catalan_le_four_pow _
      · exact descFactorial_le_factorial _ _ hq
    _ = _ := by
      rw [show (8 : ℕ) = 4 * 2 by rfl]
      simp only [mul_pow]
      ring


end DiagramCounts

section DiagramEncoding
attribute [local instance] Classical.decEq Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

noncomputable def diagramNodeEquiv {q : ℕ}
    (shape : BinaryTree.treesOfNumNodesEq (q - 1)) : NodePos shape.1 ≃ Fin (q - 1) :=
  Fintype.equivFinOfCardEq ((nodePos_card shape.1).trans
    (BinaryTree.mem_treesOfNumNodesEq.mp shape.2))

noncomputable def diagramVertexEquiv {q : ℕ} (hq : 0 < q)
    (shape : BinaryTree.treesOfNumNodesEq (q - 1)) : Option (NodePos shape.1) ≃ Fin q :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_option, nodePos_card,
      BinaryTree.mem_treesOfNumNodesEq.mp shape.2]
    omega)

noncomputable def diagramParent {q : ℕ} (hq : 0 < q)
    (shape : BinaryTree.treesOfNumNodesEq (q - 1)) (i : Fin (q - 1)) : Fin q :=
  diagramVertexEquiv hq shape (parent shape.1 ((diagramNodeEquiv shape).symm i))

noncomputable def diagramChild {q : ℕ} (hq : 0 < q)
    (shape : BinaryTree.treesOfNumNodesEq (q - 1)) (i : Fin (q - 1)) : Fin q :=
  diagramVertexEquiv hq shape (some ((diagramNodeEquiv shape).symm i))

/-- The tree rows record an orientation; every remaining row records its two
vertex coordinates. The labels include the root coordinate. -/
noncomputable def DiagramRealizes {Row α : Type*} {q : ℕ} (hq : 0 < q)
    (diagram : EndpointDiagram Row q) (labels : Fin q → α) (pairs : Row → α × α) : Prop :=
  (∀ i, pairs (diagram.2.1 i) =
    if diagram.2.2.1 i then
      (labels (diagramChild hq diagram.1 i), labels (diagramParent hq diagram.1 i))
    else (labels (diagramParent hq diagram.1 i), labels (diagramChild hq diagram.1 i))) ∧
  (∀ row : ExtraRows diagram.2.1, pairs row.1 =
    (labels (diagram.2.2.2 row).1, labels (diagram.2.2.2 row).2))

/-- A connected endpoint graph has a diagram using each spanning-tree row once. -/
theorem exists_endpointDiagram {Row α : Type*} [Fintype α]
    (G : SimpleGraph α) (hc : G.Connected) (pairs : Row → α × α)
    (hw : ∀ x y, G.Adj x y → ∃ row,
      s(x, y) = s((pairs row).1, (pairs row).2)) :
    ∃ hq : 0 < Fintype.card α, ∃ diagram : EndpointDiagram Row (Fintype.card α),
      ∃ labels : Fin (Fintype.card α) ≃ α,
        DiagramRealizes hq diagram labels pairs := by
  obtain ⟨root⟩ := hc.nonempty
  have hq : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨root⟩
  obtain ⟨tree, hv, hn, hcover⟩ := exists_plane_spanning_tree G hc root
  let vl : Option (NodePos (treeShape tree)) ≃ α :=
    Equiv.ofBijective (vertexLabels root tree)
      ⟨vertexLabels_injective root tree hn, vertexLabels_surjective root tree hcover⟩
  have hsize : (treeShape tree).numNodes = Fintype.card α - 1 := by
    have h := Fintype.card_congr vl
    rw [Fintype.card_option, nodePos_card] at h
    omega
  let shape : BinaryTree.treesOfNumNodesEq (Fintype.card α - 1) :=
    ⟨treeShape tree, BinaryTree.mem_treesOfNumNodesEq.mpr hsize⟩
  obtain ⟨eNode, heNode⟩ := exists_tree_row_embedding G pairs hw root tree hv hn
  let e : Fin (Fintype.card α - 1) ↪ Row :=
    (diagramNodeEquiv shape).symm.toEmbedding.trans eNode
  let labels : Fin (Fintype.card α) ≃ α := (diagramVertexEquiv hq shape).symm.trans vl
  have hparent (i : Fin (Fintype.card α - 1)) :
      labels (diagramParent hq shape i) =
        vertexLabels root tree (parent (treeShape tree) ((diagramNodeEquiv shape).symm i)) := by
    simp [labels, diagramParent, vl, shape]
  have hchild (i : Fin (Fintype.card α - 1)) :
      labels (diagramChild hq shape i) = nodeLabel tree ((diagramNodeEquiv shape).symm i) := by
    simp [labels, diagramChild, vl, shape, vertexLabels]
  have horient : ∀ i : Fin (Fintype.card α - 1), ∃ flip : Bool,
      pairs (e i) = if flip then
        (labels (diagramChild hq shape i), labels (diagramParent hq shape i))
      else (labels (diagramParent hq shape i), labels (diagramChild hq shape i)) := by
    intro i
    have h := heNode ((diagramNodeEquiv shape).symm i)
    change s(vertexLabels root tree (parent (treeShape tree) ((diagramNodeEquiv shape).symm i)),
      nodeLabel tree ((diagramNodeEquiv shape).symm i)) =
      s((pairs (e i)).1, (pairs (e i)).2) at h
    rw [← hparent i, ← hchild i] at h
    rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨false, by simp only [Bool.false_eq_true, ↓reduceIte]; exact Prod.ext h₁.symm h₂.symm⟩
    · exact ⟨true, by simp only [↓reduceIte]; exact Prod.ext h₂.symm h₁.symm⟩
  choose flip hflip using horient
  let chords : ExtraRows e → Fin (Fintype.card α) × Fin (Fintype.card α) :=
    fun row => (labels.symm (pairs row.1).1, labels.symm (pairs row.1).2)
  refine ⟨hq, (shape, ⟨e, flip, chords⟩), labels, hflip, ?_⟩
  intro row
  simp only [chords, Equiv.apply_symm_apply, Prod.mk.eta]



lemma diagramRealizes_map {Row α β : Type*} {q : ℕ} {hq : 0 < q}
    {diagram : EndpointDiagram Row q} {labels : Fin q → α} {pairs : Row → α × α}
    (f : α → β) (h : DiagramRealizes hq diagram labels pairs) :
    DiagramRealizes hq diagram (fun i => f (labels i))
      (fun row => (f (pairs row).1, f (pairs row).2)) := by
  constructor
  · intro i
    change (f (pairs (diagram.2.1 i)).1, f (pairs (diagram.2.1 i)).2) = _
    rw [h.1 i]
    split_ifs <;> rfl
  · intro row
    change (f (pairs row.1).1, f (pairs row.1).2) = _
    rw [h.2 row]


lemma extendRowAssignment_apply (D : LateData hPT) (S : Finset (Pos T k))
    (a : RowAssignment S) (v : S) : extendRowAssignment D S a v = a v := by
  simp only [extendRowAssignment, v.2, ↓reduceDIte]

lemma supported_host_mem (D : LateData hPT) (palette : PaletteIndex D)
    (S : Finset (Pos T k)) (a : RowAssignment S) (violating : Bool)
    (ha : rowPredicate D palette S violating a)
    (x : HostVertices S (extendRowAssignment D S a)) :
    x.1 ∈ D.palettes palette.1 palette.2 := by
  obtain ⟨v, hv, hx⟩ := Finset.mem_biUnion.mp x.2
  let row : S := ⟨v, hv⟩
  have hrow := extendRowAssignment_apply D S a row
  change extendRowAssignment D S a v = a row at hrow
  rw [hrow] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx
  · rw [hx]
    exact (ha.1 row).2.1
  · rw [hx]
    exact (ha.1 row).2.2

/-- Every supported assignment has a finite diagram, injective palette-valued
labels, and the endpoint-count bounds used to stratify the weighted sum. -/
theorem supported_assignment_diagram (D : LateData hPT) (palette : PaletteIndex D)
    (S : Finset (Pos T k)) (violating : Bool) (a : RowAssignment S)
    (ha : rowPredicate D palette S violating a) :
    ∃ q : ℕ, ∃ hq : 0 < q,
      q = (endpointVertices S (extendRowAssignment D S a)).card ∧
      2 ≤ q ∧ q ≤ S.card + 1 ∧ (violating = true → q < S.card) ∧
      ∃ diagram : EndpointDiagram S q, ∃ labels : Fin q ↪ Fin (T.S.N k),
        (∀ i, labels i ∈ D.palettes palette.1 palette.2) ∧
        DiagramRealizes hq diagram labels a := by
  let b := extendRowAssignment D S a
  let V := HostVertices S b
  let pairs : S → V × V := fun row => (hostFirst S b row, hostSecond S b row)
  have hc : (hostGraph S b).Connected := hostGraph_connected S b ha.2.1
  have hw : ∀ x y : V, (hostGraph S b).Adj x y → ∃ row : S,
      s(x, y) = s((pairs row).1, (pairs row).2) := by
    rintro x y ⟨hne, row, hx⟩
    refine ⟨row, ?_⟩
    rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have h₁' : x = (pairs row).1 := Subtype.ext h₁
      have h₂' : y = (pairs row).2 := Subtype.ext h₂
      rw [h₁', h₂']
    · have h₁' : x = (pairs row).2 := Subtype.ext h₁
      have h₂' : y = (pairs row).1 := Subtype.ext h₂
      rw [h₁', h₂']
      exact Sym2.eq_swap
  obtain ⟨hq, diagram, labelsV, hrealizes⟩ := exists_endpointDiagram (hostGraph S b) hc pairs hw
  let labels : Fin (Fintype.card V) ↪ Fin (T.S.N k) :=
    labelsV.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hcard : Fintype.card V = (endpointVertices S b).card := Fintype.card_coe _
  have htwo : 2 ≤ Fintype.card V := by
    obtain ⟨row⟩ := ha.2.1.nonempty
    have hne : hostFirst S b row ≠ hostSecond S b row := by
      intro heq
      have h := congrArg Subtype.val heq
      change (b row).1 = (b row).2 at h
      have hb := extendRowAssignment_apply D S a row
      change b row = a row at hb
      rw [hb] at h
      exact (ha.1 row).1 h
    haveI : Nontrivial V := ⟨⟨hostFirst S b row, hostSecond S b row, hne⟩⟩
    exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hupper : Fintype.card V ≤ S.card + 1 := by
    rw [hcard]
    exact connected_vertices_le S b ha.2.1
  have hviolating : violating = true → Fintype.card V < S.card := by
    rw [hcard]
    exact ha.2.2
  refine ⟨Fintype.card V, hq, hcard, htwo, hupper, hviolating,
    diagram, labels, ?_, ?_⟩
  · intro i
    exact supported_host_mem D palette S a violating ha (labelsV i)
  · have hmap := diagramRealizes_map (fun x : V => x.1) hrealizes
    have hpairs : (fun row : S => ((pairs row).1.1, (pairs row).2.1)) = a := by
      funext row
      exact extendRowAssignment_apply D S a row
    rw [hpairs] at hmap
    exact hmap

end DiagramEncoding

end HypercubeRamsey.S18.Lane_sol_s18_6b
