import HypercubeRamsey.Framework.Patch

/-!
# Lemma 3.2: stabilization and finite menus

Source: `sections/03-…tex`, Lemma 3.2 (`lem:stabilization`) and its proof.
-/

namespace HypercubeRamsey

open Filter

private lemma tendsto_eventually_lt {f : ℕ → ℝ} (hf : Tendsto f atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, f k < ε := by
  filter_upwards [Metric.tendsto_nhds.1 hf ε hε] with k hk
  have hk' : |f k| < ε := by simpa [Real.dist_eq] using hk
  exact (abs_lt.mp hk').2

private lemma card_sdiff_compl_le {N : ℕ} (A B : Finset (Fin N)) :
    (A \ B)ᶜ.card ≤ Aᶜ.card + B.card := by
  calc
    (A \ B)ᶜ.card ≤ (Aᶜ ∪ B).card := Finset.card_le_card fun x hx => by
      simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union] at *
      tauto
    _ ≤ Aᶜ.card + B.card := Finset.card_union_le _ _

private lemma card_subset_compl_le {N : ℕ} (A B : Finset (Fin N)) :
    (B \ A).card ≤ Aᶜ.card := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_compl] at *
  exact hx.2

private lemma eventually_fintype_forall {ι : Type*} [Fintype ι] {p : ι → ℕ → Prop}
    (h : ∀ i, ∀ᶠ k in atTop, p i k) : ∀ᶠ k in atTop, ∀ i, p i k := by
  classical
  choose bound hbound using fun i => (Filter.eventually_atTop.1 (h i))
  let M := Finset.univ.sup bound
  filter_upwards [Filter.eventually_atTop.2 ⟨M, fun k hk i => hbound i k
    ((Finset.le_sup (Finset.mem_univ i)).trans hk)⟩] with k hk
  exact hk

private lemma card_removed_pair_le {N : ℕ} (A B R S : Finset (Fin N))
    (hN : 0 < N) :
    ((((A \ R)ᶜ.card + (B \ S)ᶜ.card : ℕ) : ℝ) / N) ≤
      ((((Aᶜ.card + Bᶜ.card : ℕ) : ℝ) / N) +
        (((R.card + S.card : ℕ) : ℝ) / N)) := by
  have hX := card_sdiff_compl_le A R
  have hY := card_sdiff_compl_le B S
  have hNat : (A \ R)ᶜ.card + (B \ S)ᶜ.card ≤ Aᶜ.card + Bᶜ.card + (R.card + S.card) := by omega
  have hReal :
      (((A \ R)ᶜ.card + (B \ S)ᶜ.card : ℕ) : ℝ) ≤
        ((Aᶜ.card + Bᶜ.card + (R.card + S.card) : ℕ) : ℝ) := by exact_mod_cast hNat
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  calc
    (((A \ R)ᶜ.card + (B \ S)ᶜ.card : ℕ) : ℝ) / N ≤
        ((Aᶜ.card + Bᶜ.card + (R.card + S.card) : ℕ) : ℝ) / N :=
      div_le_div_of_nonneg_right hReal hN'.le
    _ = (((Aᶜ.card + Bᶜ.card : ℕ) : ℝ) / N) +
        (((R.card + S.card : ℕ) : ℝ) / N) := by push_cast; ring

private def goodAt (U : Stage) (P : PatchProp) (κ : ℝ) (k : ℕ) : Prop :=
  ∀ RX RY : Finset (Fin (U.S.N k)),
    (RX.card : ℝ) ≤ κ * U.S.N k → (RY.card : ℝ) ≤ κ * U.S.N k →
      ∃ A B, (A, B) ∈ P (U.S.n k) (U.S.N k) (U.S.E k) ∧
        A ⊆ U.X k \ RX ∧ B ⊆ U.Y k \ RY

private noncomputable def removeTol (i : ℕ) : ℝ := 1 / (2 * ((i : ℝ) + 1))

private theorem eliminate_property (U : Stage) (P : PatchProp)
    (hnot : ¬ Available U P) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
      ∃ X : (k : ℕ) → Finset (Fin (U.S.N (φ k))),
      ∃ Y : (k : ℕ) → Finset (Fin (U.S.N (φ k))),
        (∀ k, X k ⊆ U.X (φ k)) ∧ (∀ k, Y k ⊆ U.Y (φ k)) ∧
        ∃ hsmall : Tendsto (fun k => (((X k)ᶜ.card + (Y k)ᶜ.card : ℕ) : ℝ) /
            U.S.N (φ k)) atTop (nhds 0),
          EventuallyAbsent ⟨U.S.comp φ hφ, X, Y, hsmall⟩ P := by
  classical
  have htol : ∀ i, 0 < removeTol i := by
    intro i
    dsimp [removeTol]
    positivity
  have hfreq : ∀ i, ∃ᶠ k in atTop, ¬ goodAt U P (removeTol i) k := by
    intro i
    have hno : ¬ ∀ᶠ k in atTop, goodAt U P (removeTol i) k := by
      intro hgood
      apply hnot
      exact ⟨removeTol i, htol i, by simpa only [goodAt] using hgood⟩
    exact (Filter.not_eventually).1 hno
  obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_forall_of_frequently hfreq
  have hkill : ∀ i, ∃ RX RY : Finset (Fin (U.S.N (φ i))),
      (RX.card : ℝ) ≤ removeTol i * U.S.N (φ i) ∧
      (RY.card : ℝ) ≤ removeTol i * U.S.N (φ i) ∧
      ∀ A B, (A, B) ∈ P (U.S.n (φ i)) (U.S.N (φ i)) (U.S.E (φ i)) →
        ¬ (A ⊆ U.X (φ i) \ RX ∧ B ⊆ U.Y (φ i) \ RY) := by
    intro i
    have hi := hbad i
    unfold goodAt at hi
    push_neg at hi
    rcases hi with ⟨RX, RY, hRX, hRY, hNo⟩
    refine ⟨RX, RY, hRX, hRY, ?_⟩
    intro A B hmem hAB
    exact hNo A B hmem hAB.1 hAB.2
  choose RX RY hRX hRY hNo using hkill
  let X : ∀ k, Finset (Fin (U.S.N (φ k))) := fun k => U.X (φ k) \ RX k
  let Y : ∀ k, Finset (Fin (U.S.N (φ k))) := fun k => U.Y (φ k) \ RY k
  have hX : ∀ k, X k ⊆ U.X (φ k) := fun _ => Finset.sdiff_subset
  have hY : ∀ k, Y k ⊆ U.Y (φ k) := fun _ => Finset.sdiff_subset
  have hremBound : ∀ i,
      (((RX i).card + (RY i).card : ℕ) : ℝ) / U.S.N (φ i) ≤ 1 / ((i : ℝ) + 1) := by
    intro i
    have hN : (0 : ℝ) < U.S.N (φ i) := by exact_mod_cast U.S.N_pos (φ i)
    have hsum : ((RX i).card : ℝ) + ((RY i).card : ℝ) ≤
        (1 / ((i : ℝ) + 1)) * U.S.N (φ i) := by
      calc
        ((RX i).card : ℝ) + ((RY i).card : ℝ) ≤
            removeTol i * U.S.N (φ i) + removeTol i * U.S.N (φ i) :=
              add_le_add (hRX i) (hRY i)
        _ = (1 / ((i : ℝ) + 1)) * U.S.N (φ i) := by
              simp [removeTol]
              ring
    have hsum' : (((RX i).card + (RY i).card : ℕ) : ℝ) ≤
        (1 / ((i : ℝ) + 1)) * U.S.N (φ i) := by
      simpa using hsum
    exact (div_le_iff₀ hN).2 hsum'
  have hrem : Tendsto (fun i => (((RX i).card + (RY i).card : ℕ) : ℝ) /
      U.S.N (φ i)) atTop (nhds 0) := by
    apply squeeze_zero (fun i => by positivity) hremBound
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hOld : Tendsto (fun k => (((U.X (φ k))ᶜ.card + (U.Y (φ k))ᶜ.card : ℕ) : ℝ) /
      U.S.N (φ k)) atTop (nhds 0) := U.small.comp hφ.tendsto_atTop
  have hsum : Tendsto (fun k =>
      (((U.X (φ k))ᶜ.card + (U.Y (φ k))ᶜ.card : ℕ) : ℝ) / U.S.N (φ k) +
        (((RX k).card + (RY k).card : ℕ) : ℝ) / U.S.N (φ k)) atTop (nhds 0) := by
    simpa using hOld.add hrem
  have hsmall : Tendsto (fun k => (((X k)ᶜ.card + (Y k)ᶜ.card : ℕ) : ℝ) /
      U.S.N (φ k)) atTop (nhds 0) := by
    apply squeeze_zero (fun k => by positivity) ?_ hsum
    intro k
    simpa [X, Y] using card_removed_pair_le (U.X (φ k)) (U.Y (φ k))
      (RX k) (RY k) (U.S.N_pos (φ k))
  refine ⟨φ, hφ, X, Y, hX, hY, hsmall, ?_⟩
  filter_upwards [Filter.Eventually.of_forall (fun k => hNo k)] with k hk A B hmem hAB
  exact hk A B hmem hAB

private structure ElimWitness (U : Stage) (P : PatchProp) where
  φ : ℕ → ℕ
  hφ : StrictMono φ
  X : (k : ℕ) → Finset (Fin (U.S.N (φ k)))
  Y : (k : ℕ) → Finset (Fin (U.S.N (φ k)))
  hX : ∀ k, X k ⊆ U.X (φ k)
  hY : ∀ k, Y k ⊆ U.Y (φ k)
  hsmall : Tendsto (fun k => (((X k)ᶜ.card + (Y k)ᶜ.card : ℕ) : ℝ) /
      U.S.N (φ k)) atTop (nhds 0)
  hAbsent : EventuallyAbsent ⟨U.S.comp φ hφ, X, Y, hsmall⟩ P

private theorem eliminate_property_nonempty (U : Stage) (P : PatchProp)
    (hnot : ¬ Available U P) : Nonempty (ElimWitness U P) := by
  obtain ⟨φ, hφ, X, Y, hX, hY, hsmall, hAbsent⟩ := eliminate_property U P hnot
  exact ⟨⟨φ, hφ, X, Y, hX, hY, hsmall, hAbsent⟩⟩

private structure StabState (T : Stage) where
  idx : ℕ → ℕ
  strict : StrictMono idx
  X : ∀ k, Finset (Fin (T.S.N (idx k)))
  Y : ∀ k, Finset (Fin (T.S.N (idx k)))
  small : Tendsto (fun k => (((X k)ᶜ.card + (Y k)ᶜ.card : ℕ) : ℝ) /
    T.S.N (idx k)) atTop (nhds 0)

private def StabState.toStage {T : Stage} (s : StabState T) : Stage where
  S := T.S.comp s.idx s.strict
  X := s.X
  Y := s.Y
  small := s.small

private def stepStage {T : Stage} (s : StabState T) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (X Y : ∀ k, Finset (Fin (s.toStage.S.N (φ k))))
    (hsmall : Tendsto (fun k => (((X k)ᶜ.card + (Y k)ᶜ.card : ℕ) : ℝ) /
      s.toStage.S.N (φ k)) atTop (nhds 0)) : Stage where
  S := s.toStage.S.comp φ hφ
  X := X
  Y := Y
  small := hsmall

private structure StabStep {T : Stage} (s : StabState T) (P : PatchProp) where
  φ : ℕ → ℕ
  strict : StrictMono φ
  X : ∀ k, Finset (Fin (s.toStage.S.N (φ k)))
  Y : ∀ k, Finset (Fin (s.toStage.S.N (φ k)))
  small : Tendsto (fun k => (((X k)ᶜ.card + (Y k)ᶜ.card : ℕ) : ℝ) /
    s.toStage.S.N (φ k)) atTop (nhds 0)
  subX : ∀ k, X k ⊆ s.X (φ k)
  subY : ∀ k, Y k ⊆ s.Y (φ k)
  status : Available (stepStage s φ strict X Y small) P ∨
    EventuallyAbsent (stepStage s φ strict X Y small) P

private noncomputable def chooseStep {T : Stage} (s : StabState T) (P : PatchProp) :
    StabStep s P := by
  classical
  by_cases h : Available s.toStage P
  · refine ⟨id, strictMono_id, s.X, s.Y, s.small, ?_, ?_, ?_⟩
    · intro k
      exact Finset.Subset.rfl
    · intro k
      exact Finset.Subset.rfl
    · left
      simpa [stepStage, StabState.toStage, BadSeq.comp] using h
  · let e := Classical.choice (eliminate_property_nonempty s.toStage P h)
    exact ⟨e.φ, e.hφ, e.X, e.Y, e.hsmall, e.hX, e.hY,
      Or.inr (by simpa [stepStage] using e.hAbsent)⟩

private def StabState.after {T : Stage} (s : StabState T) {P : PatchProp}
    (step : StabStep s P) : StabState T where
  idx := fun k => s.idx (step.φ k)
  strict := s.strict.comp step.strict
  X := step.X
  Y := step.Y
  small := step.small

private noncomputable def stateSeq {T : Stage} (P : ℕ → PatchProp) : ℕ → StabState T
  | 0 => ⟨id, by intro a b hab; exact hab, T.X, T.Y, T.small⟩
  | j + 1 =>
      let s := stateSeq (T := T) P j
      s.after (chooseStep s (P j))

private noncomputable def stateStep {T : Stage} (P : ℕ → PatchProp) (j : ℕ) :
    StabStep (stateSeq (T := T) P j) (P j) :=
  chooseStep (stateSeq (T := T) P j) (P j)

private theorem stateSeq_succ {T : Stage} (P : ℕ → PatchProp) (j : ℕ) :
    stateSeq (T := T) P (j + 1) = (stateSeq (T := T) P j).after (stateStep (T := T) P j) := rfl

private lemma strictMono_ge_id {f : ℕ → ℕ} (hf : StrictMono f) : ∀ k, k ≤ f k := by
  intro k
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hs := hf (Nat.lt_succ_self k)
      exact Nat.succ_le_of_lt (ih.trans_lt hs)

private noncomputable def tailMap {T : Stage} (P : ℕ → PatchProp) (q : ℕ) :
    ℕ → ℕ → ℕ
  | 0, k => k
  | d + 1, k => tailMap (T := T) P q d ((stateStep (T := T) P (q + d)).φ k)

private theorem tailMap_strict {T : Stage} (P : ℕ → PatchProp) (q d : ℕ) :
    StrictMono (tailMap (T := T) P q d) := by
  induction d with
  | zero =>
      intro a b hab
      simpa [tailMap] using hab
  | succ d ih =>
      change StrictMono (fun k => tailMap (T := T) P q d ((stateStep (T := T) P (q + d)).φ k))
      exact ih.comp (stateStep (T := T) P (q + d)).strict

private theorem stateIndex_tail {T : Stage} (P : ℕ → PatchProp) (q d k : ℕ) :
    (stateSeq (T := T) P (q + d)).idx k =
      (stateSeq (T := T) P q).idx (tailMap (T := T) P q d k) := by
  induction d generalizing k with
  | zero => simp [tailMap]
  | succ d ih =>
      rw [Nat.add_succ, stateSeq_succ]
      change (stateSeq (T := T) P (q + d)).idx ((stateStep (T := T) P (q + d)).φ k) =
        (stateSeq (T := T) P q).idx
          (tailMap (T := T) P q d ((stateStep (T := T) P (q + d)).φ k))
      exact ih ((stateStep (T := T) P (q + d)).φ k)

private theorem stateX_tail {T : Stage} (P : ℕ → PatchProp) (q d : ℕ) :
    ∀ k, (stateSeq (T := T) P (q + d)).X k ⊆
      (congrArg T.S.N (stateIndex_tail (T := T) P q d k)).symm ▸
        (stateSeq (T := T) P q).X (tailMap (T := T) P q d k) := by
  induction d with
  | zero =>
      intro k
      cases stateIndex_tail (T := T) P q 0 k
      simp [tailMap]
  | succ d ih =>
      intro k
      change (stateStep (T := T) P (q + d)).X k ⊆
        (congrArg T.S.N
          (stateIndex_tail (T := T) P q d ((stateStep (T := T) P (q + d)).φ k))).symm ▸
          (stateSeq (T := T) P q).X
            (tailMap (T := T) P q d ((stateStep (T := T) P (q + d)).φ k))
      exact Finset.Subset.trans ((stateStep (T := T) P (q + d)).subX k)
        (ih ((stateStep (T := T) P (q + d)).φ k))

private theorem stateY_tail {T : Stage} (P : ℕ → PatchProp) (q d : ℕ) :
    ∀ k, (stateSeq (T := T) P (q + d)).Y k ⊆
      (congrArg T.S.N (stateIndex_tail (T := T) P q d k)).symm ▸
        (stateSeq (T := T) P q).Y (tailMap (T := T) P q d k) := by
  induction d with
  | zero =>
      intro k
      cases stateIndex_tail (T := T) P q 0 k
      simp [tailMap]
  | succ d ih =>
      intro k
      change (stateStep (T := T) P (q + d)).Y k ⊆
        (congrArg T.S.N
          (stateIndex_tail (T := T) P q d ((stateStep (T := T) P (q + d)).φ k))).symm ▸
          (stateSeq (T := T) P q).Y
            (tailMap (T := T) P q d ((stateStep (T := T) P (q + d)).φ k))
      exact Finset.Subset.trans ((stateStep (T := T) P (q + d)).subY k)
        (ih ((stateStep (T := T) P (q + d)).φ k))

private theorem stateX_base {T : Stage} (P : ℕ → PatchProp) :
    ∀ i k, (stateSeq (T := T) P i).X k ⊆ T.X ((stateSeq (T := T) P i).idx k) := by
  intro i
  induction i with
  | zero =>
      intro k
      change T.X k ⊆ T.X k
      exact Finset.Subset.rfl
  | succ i ih =>
      intro k
      change (stateStep (T := T) P i).X k ⊆
        T.X ((stateSeq (T := T) P i).idx ((stateStep (T := T) P i).φ k))
      exact Finset.Subset.trans ((stateStep (T := T) P i).subX k)
        (ih ((stateStep (T := T) P i).φ k))

private theorem stateY_base {T : Stage} (P : ℕ → PatchProp) :
    ∀ i k, (stateSeq (T := T) P i).Y k ⊆ T.Y ((stateSeq (T := T) P i).idx k) := by
  intro i
  induction i with
  | zero =>
      intro k
      change T.Y k ⊆ T.Y k
      exact Finset.Subset.rfl
  | succ i ih =>
      intro k
      change (stateStep (T := T) P i).Y k ⊆
        T.Y ((stateSeq (T := T) P i).idx ((stateStep (T := T) P i).φ k))
      exact Finset.Subset.trans ((stateStep (T := T) P i).subY k)
        (ih ((stateStep (T := T) P i).φ k))

private noncomputable def diagonalIndex {T : Stage} (P : ℕ → PatchProp) (m : ℕ → ℕ) :
    ℕ → ℕ := fun i => (stateSeq (T := T) P i).idx (m i)

private theorem diagonalIndex_strict {T : Stage} (P : ℕ → PatchProp) (m : ℕ → ℕ)
    (hm : StrictMono m) : StrictMono (diagonalIndex (T := T) P m) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hmi := hm (Nat.lt_succ_self i)
  have hlarge := strictMono_ge_id ((stateStep (T := T) P i).strict) (m (i + 1))
  change (stateSeq (T := T) P i).idx (m i) <
    (stateSeq (T := T) P (i + 1)).idx (m (i + 1))
  calc
    (stateSeq (T := T) P i).idx (m i) <
        (stateSeq (T := T) P i).idx ((stateStep (T := T) P i).φ (m (i + 1))) :=
      (stateSeq (T := T) P i).strict (hmi.trans_le hlarge)
    _ = (stateSeq (T := T) P (i + 1)).idx (m (i + 1)) := by
      simp [stateSeq_succ, StabState.after]

private lemma card_finset_cast_index {S : BadSeq} {k l : ℕ} (hkl : k = l)
    (A : Finset (Fin (S.N k))) : (hkl ▸ A).card = A.card := by
  cases hkl
  rfl

private lemma card_compl_finset_cast_index {S : BadSeq} {k l : ℕ} (hkl : k = l)
    (A : Finset (Fin (S.N k))) : ((hkl ▸ A)ᶜ).card = Aᶜ.card := by
  cases hkl
  rfl

private lemma card_finset_cast_host {S : BadSeq} {k l : ℕ} (hkl : k = l)
    (hN : S.N k = S.N l) (A : Finset (Fin (S.N k))) :
    (hN ▸ A).card = A.card := by
  cases hkl
  rfl

private lemma card_compl_finset_cast_host {S : BadSeq} {k l : ℕ} (hkl : k = l)
    (hN : S.N k = S.N l) (A : Finset (Fin (S.N k))) :
    ((hN ▸ A)ᶜ).card = Aᶜ.card := by
  cases hkl
  rfl

private theorem transport_patch_witness {S : BadSeq} {P : PatchProp} {k l : ℕ}
    (hkl : k = l) (hN : S.N k = S.N l) (A B Xold Yold : Finset (Fin (S.N l)))
    (Xnew Ynew RX RY : Finset (Fin (S.N k)))
    (hmem : (A, B) ∈ P (S.n l) (S.N l) (S.E l))
    (hA : A ⊆ Xold \ ((hN ▸ RX) ∪ (Xold \ (hN ▸ Xnew))))
    (hB : B ⊆ Yold \ ((hN ▸ RY) ∪ (Yold \ (hN ▸ Ynew)))) :
    ∃ A' B', (A', B') ∈ P (S.n k) (S.N k) (S.E k) ∧
      A' ⊆ Xnew \ RX ∧ B' ⊆ Ynew \ RY := by
  refine ⟨hN.symm ▸ A, hN.symm ▸ B, ?_, ?_, ?_⟩
  · cases hkl
    exact hmem
  · cases hkl
    intro x hx
    rcases Finset.mem_sdiff.mp (hA hx) with ⟨hxOld, hxnot⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · by_contra hxNew
      exact hxnot (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxOld, hxNew⟩)))
    · intro hxR
      exact hxnot (Finset.mem_union.mpr (Or.inl hxR))
  · cases hkl
    intro y hy
    rcases Finset.mem_sdiff.mp (hB hy) with ⟨hyOld, hynot⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · by_contra hyNew
      exact hynot (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hyOld, hyNew⟩)))
    · intro hyR
      exact hynot (Finset.mem_union.mpr (Or.inl hyR))

private theorem transport_patch_absence {S : BadSeq} {P : PatchProp} {k l : ℕ}
    (hkl : k = l) (hN : S.N k = S.N l) (Xnew Ynew : Finset (Fin (S.N k)))
    (Xold Yold : Finset (Fin (S.N l)))
    (hX : Xnew ⊆ hN.symm ▸ Xold) (hY : Ynew ⊆ hN.symm ▸ Yold)
    (habs : ∀ A B, (A, B) ∈ P (S.n l) (S.N l) (S.E l) →
      ¬ (A ⊆ Xold ∧ B ⊆ Yold)) :
    ∀ A B, (A, B) ∈ P (S.n k) (S.N k) (S.E k) →
      ¬ (A ⊆ Xnew ∧ B ⊆ Ynew) := by
  cases hkl
  intro A B hmem hAB
  exact habs A B hmem ⟨hAB.1.trans hX, hAB.2.trans hY⟩

private theorem available_remove {T : Stage} {P : PatchProp}
    (h : Available T P) {X' Y' : ∀ k, Finset (Fin (T.S.N k))}
    (hX : ∀ k, X' k ⊆ T.X k) (hY : ∀ k, Y' k ⊆ T.Y k)
    (hsmall : Tendsto (fun k => (((X' k)ᶜ.card + (Y' k)ᶜ.card : ℕ) : ℝ) /
      T.S.N k) atTop (nhds 0)) :
    Available ⟨T.S, X', Y', hsmall⟩ P := by
  classical
  obtain ⟨κ, hκ, hav⟩ := h
  refine ⟨κ / 2, by positivity, ?_⟩
  have hsmall' := tendsto_eventually_lt hsmall (by linarith : 0 < κ / 2)
  filter_upwards [hav, hsmall'] with k hk hε
  intro RX RY hRX hRY
  let RX' := RX ∪ (T.X k \ X' k)
  let RY' := RY ∪ (T.Y k \ Y' k)
  have hExtraX : ((T.X k \ X' k).card : ℝ) ≤ (X' k)ᶜ.card := by
    exact_mod_cast card_subset_compl_le (X' k) (T.X k)
  have hExtraY : ((T.Y k \ Y' k).card : ℝ) ≤ (Y' k)ᶜ.card := by
    exact_mod_cast card_subset_compl_le (Y' k) (T.Y k)
  have hN : 0 < T.S.N k := T.S.N_pos k
  have hNreal : (0 : ℝ) < T.S.N k := by exact_mod_cast hN
  have hExtra : (((T.X k \ X' k).card + (T.Y k \ Y' k).card : ℕ) : ℝ) ≤
      (κ / 2) * T.S.N k := by
    have hsum : (((T.X k \ X' k).card + (T.Y k \ Y' k).card : ℕ) : ℝ) ≤
        ((X' k)ᶜ.card + (Y' k)ᶜ.card : ℕ) := by
      exact_mod_cast Nat.add_le_add
        (card_subset_compl_le (X' k) (T.X k)) (card_subset_compl_le (Y' k) (T.Y k))
    have hratio : (((X' k)ᶜ.card + (Y' k)ᶜ.card : ℕ) : ℝ) <
        (κ / 2) * T.S.N k := by
      have := (div_lt_iff₀ hNreal).1 hε
      linarith
    linarith
  have hRX' : (RX'.card : ℝ) ≤ κ * T.S.N k := by
    have hcard : RX'.card ≤ RX.card + (T.X k \ X' k).card := by
      simp [RX', Finset.card_union_le]
    have hcard' : (RX'.card : ℝ) ≤ (RX.card : ℝ) + ((T.X k \ X' k).card : ℝ) := by
      exact_mod_cast hcard
    have hpart : ((T.X k \ X' k).card : ℝ) ≤ (κ / 2) * T.S.N k := by
      have hBoth : (((T.X k \ X' k).card + (T.Y k \ Y' k).card : ℕ) : ℝ) ≤
          (κ / 2) * T.S.N k := hExtra
      have hNonneg : 0 ≤ ((T.Y k \ Y' k).card : ℝ) := by positivity
      have hle : ((T.X k \ X' k).card : ℝ) ≤
          (((T.X k \ X' k).card + (T.Y k \ Y' k).card : ℕ) : ℝ) := by
        push_cast
        exact le_add_of_nonneg_right (by positivity)
      exact le_trans hle hBoth
    have hsum : (RX.card : ℝ) + ((T.X k \ X' k).card : ℝ) ≤
        (κ / 2) * T.S.N k + (κ / 2) * T.S.N k := add_le_add hRX hpart
    linarith [hcard', hsum]
  have hRY' : (RY'.card : ℝ) ≤ κ * T.S.N k := by
    have hcard : RY'.card ≤ RY.card + (T.Y k \ Y' k).card := by
      simp [RY', Finset.card_union_le]
    have hcard' : (RY'.card : ℝ) ≤ (RY.card : ℝ) + ((T.Y k \ Y' k).card : ℝ) := by
      exact_mod_cast hcard
    have hpart : ((T.Y k \ Y' k).card : ℝ) ≤ (κ / 2) * T.S.N k := by
      have hBoth : (((T.X k \ X' k).card + (T.Y k \ Y' k).card : ℕ) : ℝ) ≤
          (κ / 2) * T.S.N k := hExtra
      have hle : ((T.Y k \ Y' k).card : ℝ) ≤
          (((T.X k \ X' k).card + (T.Y k \ Y' k).card : ℕ) : ℝ) := by
        push_cast
        exact le_add_of_nonneg_left (by positivity)
      exact le_trans hle hBoth
    have hsum : (RY.card : ℝ) + ((T.Y k \ Y' k).card : ℝ) ≤
        (κ / 2) * T.S.N k + (κ / 2) * T.S.N k := add_le_add hRY hpart
    linarith [hcard', hsum]
  obtain ⟨A, B, hmem, hA, hB⟩ := hk RX' RY' hRX' hRY'
  refine ⟨A, B, hmem, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_sdiff.mp (hA hx) with ⟨hxT, hxnot⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · by_contra hxX
      exact hxnot (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxX⟩)))
    · intro hxR
      exact hxnot (Finset.mem_union.mpr (Or.inl hxR))
  · intro y hy
    rcases Finset.mem_sdiff.mp (hB hy) with ⟨hyT, hynot⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · by_contra hyY
      exact hynot (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hyT, hyY⟩)))
    · intro hyR
      exact hynot (Finset.mem_union.mpr (Or.inl hyR))

private theorem available_mono {T : Stage} {P Q : PatchProp}
    (hPQ : ∀ n N E, P n N E ⊆ Q n N E) (hP : Available T P) : Available T Q := by
  obtain ⟨κ, hκ, hav⟩ := hP
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hav] with k hk RX RY hRX hRY
  obtain ⟨A, B, hmem, hA, hB⟩ := hk RX RY hRX hRY
  exact ⟨A, B, hPQ _ _ _ hmem, hA, hB⟩

/-- Lemma 3.2, first clause: a countable list of patch properties can be stabilized. -/
theorem stabilization (T : Stage) (P : ℕ → PatchProp) :
    ∃ T', T'.Refines T ∧ ∀ j, Available T' (P j) ∨ EventuallyAbsent T' (P j) := by
  classical
  have hsmallEvent : ∀ i, ∀ᶠ k in atTop,
      (((stateSeq (T := T) P i).X k)ᶜ.card + ((stateSeq (T := T) P i).Y k)ᶜ.card : ℕ) /
        T.S.N ((stateSeq (T := T) P i).idx k) < 1 / ((i : ℝ) + 1) := by
    intro i
    exact tendsto_eventually_lt (stateSeq (T := T) P i).small (by positivity)
  obtain ⟨m, hm, hmSmall⟩ := Filter.extraction_forall_of_eventually hsmallEvent
  let ψ := diagonalIndex (T := T) P m
  have hψ : StrictMono ψ := diagonalIndex_strict (T := T) P m hm
  let Xd : ∀ k, Finset (Fin (T.S.N (ψ k))) := fun k => (stateSeq (T := T) P k).X (m k)
  let Yd : ∀ k, Finset (Fin (T.S.N (ψ k))) := fun k => (stateSeq (T := T) P k).Y (m k)
  have hsmallD : Tendsto (fun k => (((Xd k)ᶜ.card + (Yd k)ᶜ.card : ℕ) : ℝ) /
      T.S.N (ψ k)) atTop (nhds 0) := by
    apply squeeze_zero (fun k => by positivity) (fun k => (hmSmall k).le)
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let D : Stage := ⟨T.S.comp ψ hψ, Xd, Yd, hsmallD⟩
  have hDX : ∀ k, Xd k ⊆ T.X (ψ k) := by
    intro k
    exact stateX_base (T := T) P k (m k)
  have hDY : ∀ k, Yd k ⊆ T.Y (ψ k) := by
    intro k
    exact stateY_base (T := T) P k (m k)
  have hRef : D.Refines T := by
    have hRemove : D.Refines (T.sub ψ hψ) := by
      exact Stage.Refines.remove (T.sub ψ hψ) Xd Yd hDX hDY hsmallD
    exact hRemove.trans (Stage.Refines.sub T ψ hψ)
  refine ⟨D, hRef, ?_⟩
  intro j
  let q := j + 1
  have hstatus : Available (stateSeq (T := T) P q).toStage (P j) ∨
      EventuallyAbsent (stateSeq (T := T) P q).toStage (P j) := by
    simpa [q, stateSeq_succ, StabState.after, StabState.toStage, stepStage,
      BadSeq.comp] using (stateStep (T := T) P j).status
  rcases hstatus with hav | habs
  · obtain ⟨κ, hκ, hav⟩ := hav
    have hsmallD' := tendsto_eventually_lt hsmallD (by linarith : 0 < κ / 2)
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hav
    obtain ⟨L, hL⟩ := Filter.eventually_atTop.1 hsmallD'
    let M := max q (max K L)
    left
    refine ⟨κ / 2, by positivity, ?_⟩
    have hIndexEvent : ∀ᶠ i in atTop, q ≤ i ∧ K ≤ i ∧ L ≤ i :=
      Filter.eventually_atTop.2 ⟨M, fun i hi =>
        ⟨(le_max_left q (max K L)).trans hi,
          (le_max_left K L).trans ((le_max_right q (max K L)).trans hi),
          (le_max_right K L).trans ((le_max_right q (max K L)).trans hi)⟩⟩
    filter_upwards [hIndexEvent] with i hi
    obtain ⟨hiq, hiK, hiL⟩ := hi
    intro RX RY hRX hRY
    let nDiag := i
    obtain ⟨d, hqd⟩ : ∃ d, q + d = i := ⟨i - q, Nat.add_sub_of_le hiq⟩
    have hsmallAt := hL i hiL
    have hKDiag : K ≤ nDiag := by dsimp [nDiag]; exact hiK
    cases hqd
    let l := tailMap (T := T) P q d (m nDiag)
    have hidx := stateIndex_tail (T := T) P q d (m nDiag)
    have hN : D.S.N nDiag = (stateSeq (T := T) P q).toStage.S.N l := by
      change T.S.N ((stateSeq (T := T) P nDiag).idx (m nDiag)) =
        T.S.N ((stateSeq (T := T) P q).idx l)
      exact congrArg T.S.N hidx
    have hl : K ≤ l := by
      have htail := strictMono_ge_id (tailMap_strict (T := T) P q d) (m nDiag)
      have hmge := strictMono_ge_id hm nDiag
      dsimp [l]
      omega
    have hgoodAt := hK l hl
    have hresult :
        ∃ A B, (A, B) ∈ P j (D.S.n nDiag) (D.S.N nDiag) (D.S.E nDiag) ∧
          A ⊆ D.X nDiag \ RX ∧ B ⊆ D.Y nDiag \ RY := by
      have hNpos : (0 : ℝ) < (stateSeq (T := T) P q).toStage.S.N l := by
        exact_mod_cast (stateSeq (T := T) P q).toStage.S.N_pos l
      have hε : (((D.X nDiag)ᶜ.card + (D.Y nDiag)ᶜ.card : ℕ) : ℝ) /
          (stateSeq (T := T) P q).toStage.S.N l < κ / 2 := by
        rw [← hN]
        exact hsmallAt
      let DXold := hN ▸ D.X nDiag
      let DYold := hN ▸ D.Y nDiag
      let extraX := (stateSeq (T := T) P q).X l \ DXold
      let extraY := (stateSeq (T := T) P q).Y l \ DYold
      have hcardExtra : (extraX.card + extraY.card) ≤
          DXoldᶜ.card + DYoldᶜ.card := by
        exact Nat.add_le_add (card_subset_compl_le DXold ((stateSeq (T := T) P q).X l))
          (card_subset_compl_le DYold ((stateSeq (T := T) P q).Y l))
      have hcardDX : DXoldᶜ.card = (D.X nDiag)ᶜ.card := by
        exact card_compl_finset_cast_host hidx hN (D.X nDiag)
      have hcardDY : DYoldᶜ.card = (D.Y nDiag)ᶜ.card := by
        exact card_compl_finset_cast_host hidx hN (D.Y nDiag)
      have hExtra : (((extraX.card + extraY.card : ℕ) : ℝ)) ≤
          (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := by
        have hreal : (((extraX.card + extraY.card : ℕ) : ℝ)) ≤
            (((D.X nDiag)ᶜ.card + (D.Y nDiag)ᶜ.card : ℕ) : ℝ) := by
          exact_mod_cast (by simpa [hcardDX, hcardDY] using hcardExtra)
        have hbound : (((D.X nDiag)ᶜ.card + (D.Y nDiag)ᶜ.card : ℕ) : ℝ) <
            (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := by
          exact (div_lt_iff₀ hNpos).1 hε
        linarith
      have hExtraX : (extraX.card : ℝ) ≤
          (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := by
        have hle : (extraX.card : ℝ) ≤ ((extraX.card + extraY.card : ℕ) : ℝ) := by
          push_cast
          exact le_add_of_nonneg_right (by positivity)
        exact le_trans hle hExtra
      have hExtraY : (extraY.card : ℝ) ≤
          (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := by
        have hle : (extraY.card : ℝ) ≤ ((extraX.card + extraY.card : ℕ) : ℝ) := by
          push_cast
          exact le_add_of_nonneg_left (by positivity)
        exact le_trans hle hExtra
      let RXold := (hN ▸ RX) ∪ extraX
      let RYold := (hN ▸ RY) ∪ extraY
      have hRXcast : ((hN ▸ RX).card : ℝ) = (RX.card : ℝ) := by
        exact_mod_cast card_finset_cast_host hidx hN RX
      have hRYcast : ((hN ▸ RY).card : ℝ) = (RY.card : ℝ) := by
        exact_mod_cast card_finset_cast_host hidx hN RY
      have hRXold : (RXold.card : ℝ) ≤ κ * (stateSeq (T := T) P q).toStage.S.N l := by
        have hcard : (RXold.card : ℝ) ≤ ((hN ▸ RX).card : ℝ) + (extraX.card : ℝ) := by
          exact_mod_cast Finset.card_union_le (hN ▸ RX) extraX
        have hRXbound : ((hN ▸ RX).card : ℝ) ≤
            (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := by
          calc
            ((hN ▸ RX).card : ℝ) = (RX.card : ℝ) := hRXcast
            _ ≤ (κ / 2) * D.S.N nDiag := hRX
            _ = (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := by rw [hN]
        calc
          (RXold.card : ℝ) ≤ ((hN ▸ RX).card : ℝ) + (extraX.card : ℝ) := hcard
          _ ≤ (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l +
              (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := add_le_add hRXbound hExtraX
          _ = κ * (stateSeq (T := T) P q).toStage.S.N l := by ring
      have hRYold : (RYold.card : ℝ) ≤ κ * (stateSeq (T := T) P q).toStage.S.N l := by
        have hcard : (RYold.card : ℝ) ≤ ((hN ▸ RY).card : ℝ) + (extraY.card : ℝ) := by
          exact_mod_cast Finset.card_union_le (hN ▸ RY) extraY
        have hRYbound : ((hN ▸ RY).card : ℝ) ≤
            (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := by
          calc
            ((hN ▸ RY).card : ℝ) = (RY.card : ℝ) := hRYcast
            _ ≤ (κ / 2) * D.S.N nDiag := hRY
            _ = (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := by rw [hN]
        calc
          (RYold.card : ℝ) ≤ ((hN ▸ RY).card : ℝ) + (extraY.card : ℝ) := hcard
          _ ≤ (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l +
              (κ / 2) * (stateSeq (T := T) P q).toStage.S.N l := add_le_add hRYbound hExtraY
          _ = κ * (stateSeq (T := T) P q).toStage.S.N l := by ring
      obtain ⟨A, B, hmem, hA, hB⟩ := hgoodAt RXold RYold hRXold hRYold
      exact transport_patch_witness hidx hN A B ((stateSeq (T := T) P q).X l)
        ((stateSeq (T := T) P q).Y l) (D.X nDiag) (D.Y nDiag) RX RY hmem hA hB
    exact hresult
  · obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 habs
    let M := max q K
    have hDabs : EventuallyAbsent D (P j) := by
      have hAbsEvent : ∀ᶠ i in atTop, q ≤ i ∧ K ≤ i :=
        Filter.eventually_atTop.2 ⟨M, fun i hi =>
          ⟨(le_max_left q K).trans hi, (le_max_right q K).trans hi⟩⟩
      filter_upwards [hAbsEvent] with i hi
      have hiq := hi.1
      let nDiag := i
      obtain ⟨d, hqd⟩ : ∃ d, q + d = i := ⟨i - q, Nat.add_sub_of_le hiq⟩
      have hKDiag : K ≤ nDiag := by dsimp [nDiag]; exact hi.2
      cases hqd
      let l := tailMap (T := T) P q d (m nDiag)
      have hl : K ≤ l := by
        have htail := strictMono_ge_id (tailMap_strict (T := T) P q d) (m nDiag)
        have hmge := strictMono_ge_id hm nDiag
        dsimp [l]
        omega
      have hidx := stateIndex_tail (T := T) P q d (m nDiag)
      have hN : D.S.N nDiag = (stateSeq (T := T) P q).toStage.S.N l := by
        change T.S.N ((stateSeq (T := T) P nDiag).idx (m nDiag)) =
          T.S.N ((stateSeq (T := T) P q).idx l)
        exact congrArg T.S.N hidx
      have hNestedX : D.X nDiag ⊆ hN.symm ▸ (stateSeq (T := T) P q).X l := by
        change (stateSeq (T := T) P (q + d)).X (m (q + d)) ⊆
          (congrArg T.S.N (stateIndex_tail (T := T) P q d (m (q + d))).symm ▸
            (stateSeq (T := T) P q).X (tailMap (T := T) P q d (m (q + d))))
        exact stateX_tail (T := T) P q d (m (q + d))
      have hNestedY : D.Y nDiag ⊆ hN.symm ▸ (stateSeq (T := T) P q).Y l := by
        change (stateSeq (T := T) P (q + d)).Y (m (q + d)) ⊆
          (congrArg T.S.N (stateIndex_tail (T := T) P q d (m (q + d))).symm ▸
            (stateSeq (T := T) P q).Y (tailMap (T := T) P q d (m (q + d))))
        exact stateY_tail (T := T) P q d (m (q + d))
      have hlocal := transport_patch_absence hidx hN (D.X nDiag) (D.Y nDiag)
        ((stateSeq (T := T) P q).X l) ((stateSeq (T := T) P q).Y l)
        hNestedX hNestedY (hK l hl)
      exact hlocal
    exact Or.inr hDabs

/-- Lemma 3.2, persistence of availability (with a smaller tolerance). -/
theorem Available.refine {T T' : Stage} {P : PatchProp} (h : Available T P)
    (hr : T'.Refines T) : Available T' P := by
  induction hr with
  | refl U => exact h
  | sub U φ hφ =>
      obtain ⟨κ, hκ, hav⟩ := h
      refine ⟨κ, hκ, ?_⟩
      have hav' := hφ.tendsto_atTop.eventually hav
      filter_upwards [hav'] with k hk RX RY hRX hRY
      exact hk RX RY hRX hRY
  | remove U X' Y' hX hY hsmall =>
      exact available_remove h hX hY hsmall
  | trans hAB hBC ihAB ihBC => exact ihAB (ihBC h)

/-- Absence persists under every refinement. -/
theorem EventuallyAbsent.refine {T T' : Stage} {P : PatchProp} (h : EventuallyAbsent T P)
    (hr : T'.Refines T) : EventuallyAbsent T' P := by
  induction hr with
  | refl U => exact h
  | sub U φ hφ =>
      have h' := hφ.tendsto_atTop.eventually h
      filter_upwards [h'] with k hk A B hmem hAB
      exact hk A B hmem hAB
  | remove U X' Y' hX hY hsmall =>
      filter_upwards [h] with k hk A B hmem hAB
      apply hk A B hmem
      exact ⟨Finset.Subset.trans hAB.1 (hX k), Finset.Subset.trans hAB.2 (hY k)⟩
  | trans hAB hBC ihAB ihBC => exact ihAB (ihBC h)

theorem Available.not_absent {T : Stage} {P : PatchProp} (h₁ : Available T P)
    (h₂ : EventuallyAbsent T P) : False := by
  obtain ⟨κ, hκ, hav⟩ := h₁
  have hboth : ∀ᶠ k in atTop, (∀ RX RY : Finset (Fin (T.S.N k)),
      (RX.card : ℝ) ≤ κ * T.S.N k → (RY.card : ℝ) ≤ κ * T.S.N k →
        ∃ A B, (A, B) ∈ P (T.S.n k) (T.S.N k) (T.S.E k) ∧
          A ⊆ T.X k \ RX ∧ B ⊆ T.Y k \ RY) ∧
      (∀ A B, (A, B) ∈ P (T.S.n k) (T.S.N k) (T.S.E k) →
        ¬ (A ⊆ T.X k ∧ B ⊆ T.Y k)) := hav.and h₂
  obtain ⟨k, ⟨havk, habsk⟩⟩ := hboth.exists
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  obtain ⟨A, B, hmem, hA, hB⟩ := havk ∅ ∅
    (by simpa using (le_of_lt (mul_pos hκ hN)))
    (by simpa using (le_of_lt (mul_pos hκ hN)))
  exact habsk A B hmem ⟨by simpa using hA, by simpa using hB⟩

/-- Lemma 3.2, finite unions: an available finite union has an available member after refinement. -/
theorem Available.union_fin {T : Stage} {m : ℕ} {P : Fin m → PatchProp}
    (h : Available T (PatchProp.union P)) :
    ∃ T', T'.Refines T ∧ ∃ i, Available T' (P i) := by
  classical
  let P' : ℕ → PatchProp := fun j => if hj : j < m then P ⟨j, hj⟩ else fun _ _ _ => ∅
  obtain ⟨T', hT, hstatus⟩ := stabilization T P'
  by_cases hm : m = 0
  · subst m
    obtain ⟨κ, hκ, hav⟩ := h
    obtain ⟨k, hk⟩ := hav.exists
    have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    obtain ⟨A, B, hmem, hA, hB⟩ := hk ∅ ∅
      (by simpa using (le_of_lt (mul_pos hκ hN)))
      (by simpa using (le_of_lt (mul_pos hκ hN)))
    change ∃ i : Fin 0, _ at hmem
    rcases hmem with ⟨i, hi⟩
    exact Fin.elim0 i
  · by_cases hSome : ∃ i : Fin m, Available T' (P i)
    · exact ⟨T', hT, hSome⟩
    · have hAbs : ∀ i : Fin m, EventuallyAbsent T' (P i) := by
        intro i
        rcases hstatus i.val with hav | habs
        · exact False.elim (hSome ⟨i, by simpa [P', i.isLt] using hav⟩)
        · simpa [P', i.isLt] using habs
      have hAll : ∀ᶠ k in atTop, ∀ i : Fin m, ∀ A B,
          (A, B) ∈ P i (T'.S.n k) (T'.S.N k) (T'.S.E k) →
            ¬ (A ⊆ T'.X k ∧ B ⊆ T'.Y k) := by
        apply eventually_fintype_forall
        intro i
        exact hAbs i
      have hUnionAbs : EventuallyAbsent T' (PatchProp.union P) := by
        filter_upwards [hAll] with k hk A B hmem
        obtain ⟨i, hi⟩ := hmem
        exact hk i A B hi
      have hUnionAv : Available T' (PatchProp.union P) := Available.refine h hT
      exact False.elim (Available.not_absent hUnionAv hUnionAbs)

/-- Lemma 3.2, finite menus: one witness per removal pair at each large index. -/
theorem Available.menu {T : Stage} {P : LawProp} (h : Available T P.toPatchProp) :
    ∃ κ > (0 : ℝ), ∀ᶠ k in atTop, ∃ w : Finset (Fin (T.S.N k)) × Finset (Fin (T.S.N k)) →
        Law (T.S.N k) × Law (T.S.N k),
      ∀ RX RY : Finset (Fin (T.S.N k)), (RX.card : ℝ) ≤ κ * T.S.N k → (RY.card : ℝ) ≤ κ * T.S.N k →
        w (RX, RY) ∈ P (T.S.n k) (T.S.N k) (T.S.E k) ∧
          (w (RX, RY)).1.SupportedIn (T.X k \ RX) ∧ (w (RX, RY)).2.SupportedIn (T.Y k \ RY) := by
  classical
  obtain ⟨κ, hκ, hav⟩ := h
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hav] with k hk
  let N := T.S.N k
  let default : Law N × Law N :=
    (Law.dirac ⟨0, T.S.N_pos k⟩, Law.dirac ⟨0, T.S.N_pos k⟩)
  have hpick : ∀ RX RY : Finset (Fin N),
      (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
      ∃ p ∈ P (T.S.n k) N (T.S.E k),
        p.1.SupportedIn (T.X k \ RX) ∧ p.2.SupportedIn (T.Y k \ RY) := by
    intro RX RY hRX hRY
    obtain ⟨A, B, hmem, hA, hB⟩ := hk RX RY hRX hRY
    change ∃ p ∈ P (T.S.n k) N (T.S.E k),
      p.1.SupportedIn A ∧ p.2.SupportedIn B at hmem
    obtain ⟨p, hp, hpA, hpB⟩ := hmem
    refine ⟨p, hp, ?_, ?_⟩
    · intro x hx
      apply hpA x
      intro hxA
      exact hx (hA hxA)
    · intro y hy
      apply hpB y
      intro hyB
      exact hy (hB hyB)
  let w : Finset (Fin N) × Finset (Fin N) → Law N × Law N := fun R =>
    if hR₁ : (R.1.card : ℝ) ≤ κ * N then
      if hR₂ : (R.2.card : ℝ) ≤ κ * N then Classical.choose (hpick R.1 R.2 hR₁ hR₂)
      else default
    else default
  refine ⟨w, ?_⟩
  intro RX RY hRX hRY
  have hw := Classical.choose_spec (hpick RX RY hRX hRY)
  simpa [w, hRX, hRY, N] using hw

end HypercubeRamsey
