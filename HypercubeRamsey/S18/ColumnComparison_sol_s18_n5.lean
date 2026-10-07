import HypercubeRamsey.S18.ReachedComparison_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

/-- The actual guarded prefix comparison followed by the terminal
certificate on the constructed finite-resampling input test. -/
theorem guarded_prefix_terminal_comparison (D : LateData hPT) (hD : D.Spec) (hT : TransitionData D)
    {δ ε : ℝ} (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (j : Fin D.geom.r) (roots : Finset (Pos T k))
    (G : D.encoding.base.History j.castSucc → ℝ) (hG : ∀ h, 0 ≤ G h)
    (hlocalG : HistoryTestLocal D j.castSucc
      (rowCells D (ancestors roots 1)) (ancestors roots 1) G)
    (hquery : ∀ m, m ≤ D.geom.r + 1 →
      ((ancestors roots m).card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) ∧
      ((rowCells D (ancestors roots m)).card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3)) :
    (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
      (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
        (fun z => if reached D δ j z.2 then
          G (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) else 0) ≤
      (2 : ℝ) ^ D.geom.r * (1 + ε) * D.encoding.permLaw.E (fun x =>
        referenceTests D (fun full => G (D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt)))
          0 (D.encoding.base.initialHistory (D.encoding.initialState x))) := by
  let F := fun full : D.encoding.base.History (Fin.last D.geom.r) =>
    G (D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt))
  let Ψ := fun x : D.encoding.InitInput => referenceTests D F
    0 (D.encoding.base.initialHistory (D.encoding.initialState x))
  have hlocalF : HistoryTestLocal D (Fin.last D.geom.r)
      (rowCells D (ancestors roots 1)) (ancestors roots 1) F :=
    HistoryTestLocal.beforeHistory D j.castSucc _ _ _ _ G hlocalG
  have hΨ : ∀ x, 0 ≤ Ψ x := fun _ => referenceTests_nonneg D F (fun _ => hG _) 0 _
  have hc := C.comparison (rowCells D (ancestors roots (D.geom.r + 1)))
    (hquery _ le_rfl).2 Ψ hΨ (referenceTests_initial_input_local D hD hT roots F hlocalF)
  have hg := guarded_prefix_comparison D hD hT C A j roots G hG hlocalG
    (fun m hm => (hquery m hm).1)
  calc
    _ ≤ (2 : ℝ) ^ D.geom.r * (D.encoding.terminalLaw (terminalSet D δ) C.positive).E Ψ := hg
    _ ≤ (2 : ℝ) ^ D.geom.r * ((1 + ε) * D.encoding.permLaw.E Ψ) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by dsimp [Ψ, F]; ring

noncomputable def rowMassProduct (D : LateData hPT) (j : Fin D.geom.r) (m : ℕ)
    (s : Fin m → {b : Pos T k // b ∈ D.encoding.base.classes j}) (y : Fin (T.S.N k))
    (h : D.encoding.base.History j.castSucc) : ℝ :=
  ∏ i, (D.encoding.kernels.refK j (s i) h).pr (fun out => D.encoding.base.rowLabel out = y)

theorem rowMassProduct_nonneg (D : LateData hPT) (j : Fin D.geom.r) (m : ℕ)
    (s : Fin m → {b : Pos T k // b ∈ D.encoding.base.classes j}) (y : Fin (T.S.N k))
    (h : D.encoding.base.History j.castSucc) : 0 ≤ rowMassProduct D j m s y h := by
  apply Finset.prod_nonneg
  intro i _
  exact HypercubeRamsey.Lane_q_s17_res1.finLaw_pr_nonneg _ _

theorem rowMassProduct_local (D : LateData hPT) (hD : D.Spec) (hT : TransitionData D)
    (j : Fin D.geom.r) (m : ℕ)
    (s : Fin m → {b : Pos T k // b ∈ D.encoding.base.classes j}) (y : Fin (T.S.N k)) :
    let roots := Finset.univ.image (fun i => (s i).1)
    HistoryTestLocal D j.castSucc (rowCells D (ancestors roots 1)) (ancestors roots 1)
      (rowMassProduct D j m s y) := by
  intro roots
  apply HistoryTestLocal.mono D _ _ _ _ _ _ (column_product_local D hD hT j m s y)
  · exact rowCells_mono D (ancestors_step_subset roots 0)
  · intro b hb
    exact Finset.mem_union.mpr (Or.inr (pastPositions_subset_twoStep D j roots hb))

/-- The column-moment products now instantiate the guarded comparison with
their actual bounded queried rows and deterministic initial cell horizons. -/
theorem reached_column_products_eventually (κ : CConsts) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → ∀ δ ε : ℝ,
        ∀ C : TerminalCertificate D δ ε, ∀ A : ClassSamplerData D δ,
          ∀ j : Fin D.geom.r, ∀ m : ℕ, m ≤ T.S.n k →
            ∀ s : Fin m → {b : Pos T k // b ∈ D.encoding.base.classes j}, ∀ y : Fin (T.S.N k),
              (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
                (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
                  (fun z => if reached D δ j z.2 then
                    rowMassProduct D j m s y (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) else 0) ≤
              (2 : ℝ) ^ D.geom.r * (1 + ε) * D.encoding.permLaw.E (fun x =>
                referenceTests D (fun full => rowMassProduct D j m s y
                  (D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt)))
                    0 (D.encoding.base.initialHistory (D.encoding.initialState x))) := by
  filter_upwards [eventually_query_size κ T] with k hk
  intro PT hPT D hD hT δ ε C A j m hm s y
  let roots := Finset.univ.image (fun i => (s i).1)
  have hroots : roots.card ≤ T.S.n k := by
    have hc : roots.card ≤ m := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := fun i => (s i).1))
    exact hc.trans hm
  exact guarded_prefix_terminal_comparison D hD hT C A j roots _
    (rowMassProduct_nonneg D j m s y) (rowMassProduct_local D hD hT j m s y)
    (hk PT hPT D roots hroots)

end HypercubeRamsey.S18.Lane_sol_s18_n5
