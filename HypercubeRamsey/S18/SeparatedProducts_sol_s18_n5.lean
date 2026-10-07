import HypercubeRamsey.S18.HorizonPool_sol_s18_n5
import HypercubeRamsey.S18.RowMean_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem conditionalRowMass_local (D : LateData hPT) (hD : D.Spec) (hT : TransitionData D)
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (y : Fin (T.S.N k)) :
    HistoryTestLocal D j.castSucc (rowCells D (ancestors {b.1} 1)) (ancestors {b.1} 1)
      (fun h => (D.encoding.kernels.refK j b h).pr (fun out => D.encoding.base.rowLabel out = y)) := by
  have h := rowMassProduct_local D hD hT j 1 (fun _ => b) y
  have he : rowMassProduct D j 1 (fun _ => b) y =
      (fun h => (D.encoding.kernels.refK j b h).pr (fun out => D.encoding.base.rowLabel out = y)) := by
    funext h
    unfold rowMassProduct
    rw [Fin.prod_univ_succ]
    simp
  rw [he] at h
  simpa using h

theorem baseline_row_product_le (D : LateData hPT) (hD : D.Spec)
    (hT : TransitionData D) (hBalance : MaskBalance D) (j : Fin D.geom.r) (m : ℕ)
    (s : Fin m → {b : Pos T k // b ∈ D.encoding.base.classes j}) (y : Fin (T.S.N k))
    (hrows : ∀ i i', i ≠ i' → Disjoint
      (ancestors {(s i).1} (D.geom.r + 1)) (ancestors {(s i').1} (D.geom.r + 1)))
    (hcells : ∀ i i', i ≠ i' → Disjoint
      (D.expandCells (rowCells D (ancestors {(s i).1} (D.geom.r + 1))))
      (D.expandCells (rowCells D (ancestors {(s i').1} (D.geom.r + 1))))) :
    D.encoding.baseline.E (fun z => rowMassProduct D j m s y
      (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt))) ≤
      (2 / ((D.encoding.base.latePool j).card : ℝ)) ^ m := by
  let F := fun i (full : D.encoding.base.History (Fin.last D.geom.r)) =>
    (D.encoding.kernels.refK j (s i)
      (D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt))).pr
        (fun out => D.encoding.base.rowLabel out = y)
  have hF : ∀ i, HistoryTestLocal D (Fin.last D.geom.r)
      (rowCells D (ancestors {(s i).1} 1)) (ancestors {(s i).1} 1) (F i) := by
    intro i
    exact HistoryTestLocal.beforeHistory D j.castSucc _ _ _ _ _
      (conditionalRowMass_local D hD hT j (s i) y)
  have h := baseline_product_local D hD hT (fun i => {(s i).1}) F hF hrows hcells
  change D.encoding.baseline.E (fun z => ∏ i, F i z.2) ≤ _
  rw [h]
  calc
    _ ≤ ∏ _i : Fin m, (2 / ((D.encoding.base.latePool j).card : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg fun z _ => mul_nonneg (D.encoding.baseline.nonneg z)
          (HypercubeRamsey.Lane_q_s17_res1.finLaw_pr_nonneg _ _)
      · intro i _
        exact baseline_row_mean_le D hBalance j (s i) y
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Actual reached products transfer to the complete iid/resampling
baseline. The factor is independent of the number of queried rows. -/
theorem reached_column_baseline_eventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : LateData hPT), D.Spec → TransitionData D → ∀ δ ε : ℝ,
      ε ≤ 1 → ∀ C : TerminalCertificate D δ ε, ∀ A : ClassSamplerData D δ,
      ∀ j : Fin D.geom.r, ∀ m : ℕ, m ≤ T.S.n k →
      ∀ s : Fin m → {b : Pos T k // b ∈ D.encoding.base.classes j}, ∀ y : Fin (T.S.N k),
      (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
        (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
          (fun z => if reached D δ j z.2 then rowMassProduct D j m s y
            (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) else 0) ≤
      4 * (2 : ℝ) ^ D.geom.r * D.encoding.baseline.E (fun z => rowMassProduct D j m s y
        (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt))) := by
  filter_upwards [reached_column_products_eventually κ T, eventually_query_size κ T,
    perm_iid_horizon_comparison_eventually hκ T] with k ha hq hp
  intro PT hPT D hD hT δ ε hε C A j m hm s y
  let roots := Finset.univ.image fun i => (s i).1
  let F := fun full : D.encoding.base.History (Fin.last D.geom.r) =>
    rowMassProduct D j m s y (D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt))
  let Ψ := fun x : D.encoding.InitInput =>
    referenceTests D F 0 (D.encoding.base.initialHistory (D.encoding.initialState x))
  have hroots : roots.card ≤ T.S.n k :=
    (Finset.card_image_le.trans (by simp : (Finset.univ : Finset (Fin m)).card ≤ m)).trans hm
  have hsize := (hq PT hPT D roots hroots (D.geom.r + 1) le_rfl).2
  have hlocal := HistoryTestLocal.beforeHistory D j.castSucc (Fin.last D.geom.r) (Nat.le_of_lt j.isLt) _ _ _
    (rowMassProduct_local D hD hT j m s y)
  have hΨ : ∀ x, 0 ≤ Ψ x := fun x => referenceTests_nonneg D F
    (fun full => rowMassProduct_nonneg D j m s y _) 0 _
  have hpool := hp D hD _ hsize Ψ hΨ (referenceTests_initial_input_local D hD hT roots F hlocal)
  have hbase : (D.encoding.initialLaw D.encoding.iidLaw).E Ψ =
      D.encoding.baseline.E (fun z => F z.2) := (baseline_reference_test D F).symm
  rw [hbase] at hpool
  have hperm : 0 ≤ D.encoding.permLaw.E Ψ :=
    Finset.sum_nonneg fun x _ => mul_nonneg (D.encoding.permLaw.nonneg x) (hΨ x)
  have hact := ha PT hPT D hD hT δ ε C A j m hm s y
  change _ ≤ (2 : ℝ) ^ D.geom.r * (1 + ε) * D.encoding.permLaw.E Ψ at hact
  calc
    _ ≤ (2 : ℝ) ^ D.geom.r * (1 + ε) * D.encoding.permLaw.E Ψ := hact
    _ ≤ (2 : ℝ) ^ D.geom.r * 2 * D.encoding.permLaw.E Ψ := by
      gcongr
      linarith
    _ ≤ (2 : ℝ) ^ D.geom.r * 2 * (2 * D.encoding.baseline.E (fun z => F z.2)) :=
      mul_le_mul_of_nonneg_left hpool (by positivity)
    _ = _ := by dsimp [F]; ring

end HypercubeRamsey.S18.Lane_sol_s18_n5
