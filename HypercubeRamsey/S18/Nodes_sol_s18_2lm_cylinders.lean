import HypercubeRamsey.S18.Nodes_sol_s18_2lm_iteration
import HypercubeRamsey.S18.Nodes_sol_fix_outsupp

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm.CylinderAdapter

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

private theorem pr_nonneg {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω) (A : Ω → Prop) :
    0 ≤ Q.pr A := by
  unfold FinLaw.pr
  exact Finset.sum_nonneg fun s _ => by split_ifs <;> simp [Q.nonneg]

private theorem pr_mono {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (A B : Ω → Prop) (h : ∀ s, A s → B s) : Q.pr A ≤ Q.pr B := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro s _
  by_cases ha : A s
  · simp [ha, h s ha]
  · simp only [ha, ↓reduceIte]
    split_ifs <;> simp [Q.nonneg]

/-- Conditioning on any positive whole-state event has the exact intersection
formula; locality is not needed until small-cylinder averaging. -/
theorem cond_probability {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (C : Finset Ω) (hC : 0 < ∑ s ∈ C, Q.w s) (A : Ω → Prop) :
    (FinLaw.cond Q C hC).pr A =
      Q.pr (fun s => s ∈ C ∧ A s) / (∑ s ∈ C, Q.w s) := by
  unfold FinLaw.pr FinLaw.cond
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hc : s ∈ C <;> by_cases ha : A s <;> simp [hc, ha]

/-- A finite injective selection of critical labels has independent
whole-cell marginals. This includes selections indexed by value prefixes. -/
theorem critical_family_probability {I : Type*} [Fintype I]
    (hgeom : TransferGeometry X) (a : I → Fin (T.S.n k))
    (ha : ∀ i, a i ∈ X.criticalCoords) (hinj : Function.Injective a)
    (ys : I → Fin (T.S.N k)) :
    X.rawLaw.pr (fun s => ∀ i, X.criticalLabel s (a i) = ys i) =
      ∏ i, (D.typicalFresh (D.geom.cellOf (flipPos X.target (a i)))).pr (fun Ps =>
        D.fresh.label (D.geom.cellOf (flipPos X.target (a i))) Ps.2 (flipPos X.target (a i)) = ys i) := by
  let H := fun i (s : X.Raw) => X.criticalLabel s (a i) = ys i
  let S := fun i => ({D.geom.cellOf (flipPos X.target (a i))} : Finset D.geom.Cell)
  have hlocal : ∀ i, ∀ s s', (∀ C ∈ S i, s C = s' C) → (H i s ↔ H i s') := by
    intro i s s' he
    have hcell := he _ (Finset.mem_singleton_self _)
    change (D.fresh.label _ (s _).2 _ = ys i) ↔ (D.fresh.label _ (s' _).2 _ = ys i)
    rw [hcell]
  have hdis : ∀ i i', i ≠ i' → Disjoint (S i) (S i') := by
    intro i i' hne
    apply Finset.disjoint_singleton.mpr
    intro he
    exact hne (hinj (hgeom.distinct_cells (a i) (ha i) (a i') (ha i') he))
  let factors := fun C => if C ∈ X.criticalCells then D.typicalFresh C
    else FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)
  have hprod := Blocks.pi_pr_all_disjoint factors H S Finset.univ
    (fun i _ => hlocal i) (fun i _ i' _ => hdis i i')
  change X.rawLaw.pr (fun s => ∀ i, H i s) = _
  have hall : (fun s => ∀ i, H i s) = (fun s => ∀ i ∈ (Finset.univ : Finset I), H i s) := by simp
  rw [hall]
  change ((FinLaw.pi factors).pr fun s => ∀ i ∈ Finset.univ, H i s) = _
  rw [hprod]
  apply Finset.prod_congr rfl
  intro i _
  have hmarg := Cylinder.critical_subset_event_probability hgeom {a i}
    (by intro b hb; have he := Finset.mem_singleton.mp hb; simpa [he] using ha i)
    (fun _ y => y = ys i)
  simpa only [Finset.mem_singleton, forall_eq, Finset.prod_singleton, H, CriticalTransferData.rawLaw, factors] using hmarg

/-- The label-prefix atom bound comes directly from the actual selected cells. -/
theorem critical_family_domination {I : Type*} [Fintype I]
    (hD : D.Spec) (hgeom : TransferGeometry X) (a : I → Fin (T.S.n k))
    (ha : ∀ i, a i ∈ X.criticalCoords) (hinj : Function.Injective a)
    (ys : I → Fin (T.S.N k)) :
    X.rawLaw.pr (fun s => ∀ i, X.criticalLabel s (a i) = ys i) ≤
      (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ Fintype.card I *
        ∏ i, (PT.π (D.geom.patchOf X.target)).w (ys i) := by
  rw [critical_family_probability hgeom a ha hinj]
  calc
    _ ≤ ∏ i, (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
        (PT.π (D.geom.patchOf X.target)).w (ys i) := Finset.prod_le_prod₀
      (fun i _ => pr_nonneg _ _) (fun i _ => Cylinder.critical_label_atom_domination hD (ha i) (ys i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

abbrev Prefix {m : ℕ} (j : Fin m) := {i : Fin m // i.val < j.val}

def prefixEquiv {m : ℕ} (j : Fin m) : Prefix j ≃ Fin j.val where
  toFun i := ⟨i.1.val, i.2⟩
  invFun i := ⟨⟨i.val, i.isLt.trans j.isLt⟩, i.isLt⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv i := by apply Fin.ext; rfl

noncomputable def prefixLaw {m N : ℕ} (π : Law N) (j : Fin m) :
    FinLaw (Prefix j → Fin N) :=
  FinLaw.pi fun _ => ⟨π.w, π.nonneg, π.sum_eq_one⟩

/-- Prefix and next-label joint domination under an actual whole-state
cylinder. Its scalar loss is the selected block density divided by mass. -/
theorem conditioned_prefix_domination {m : ℕ} (hκ : κ.Admissible)
    (hD : D.Spec) (hgeom : TransferGeometry X) (a : Fin m → Fin (T.S.n k))
    (ha : ∀ i, a i ∈ X.criticalCoords) (hinj : Function.Injective a)
    (C : Finset X.Raw) (hC : 0 < ∑ s ∈ C, X.rawLaw.w s)
    (j : Fin m) (v : Prefix j → Fin (T.S.N k)) (y : Fin (T.S.N k)) :
    (FinLaw.cond X.rawLaw C hC).pr (fun s =>
      (fun i : Prefix j => X.criticalLabel s (a i.1)) = v ∧ X.criticalLabel s (a j) = y) ≤
      ((1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ m / (∑ s ∈ C, X.rawLaw.w s)) *
        (prefixLaw (PT.π (D.geom.patchOf X.target)) j).w v *
        (PT.π (D.geom.patchOf X.target)).w y := by
  let b : Option (Prefix j) → Fin (T.S.n k) := fun i => match i with
    | none => a j
    | some i => a i.1
  let ys : Option (Prefix j) → Fin (T.S.N k) := fun i => match i with
    | none => y
    | some i => v i
  have hb : ∀ i, b i ∈ X.criticalCoords := by intro i; cases i <;> exact ha _
  have hbinj : Function.Injective b := by
    intro i i' he
    cases i with
    | none =>
      cases i' with
      | none => rfl
      | some i' =>
        have hh := hinj he
        have hhval := congrArg Fin.val hh
        have hlt := i'.2
        omega
    | some i =>
      cases i' with
      | none =>
        have hh := hinj he
        have hhval := congrArg Fin.val hh
        have hlt := i.2
        omega
      | some i' =>
        exact congrArg some (Subtype.ext (hinj he))
  have hevent : (fun s : X.Raw => (fun i : Prefix j => X.criticalLabel s (a i.1)) = v ∧
      X.criticalLabel s (a j) = y) = (fun s => ∀ i, X.criticalLabel s (b i) = ys i) := by
    funext s
    apply propext
    simp only [b, ys, Option.forall, funext_iff]
    exact and_comm
  have hd := critical_family_domination hD hgeom b hb hbinj ys
  have hcard : Fintype.card (Option (Prefix j)) = j.val + 1 := by
    rw [Fintype.card_option, Fintype.card_congr (prefixEquiv j), Fintype.card_fin]
  have hbase : 1 ≤ 1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3) := by
    have hKB : 0 ≤ κ.KB := (show (0 : ℝ) ≤ 10 ^ 6 * (κ.R : ℝ) by positivity).trans hκ.KB_big
    have h := mul_nonneg hKB (Real.rpow_nonneg (show (0 : ℝ) ≤ (T.S.n k : ℝ) from Nat.cast_nonneg _) (-3))
    simp only [Real.rpow_eq_pow] at *
    linarith
  have hpow := pow_le_pow_right₀ hbase (Nat.succ_le_of_lt j.isLt)
  rw [hcard, Fintype.prod_option] at hd
  have hd' : X.rawLaw.pr (fun s => ∀ i, X.criticalLabel s (b i) = ys i) ≤
      (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ m *
        (prefixLaw (PT.π (D.geom.patchOf X.target)) j).w v * (PT.π (D.geom.patchOf X.target)).w y := by
    have hm := mul_le_mul_of_nonneg_right hpow (show 0 ≤
      (PT.π (D.geom.patchOf X.target)).w y * ∏ i : Prefix j, (PT.π (D.geom.patchOf X.target)).w (v i) from
        mul_nonneg ((PT.π _).nonneg y) (Finset.prod_nonneg fun i _ => (PT.π _).nonneg (v i)))
    dsimp [ys, prefixLaw, FinLaw.pi] at *
    nlinarith only [hd, hm]
  rw [cond_probability]
  calc
    _ ≤ X.rawLaw.pr (fun s => (fun i : Prefix j => X.criticalLabel s (a i.1)) = v ∧
        X.criticalLabel s (a j) = y) / (∑ s ∈ C, X.rawLaw.w s) :=
      div_le_div_of_nonneg_right (pr_mono _ _ _ (fun _ h => h.2)) hC.le
    _ ≤ _ := by
      rw [hevent]
      have h := div_le_div_of_nonneg_right hd' hC.le
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- The existing quantitative cylinder theorem now accepts a block of the
actual critical labels, including any cylinder on the whole cell states. -/
theorem selected_survival_window {m : ℕ} {W : Type*} [Fintype W]
    (hκ : κ.Admissible) (hD : D.Spec) (hgeom : TransferGeometry X)
    (a : Fin m → Fin (T.S.n k)) (ha : ∀ i, a i ∈ X.criticalCoords) (hinj : Function.Injective a)
    (C : Finset X.Raw) (hC : 0 < ∑ s ∈ C, X.rawLaw.w s)
    (τ : FinLaw W) (H : W → Fin (T.S.N k) → Prop)
    (ε η u p b w : ℝ) (hε : 0 < ε) (hη : 0 ≤ η) (hu : 0 < u)
    (hp : 0 ≤ p ∧ p ≤ 1) (hb : 0 ≤ b) (hlo : 0 ≤ p - b) (hhi : p + b ≤ 1)
    (hπ : (PT.π (D.geom.patchOf X.target)).SupportedIn (T.Y k))
    (hπw : (PT.π (D.geom.patchOf X.target)).WidthLE w)
    (hcap : ∀ y, ((1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ m /
      (∑ s ∈ C, X.rawLaw.w s)) / ε * (PT.π (D.geom.patchOf X.target)).w y ≤
        Real.exp w / T.S.N k)
    (hdisc : ∀ U : Law (T.S.N k), U.SupportedIn (T.Y k) → U.WidthLE w →
      τ.pr (fun x => b < |U.pr (H x) - p|) ≤ η) :
    τ.pr (fun x => ¬ ((p - b) ^ m - m * u ≤
      (FinLaw.cond X.rawLaw C hC).pr (fun s => ∀ i, H x (X.criticalLabel s (a i))) ∧
      (FinLaw.cond X.rawLaw C hC).pr (fun s => ∀ i, H x (X.criticalLabel s (a i))) ≤
        (p + b) ^ m + m * u)) ≤ m * (ε + η) / u := by
  have hKB : 0 ≤ κ.KB := (show (0 : ℝ) ≤ 10 ^ 6 * (κ.R : ℝ) by positivity).trans hκ.KB_big
  have hbase0 : 0 ≤ 1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3) := by
    have hnr : 0 ≤ Real.rpow (T.S.n k : ℝ) (-3) := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_nonneg (show (0 : ℝ) ≤ (T.S.n k : ℝ) from Nat.cast_nonneg _) (-3)
    exact add_nonneg (by norm_num) (mul_nonneg hKB hnr)
  let g := fun i s => X.criticalLabel s (a i)
  let f := fun (j : Fin m) (s : X.Raw) (i : Prefix j) => g i.1 s
  let old := fun (j : Fin m) (v : Prefix j → Fin (T.S.N k)) (x : W) => ∀ i, H x (v i)
  have hOld : ∀ j s x, old j (f j s) x ↔ Cylinder.allHits g H x j.val s := by
    intro j s x
    exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.1 i.2⟩
  apply Cylinder.cylinder_survival_window (FinLaw.cond X.rawLaw C hC) τ _ (T.Y k)
    g f (fun j => prefixLaw (PT.π (D.geom.patchOf X.target)) j) old H
    _ ε η u p b w (div_nonneg (pow_nonneg hbase0 m) hC.le) hε hη hu hp hb hlo hhi hπ hπw hcap
    (fun j v y => conditioned_prefix_domination hκ hD hgeom a ha hinj C hC j v y) hOld hdisc

end HypercubeRamsey.S18.Lane_sol_s18_2lm.CylinderAdapter
