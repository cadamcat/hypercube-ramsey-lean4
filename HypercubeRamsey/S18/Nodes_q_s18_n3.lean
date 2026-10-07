import HypercubeRamsey.S18.Transfer
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace HypercubeRamsey.S18.Lane_q_s18_n3
open Classical

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

private theorem replies_length (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) :
    ∀ n, (P.replies seed s n).length = n := by
  intro n
  induction n with
  | zero => simp [P.replies_zero]
  | succ n ih => simp [P.replies_step, ih]

private theorem replies_take_prefix (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) :
    ∀ {i n}, i ≤ n → (P.replies seed s n).take i = P.replies seed s i := by
  intro i n hin
  induction n with
  | zero =>
      have : i = 0 := by omega
      subst i
      simp [P.replies_zero]
  | succ n ih =>
      rw [P.replies_step]
      by_cases hle : i ≤ n
      · rw [List.take_append_of_le_length (l₂ := [P.answer seed (P.replies seed s n) s])
          (by simpa [replies_length] using hle)]
        exact ih hle
      · have hi : i = n + 1 := by omega
        subst i
        simp [P.replies_step, replies_length]

private theorem replies_eq_of_path (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) :
    ∀ {n : ℕ} {tr : List P.Reply}, tr.length = n →
      (∀ i, i < n → P.answer seed (tr.take i) s = tr.getD i P.defaultReply) →
      P.replies seed s n = tr := by
  intro n
  induction n with
  | zero =>
      intro tr hlen _
      cases tr with
      | nil => simp [P.replies_zero]
      | cons r rs => simp at hlen
  | succ n ih =>
      intro tr hlen hpath
      have hpreLen : (tr.take n).length = n := by
        simp [List.length_take, Nat.min_eq_left (by omega : n ≤ tr.length)]
      have hprePath : ∀ i, i < n →
          P.answer seed ((tr.take n).take i) s = (tr.take n).getD i P.defaultReply := by
        intro i hi
        have hp := hpath i (by omega)
        have hget : (tr.take n)[i]? = tr[i]? := List.getElem?_take_of_lt (by omega)
        have hmin : min i n = i := Nat.min_eq_left (by omega)
        simpa [List.getD_eq_getElem?_getD, hget, List.take_take, hmin] using hp
      have hpre := ih hpreLen hprePath
      have hlast := hpath n (by omega)
      have htake : tr.take (n + 1) = tr.take n ++ [tr[n]] :=
        List.take_succ_eq_append_getElem (by omega)
      have hcut : tr.take (n + 1) = tr := List.take_of_length_le (by omega)
      calc
        P.replies seed s (n + 1) = P.replies seed s n ++
            [P.answer seed (P.replies seed s n) s] := P.replies_step seed s n
        _ = tr.take n ++ [tr.getD n P.defaultReply] := by rw [hpre, hlast]
        _ = tr.take (n + 1) := by
          rw [htake]
          rw [List.getD_eq_getElem tr P.defaultReply (by omega)]
        _ = tr := hcut

private theorem replies_eq_iff_path (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw)
    (n : ℕ) (tr : List P.Reply) :
    P.replies seed s n = tr ↔
      tr.length = n ∧ ∀ i, i < n →
        P.answer seed (tr.take i) s = tr.getD i P.defaultReply := by
  constructor
  · intro h
    have hlen : n = tr.length := by
      have hh := congrArg List.length h
      simpa [replies_length] using hh
    refine ⟨hlen.symm, ?_⟩
    intro i hi
    have hprefix : P.replies seed s (i + 1) = tr.take (i + 1) := by
      calc
        P.replies seed s (i + 1) = (P.replies seed s n).take (i + 1) :=
          (replies_take_prefix P seed s (by omega : i + 1 ≤ n)).symm
        _ = tr.take (i + 1) := by rw [h]
    have hidx := congrArg (fun l : List P.Reply => l[i]?) hprefix
    have hleft : (P.replies seed s (i + 1))[i]? =
        some (P.answer seed (P.replies seed s i) s) := by
      simp [P.replies_step, replies_length]
    have hright : (tr.take (i + 1))[i]? = some (tr.getD i P.defaultReply) := by
      rw [List.getElem?_take_of_succ, List.getElem?_eq_getElem (by omega)]
      rw [List.getD_eq_getElem tr P.defaultReply (by omega)]
    rw [hleft, hright] at hidx
    have hstate : P.replies seed s i = tr.take i := by
      calc
        P.replies seed s i = (P.replies seed s (i + 1)).take i :=
          (replies_take_prefix P seed s (by omega : i ≤ i + 1)).symm
        _ = (tr.take (i + 1)).take i := by rw [hprefix]
        _ = tr.take i := by simp [List.take_take]
    exact hstate ▸ Option.some.inj hidx
  · rintro ⟨hlen, hpath⟩
    exact replies_eq_of_path P seed s hlen hpath

private theorem finLaw_pi_pr_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (E : ∀ i, Ω i → Prop) :
    (FinLaw.pi P).pr (fun s => ∀ i, E i (s i)) =
      ∏ i, (P i).pr (E i) := by
  classical
  unfold FinLaw.pr FinLaw.pi
  have hpoint (s : ∀ i, Ω i) :
      (if ∀ i, E i (s i) then ∏ i, (P i).w (s i) else 0) =
        ∏ i, if E i (s i) then (P i).w (s i) else 0 := by
    by_cases h : ∀ i, E i (s i)
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hz : ∏ j, (if E j (s j) then (P j).w (s j) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      simp [h, hz]
  simp_rw [hpoint]
  exact (Fintype.prod_sum (fun i ω => if E i ω then (P i).w ω else 0)).symm

private theorem finLaw_pr_congr {α : Type*} [Fintype α]
    (P : FinLaw α) (A B : α → Prop) (h : ∀ x, A x ↔ B x) :
    P.pr A = P.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : A x
  · have hb : B x := (h x).mp ha
    simp [ha, hb]
  · have hb : ¬ B x := fun hb => ha ((h x).mpr hb)
    simp [ha, hb]

private theorem finLaw_pr_mono {α : Type*} [Fintype α]
    (P : FinLaw α) (A B : α → Prop) (h : ∀ x, A x → B x) :
    P.pr A ≤ P.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x
  · have hb : B x := h x ha
    simp [ha, hb]
  · by_cases hb : B x
    · simp [ha, hb, P.nonneg x]
    · simp [ha, hb]

private theorem finLaw_pr_compl {α : Type*} [Fintype α]
    (Q : FinLaw α) (A : α → Prop) :
    Q.pr A + Q.pr (fun x => ¬ A x) = 1 := by
  classical
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ x, Q.w x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : A x <;> simp [h]
    _ = 1 := Q.sum_one

private theorem finLaw_pr_eq_sum {α : Type*} [Fintype α]
    (Q : FinLaw α) (A : α → Prop) : Q.pr A = ∑ x, if A x then Q.w x else 0 := by
  classical
  unfold FinLaw.pr
  rfl

private theorem finLaw_pr_upper_of_atoms {α : Type*} [Fintype α]
    (Q π : FinLaw α) (c : ℝ) (hAtom : ∀ x, Q.w x ≤ c * π.w x)
    (B : α → Prop) : Q.pr B ≤ c * π.pr B := by
  classical
  unfold FinLaw.pr
  calc
    _ ≤ ∑ x, if B x then c * π.w x else 0 := by
          apply Finset.sum_le_sum
          intro x _
          by_cases h : B x
          · simpa [h] using hAtom x
          · simp [h]
    _ = c * (∑ x, if B x then π.w x else 0) := by
          calc
            (∑ x, if B x then c * π.w x else 0) =
                ∑ x, c * (if B x then π.w x else 0) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  by_cases h : B x <;> simp [h]
            _ = c * (∑ x, if B x then π.w x else 0) := by rw [Finset.mul_sum]

private theorem finLaw_pr_domination {α : Type*} [Fintype α]
    (Q π : FinLaw α) (c : ℝ)
    (hAtom : ∀ x, Q.w x ≤ c * π.w x) (A : α → Prop) :
    Q.pr A ≥ 1 - c * π.pr (fun x => ¬ A x) := by
  classical
  have htail := finLaw_pr_upper_of_atoms Q π c hAtom (fun x => ¬ A x)
  have hcompQ := finLaw_pr_compl Q A
  linarith

private theorem corr_false_eq_true {N : ℕ} (E : Fin N → Fin N → Prop)
    (μ : Fin N → ℝ) (x z : Fin N) : corr E false μ x z = corr E true μ x z := by
  classical
  unfold corr
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : E x y <;> by_cases h' : E z y <;>
    simp [fv, hit, Hits, h, h'] <;> ring

private theorem pairHitMass_identity {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (μ : Law N) (x z : Fin N) :
    (∑ y, μ.w y * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0)) =
      (deg E c μ.w x + deg E c μ.w z) / 2 - 1 / 4 +
        corr E c μ.w x z / 4 := by
  classical
  have hfx (v : Fin N) :
      (∑ y, μ.w y * fv E c v y) = 2 * deg E c μ.w v - 1 := by
    calc
      (∑ y, μ.w y * fv E c v y) =
          ∑ y, (2 * (μ.w y * hit E c v y) - μ.w y) := by
            apply Finset.sum_congr rfl
            intro y _
            simp [fv]
            ring
      _ = 2 * (∑ y, μ.w y * hit E c v y) - ∑ y, μ.w y := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * deg E c μ.w v - 1 := by simp [deg, μ.sum_eq_one]
  have hpoint (y : Fin N) :
      (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0) =
        (1 + fv E c x y + fv E c z y + fv E c x y * fv E c z y) / 4 := by
    by_cases hx : Hits E c x y <;> by_cases hz : Hits E c z y <;>
      simp [fv, hit, hx, hz] <;> ring
  calc
    (∑ y, μ.w y * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0)) =
        (∑ y, μ.w y *
          (1 + fv E c x y + fv E c z y + fv E c x y * fv E c z y)) / 4 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro y _
            rw [hpoint]
            ring
    _ = (∑ y, μ.w y + ∑ y, μ.w y * fv E c x y +
          ∑ y, μ.w y * fv E c z y +
          ∑ y, μ.w y * fv E c x y * fv E c z y) / 4 := by
            congr 1
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
            simp [mul_one, mul_assoc]
    _ = (deg E c μ.w x + deg E c μ.w z) / 2 - 1 / 4 +
          corr E c μ.w x z / 4 := by
            rw [μ.sum_eq_one, hfx x, hfx z]
            unfold corr
            ring

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

private theorem finLaw_mass_split {α : Type*} [Fintype α] (Q : FinLaw α) (A : α → Prop) :
    (∑ x, if A x then Q.w x else 0) + (∑ x, if A x then 0 else Q.w x) = 1 := by
  classical
  calc
    (∑ x, if A x then Q.w x else 0) + (∑ x, if A x then 0 else Q.w x) =
        ∑ x, ((if A x then Q.w x else 0) + (if A x then 0 else Q.w x)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ x, Q.w x := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : A x <;> simp [h]
    _ = 1 := Q.sum_one

private theorem finLaw_map_pr_local {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinLaw α) (f : α → β) (A : β → Prop) :
    (FinLaw.map P f).pr A = P.pr (fun x => A (f x)) := by
  classical
  unfold FinLaw.pr FinLaw.map
  have hterm (b : β) :
      (if A b then ∑ a, if f a = b then P.w a else 0 else 0) =
        ∑ a, if A b ∧ f a = b then P.w a else 0 := by
    by_cases hA : A b <;> simp [hA]
  calc
    (∑ b, if A b then ∑ a, if f a = b then P.w a else 0 else 0) =
        ∑ a, ∑ b, if A b ∧ f a = b then P.w a else 0 := by
          simp_rw [hterm]
          rw [Finset.sum_comm]
    _ = ∑ a, if A (f a) then P.w a else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : A (f a)
          · rw [Finset.sum_eq_single (f a)]
            · simp [h]
            · intro b _ hne
              by_cases hb : A b <;> simp [hb, Ne.symm hne]
            · intro hnot
              exact (hnot (Finset.mem_univ _)).elim
          · simp only [if_neg h]
            apply Finset.sum_eq_zero
            intro b _
            by_cases hEq : f a = b
            · subst b
              simp [h]
            · simp [hEq]

private theorem finLaw_map_mass_eq_pr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinLaw α) (f : α → β) (y : β) :
    (FinLaw.map P f).w y = P.pr (fun x => f x = y) := by
  classical
  unfold FinLaw.map FinLaw.pr
  apply Finset.sum_congr rfl
  intro x _
  let d₁ : Decidable (f x = y) := inferInstance
  let d₂ : Decidable (f x = y) := Classical.propDecidable _
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  change @ite ℝ (f x = y) d₁ (P.w x) 0 = @ite ℝ (f x = y) d₂ (P.w x) 0
  rw [hd]

private theorem typical_label_atom_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (hD : D.Spec) (b : Pos T k) (hodd : ¬ IsEvenRole b)
    (hclass : D.geom.classOf b = none) (y : Fin (T.S.N k)) :
    (FinLaw.map (D.typicalFresh (D.geom.cellOf b))
      (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b)).w y ≤
      (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
        (PT.π (D.geom.patchOf b)).w y := by
  rw [finLaw_map_mass_eq_pr]
  exact hD.fresh_singleton b hodd hclass y

private theorem fresh_label_hit_lower_single {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (hD : D.Spec) (b : Pos T k) (hodd : ¬ IsEvenRole b)
    (hclass : D.geom.classOf b = none) (x : Fin (T.S.N k))
    (hdeg : (1 / 2 : ℝ) - 1 / 100 ≤ deg (T.S.E k) PT.tiling.c
      (PT.π (D.geom.patchOf b)).w x)
    (hdelta : κ.KB * Real.rpow (T.S.n k : ℝ) (-3) ≤ 1 / 100) :
    (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps =>
      Hits (T.S.E k) PT.tiling.c x
        (D.fresh.label (D.geom.cellOf b) Ps.2 b)) ≥ 0.15 := by
  classical
  let Q : FinLaw (Fin (T.S.N k)) :=
    FinLaw.map (D.typicalFresh (D.geom.cellOf b))
      (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b)
  let π : Law (T.S.N k) := PT.π (D.geom.patchOf b)
  let πQ : FinLaw (Fin (T.S.N k)) := ⟨π.w, π.nonneg, π.sum_eq_one⟩
  let δ : ℝ := κ.KB * Real.rpow (T.S.n k : ℝ) (-3)
  let A : Fin (T.S.N k) → Prop := fun y => Hits (T.S.E k) PT.tiling.c x y
  have hAtom : ∀ y, Q.w y ≤ (1 + δ) * πQ.w y := by
    intro y
    have h := typical_label_atom_bound hD b hodd hclass y
    simpa [Q, πQ, π, δ] using h
  have hdom := finLaw_pr_domination Q πQ (1 + δ) (fun y => hAtom y) A
  have hmass : (∑ y, if A y then πQ.w y else 0) =
      deg (T.S.E k) PT.tiling.c π.w x := by
    calc
      (∑ y, if A y then πQ.w y else 0) =
          ∑ y, π.w y * (if A y then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases h : A y <;> simp [πQ, π, h]
      _ = deg (T.S.E k) PT.tiling.c π.w x := by
            simp [deg, hit, A]
  have hmassPr : πQ.pr A = deg (T.S.E k) PT.tiling.c π.w x := by
    rw [finLaw_pr_eq_sum]
    exact hmass
  have hπcomp : πQ.pr (fun y => ¬ A y) = 1 - deg (T.S.E k) PT.tiling.c π.w x := by
    have h := finLaw_pr_compl πQ A
    rw [hmassPr] at h
    linarith
  have hlarge :
      1 - (1 + δ) * (1 - deg (T.S.E k) PT.tiling.c π.w x) ≥ 0.15 := by
    have hKB : 0 ≤ κ.KB := le_trans
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10 ^ 6) (by positivity)) D.constants.KB_big
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      exact mul_nonneg hKB (Real.rpow_nonneg (by positivity) _)
    have hδle : δ ≤ 1 / 100 := by simpa [δ] using hdelta
    have hdnonneg : 0 ≤ deg (T.S.E k) PT.tiling.c π.w x := by
      unfold deg hit
      exact Finset.sum_nonneg fun y _ =>
        mul_nonneg (π.nonneg y) (by split_ifs <;> norm_num)
    rw [show (1 / 2 : ℝ) - 1 / 100 = 0.49 by norm_num] at hdeg
    nlinarith [mul_nonneg hδ hdnonneg]
  have hmap := finLaw_map_pr_local
    (D.typicalFresh (D.geom.cellOf b))
    (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b)
    A
  have hdom' : Q.pr A ≥ 1 - (1 + δ) * (1 - deg (T.S.E k) PT.tiling.c π.w x) := by
    rw [hπcomp] at hdom
    exact hdom
  calc
    (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps =>
        A (D.fresh.label (D.geom.cellOf b) Ps.2 b)) = Q.pr A := by
        symm
        exact hmap
    _ ≥ 1 - (1 + δ) * (1 - deg (T.S.E k) PT.tiling.c π.w x) := by
        exact hdom'
    _ ≥ 0.15 := hlarge

private theorem fresh_label_hit_lower_pair {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (hD : D.Spec) (b : Pos T k) (hodd : ¬ IsEvenRole b)
    (hclass : D.geom.classOf b = none) (x z : Fin (T.S.N k))
    (hdegx : (1 / 2 : ℝ) - 1 / 100 ≤ deg (T.S.E k) PT.tiling.c
      (PT.π (D.geom.patchOf b)).w x)
    (hdegz : (1 / 2 : ℝ) - 1 / 100 ≤ deg (T.S.E k) PT.tiling.c
      (PT.π (D.geom.patchOf b)).w z)
    (hcorr : |pairCorr (T.S.E k) true (PT.π (D.geom.patchOf b)) x z| ≤ 1 / 100)
    (hdelta : κ.KB * Real.rpow (T.S.n k : ℝ) (-3) ≤ 1 / 100) :
    (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps =>
      Hits (T.S.E k) PT.tiling.c x
        (D.fresh.label (D.geom.cellOf b) Ps.2 b) ∧
      Hits (T.S.E k) PT.tiling.c z
        (D.fresh.label (D.geom.cellOf b) Ps.2 b)) ≥ 0.15 := by
  classical
  let Q : FinLaw (Fin (T.S.N k)) :=
    FinLaw.map (D.typicalFresh (D.geom.cellOf b))
      (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b)
  let π : Law (T.S.N k) := PT.π (D.geom.patchOf b)
  let πQ : FinLaw (Fin (T.S.N k)) := ⟨π.w, π.nonneg, π.sum_eq_one⟩
  let δ : ℝ := κ.KB * Real.rpow (T.S.n k : ℝ) (-3)
  let A : Fin (T.S.N k) → Prop := fun y =>
    Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y
  have hAtom : ∀ y, Q.w y ≤ (1 + δ) * πQ.w y := by
    intro y
    have h := typical_label_atom_bound hD b hodd hclass y
    simpa [Q, πQ, π, δ] using h
  have hdom := finLaw_pr_domination Q πQ (1 + δ) (fun y => hAtom y) A
  have hmassPr : πQ.pr A =
      (deg (T.S.E k) PT.tiling.c π.w x + deg (T.S.E k) PT.tiling.c π.w z) / 2 - 1 / 4 +
        corr (T.S.E k) PT.tiling.c π.w x z / 4 := by
    unfold FinLaw.pr
    calc
      _ =
          ∑ y, π.w y *
            (if Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y
              then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases h : A y
            · have hp : Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y := by
                simpa [A] using h
              have hq : πQ.w y = π.w y := rfl
              simp [h, hp, π, hq]
            · have hp : ¬ (Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y) := by
                simpa [A] using h
              simp [h, hp]
      _ = _ := pairHitMass_identity (T.S.E k) PT.tiling.c π x z
  have hπcomp : πQ.pr (fun y => ¬ A y) =
      1 - ((deg (T.S.E k) PT.tiling.c π.w x + deg (T.S.E k) PT.tiling.c π.w z) / 2 -
        1 / 4 + corr (T.S.E k) PT.tiling.c π.w x z / 4) := by
    have h := finLaw_pr_compl πQ A
    rw [hmassPr] at h
    linarith
  have hcorr' : |corr (T.S.E k) PT.tiling.c π.w x z| ≤ 1 / 100 := by
    cases hc : PT.tiling.c with
    | false =>
        rw [corr_false_eq_true]
        simpa [pairCorr] using hcorr
    | true => simpa [pairCorr] using hcorr
  have hlarge :
      1 - (1 + δ) * (1 -
        ((deg (T.S.E k) PT.tiling.c π.w x + deg (T.S.E k) PT.tiling.c π.w z) / 2 -
          1 / 4 + corr (T.S.E k) PT.tiling.c π.w x z / 4)) ≥ 0.15 := by
    have hKB : 0 ≤ κ.KB := le_trans
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10 ^ 6) (by positivity)) D.constants.KB_big
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      exact mul_nonneg hKB (Real.rpow_nonneg (by positivity) _)
    have hδle : δ ≤ 1 / 100 := by simpa [δ] using hdelta
    have hcLo : -(1 / 100 : ℝ) ≤ corr (T.S.E k) PT.tiling.c π.w x z :=
      (abs_le.mp hcorr').1
    have hjoint : 1 / 4 - 1 / 100 - 1 / 400 ≤
        (deg (T.S.E k) PT.tiling.c π.w x + deg (T.S.E k) PT.tiling.c π.w z) / 2 -
          1 / 4 + corr (T.S.E k) PT.tiling.c π.w x z / 4 := by
      nlinarith [hdegx, hdegz, hcLo]
    have hjoint_nonneg : 0 ≤
        (deg (T.S.E k) PT.tiling.c π.w x + deg (T.S.E k) PT.tiling.c π.w z) / 2 -
          1 / 4 + corr (T.S.E k) PT.tiling.c π.w x z / 4 := by linarith
    nlinarith [mul_nonneg hδ hjoint_nonneg]
  have hmap := finLaw_map_pr_local
    (D.typicalFresh (D.geom.cellOf b))
    (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b) A
  have hdom' : Q.pr A ≥ 1 - (1 + δ) *
      (1 - ((deg (T.S.E k) PT.tiling.c π.w x + deg (T.S.E k) PT.tiling.c π.w z) / 2 -
        1 / 4 + corr (T.S.E k) PT.tiling.c π.w x z / 4)) := by
    have h := hdom
    rw [hπcomp] at h
    exact h
  calc
    (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps =>
        A (D.fresh.label (D.geom.cellOf b) Ps.2 b)) = Q.pr A :=
        hmap.symm
    _ ≥ 1 - (1 + δ) *
          (1 - ((deg (T.S.E k) PT.tiling.c π.w x + deg (T.S.E k) PT.tiling.c π.w z) / 2 -
            1 / 4 + corr (T.S.E k) PT.tiling.c π.w x z / 4)) := by
        exact hdom'
    _ ≥ 0.15 := hlarge

private theorem fresh_label_hit_upper_single {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (hD : D.Spec) (b : Pos T k) (hodd : ¬ IsEvenRole b)
    (hclass : D.geom.classOf b = none) (x : Fin (T.S.N k)) :
    (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps =>
      Hits (T.S.E k) PT.tiling.c x
        (D.fresh.label (D.geom.cellOf b) Ps.2 b)) ≤
      (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
        deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf b)).w x := by
  classical
  let Q : FinLaw (Fin (T.S.N k)) :=
    FinLaw.map (D.typicalFresh (D.geom.cellOf b))
      (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b)
  let π : Law (T.S.N k) := PT.π (D.geom.patchOf b)
  let πQ : FinLaw (Fin (T.S.N k)) := ⟨π.w, π.nonneg, π.sum_eq_one⟩
  let c : ℝ := 1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)
  let A : Fin (T.S.N k) → Prop := fun y => Hits (T.S.E k) PT.tiling.c x y
  have hAtom : ∀ y, Q.w y ≤ c * πQ.w y := by
    intro y
    have h := typical_label_atom_bound hD b hodd hclass y
    simpa [Q, πQ, π, c] using h
  have hmassPr : πQ.pr A = deg (T.S.E k) PT.tiling.c π.w x := by
    unfold FinLaw.pr
    calc
      _ = ∑ y, π.w y * (if Hits (T.S.E k) PT.tiling.c x y then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases h : A y <;> simp [A, πQ, π, h]
      _ = _ := by simp [deg, hit, π]
  have hmap := finLaw_map_pr_local (D.typicalFresh (D.geom.cellOf b))
    (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b) A
  calc
    (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps => A
        (D.fresh.label (D.geom.cellOf b) Ps.2 b)) = Q.pr A := hmap.symm
    _ ≤ c * deg (T.S.E k) PT.tiling.c π.w x := by
      have h := finLaw_pr_upper_of_atoms Q πQ c hAtom A
      simpa [hmassPr] using h

private theorem fresh_label_hit_upper_pair {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (hD : D.Spec) (b : Pos T k) (hodd : ¬ IsEvenRole b)
    (hclass : D.geom.classOf b = none) (x z : Fin (T.S.N k)) :
    (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps =>
      Hits (T.S.E k) PT.tiling.c x (D.fresh.label (D.geom.cellOf b) Ps.2 b) ∧
      Hits (T.S.E k) PT.tiling.c z (D.fresh.label (D.geom.cellOf b) Ps.2 b)) ≤
      (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
        ((deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf b)).w x +
          deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf b)).w z) / 2 - 1 / 4 +
          corr (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf b)).w x z / 4) := by
  classical
  let Q : FinLaw (Fin (T.S.N k)) :=
    FinLaw.map (D.typicalFresh (D.geom.cellOf b))
      (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b)
  let π : Law (T.S.N k) := PT.π (D.geom.patchOf b)
  let πQ : FinLaw (Fin (T.S.N k)) := ⟨π.w, π.nonneg, π.sum_eq_one⟩
  let c : ℝ := 1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)
  let A : Fin (T.S.N k) → Prop := fun y =>
    Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y
  have hAtom : ∀ y, Q.w y ≤ c * πQ.w y := by
    intro y
    have h := typical_label_atom_bound hD b hodd hclass y
    simpa [Q, πQ, π, c] using h
  have hmassPr : πQ.pr A =
      (deg (T.S.E k) PT.tiling.c π.w x + deg (T.S.E k) PT.tiling.c π.w z) / 2 - 1 / 4 +
        corr (T.S.E k) PT.tiling.c π.w x z / 4 := by
    unfold FinLaw.pr
    calc
      _ = ∑ y, π.w y *
          (if Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y
            then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro y _
              by_cases h : A y
              · have hp : Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y := by
                  simpa [A] using h
                have hq : πQ.w y = π.w y := rfl
                simp [h, hp, π, hq]
              · have hp : ¬ (Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y) := by
                  simpa [A] using h
                simp [h, hp, π]
      _ = _ := pairHitMass_identity (T.S.E k) PT.tiling.c π x z
  have hmap := finLaw_map_pr_local (D.typicalFresh (D.geom.cellOf b))
    (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b) A
  calc
    (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps => A
        (D.fresh.label (D.geom.cellOf b) Ps.2 b)) = Q.pr A := hmap.symm
    _ ≤ c * ((deg (T.S.E k) PT.tiling.c π.w x + deg (T.S.E k) PT.tiling.c π.w z) / 2 -
        1 / 4 + corr (T.S.E k) PT.tiling.c π.w x z / 4) := by
      have h := finLaw_pr_upper_of_atoms Q πQ c hAtom A
      simpa [hmassPr] using h

private theorem finLaw_pr_nonneg {α : Type*} [Fintype α]
    (Q : FinLaw α) (A : α → Prop) : 0 ≤ Q.pr A := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_nonneg
  intro x _
  by_cases h : A x <;> simp [h, Q.nonneg x]

private theorem finLaw_pr_true {α : Type*} [Fintype α] (Q : FinLaw α) :
    Q.pr (fun _ => True) = 1 := by
  classical
  simp [FinLaw.pr, Q.sum_one]

private theorem finLaw_pr_le_one {α : Type*} [Fintype α]
    (Q : FinLaw α) (A : α → Prop) : Q.pr A ≤ 1 := by
  have h := finLaw_pr_compl Q A
  have hc := finLaw_pr_nonneg Q (fun x => ¬ A x)
  linarith

private theorem finLaw_pr_filter {α : Type*} [Fintype α]
    (P : FinLaw α) (A : α → Prop) :
    P.pr A = ∑ x ∈ Finset.univ.filter A, P.w x := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_filter]

private theorem finLaw_pr_mul_cond {α : Type*} [Fintype α]
    (P : FinLaw α) (A B : α → Prop)
    (h : 0 < ∑ x ∈ Finset.univ.filter A, P.w x) :
    P.pr A * (FinLaw.cond P (Finset.univ.filter A) h).pr B =
      P.pr (fun x => A x ∧ B x) := by
  classical
  rw [finLaw_pr_filter, FinLaw.pr, FinLaw.pr, FinLaw.cond]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hA : A x <;> by_cases hB : B x
  · have hne : (∑ x ∈ Finset.univ.filter A, P.w x) ≠ 0 := ne_of_gt h
    simp [hA, hB, Finset.mem_filter]
    field_simp
  · simp [hA, hB, Finset.mem_filter]
  · simp [hA, hB, Finset.mem_filter]
  · simp [hA, hB, Finset.mem_filter]

private theorem finLaw_bind_pr_pair_event {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (A : α → Prop) (B : β → α → Prop) :
    (FinLaw.bind P (fun _ => Q)).pr (fun ab => A ab.1 ∧ B ab.2 ab.1) =
      ∑ b, Q.w b * P.pr (fun a => A a ∧ B b a) := by
  classical
  simp only [finLaw_pr_eq_sum]
  simp only [FinLaw.bind]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Prod.fst, Prod.snd]
  calc
    (∑ b, ∑ a, if A a ∧ B b a then P.w a * Q.w b else 0) =
        ∑ b, Q.w b * ∑ a, if A a ∧ B b a then P.w a else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          calc
            (∑ a, if A a ∧ B b a then P.w a * Q.w b else 0) =
                ∑ a, Q.w b * (if A a ∧ B b a then P.w a else 0) := by
                  apply Finset.sum_congr rfl
                  intro a _
                  by_cases h : A a ∧ B b a <;> simp [h, mul_comm]
            _ = Q.w b * ∑ a, if A a ∧ B b a then P.w a else 0 := by
                  rw [Finset.mul_sum]
    _ = ∑ b, Q.w b * P.pr (fun a => A a ∧ B b a) := by
          apply Finset.sum_congr rfl
          intro b _
          have hsum : (∑ a, if A a ∧ B b a then P.w a else 0) =
              P.pr (fun a => A a ∧ B b a) := by
            unfold FinLaw.pr
            apply Finset.sum_congr rfl
            intro a _
            by_cases h : A a ∧ B b a <;> simp [h]
          exact congrArg (fun q => Q.w b * q) hsum

private theorem finLaw_pr_exists_le_sum {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (P : FinLaw Ω) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  simp only [finLaw_pr_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hex : ∃ i, A i ω
  · obtain ⟨i, hi⟩ := hex
    have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
        0 ≤ if A j ω then P.w ω else 0 := by
      intro j _
      by_cases h : A j ω
      · simp [h, P.nonneg]
      · simp [h]
    have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ i)
    have hex' : ∃ j, A j ω := ⟨i, hi⟩
    rw [if_pos hex']
    calc
      P.w ω = if A i ω then P.w ω else 0 := (if_pos hi).symm
      _ ≤ ∑ j, if A j ω then P.w ω else 0 := hsingle
  · have hall : ∀ i, ¬ A i ω := fun i hi => hex ⟨i, hi⟩
    simp [hall]

private theorem finLaw_pr_or_le {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (A B : Ω → Prop) :
    P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  have h := finLaw_pr_exists_le_sum P (fun b : Bool => fun ω => if b then B ω else A ω)
  simpa [add_comm] using h

private theorem finset_sum_weighted_swap {α β : Type*} [Fintype α] [Fintype β]
    (w : β → ℝ) (f : α → β → ℝ) :
    (∑ a, ∑ b, w b * f a b) = ∑ b, w b * ∑ a, f a b := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.mul_sum]

private theorem finset_sum_univ_eq_of_support {α : Type*} [Fintype α]
    (S : Finset α) (f : α → ℝ) (hzero : ∀ x, x ∉ S → f x = 0) :
    (∑ x, f x) = ∑ x ∈ S, f x := by
  classical
  have hsub : (∑ x ∈ S, f x) = ∑ x, f x := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro x _ hx
    exact hzero x hx
  exact hsub.symm

private theorem transfer_bad_event_union_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) :
    (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
      ∃ x z, X.allowed x z ∧ X.survives ss.1 x z ∧
        X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x z) ≤
      (∑ x, (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
        X.survives ss.1 x none ∧ X.allowed x none ∧
          X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x none)) +
      ∑ x, ∑ y, (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
        X.survives ss.1 x (some y) ∧ X.allowed x (some y) ∧
          X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x (some y)) := by
  classical
  let Ω := X.Raw × P.Seed
  let Q : FinLaw Ω := FinLaw.bind X.rawLaw (fun _ => P.seedLaw)
  let bad (ss : Ω) : Prop := ∃ x z, X.allowed x z ∧ X.survives ss.1 x z ∧
    X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x z
  let single (x : Fin (T.S.N k)) (ss : Ω) : Prop :=
    X.survives ss.1 x none ∧ X.allowed x none ∧
      X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x none
  let pair (x y : Fin (T.S.N k)) (ss : Ω) : Prop :=
    X.survives ss.1 x (some y) ∧ X.allowed x (some y) ∧
      X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x (some y)
  have hcover : ∀ ss, bad ss → (∃ x, single x ss) ∨ ∃ p : Fin (T.S.N k) × Fin (T.S.N k),
      pair p.1 p.2 ss := by
    intro ss h
    obtain ⟨x, z, hallowed, hsurv, hdev⟩ := h
    cases z with
    | none => exact Or.inl ⟨x, hsurv, hallowed, hdev⟩
    | some y => exact Or.inr ⟨(x, y), hsurv, hallowed, hdev⟩
  have hsum : Q.pr bad ≤
      Q.pr (fun ss => ∃ x, single x ss) +
        Q.pr (fun ss => ∃ p : Fin (T.S.N k) × Fin (T.S.N k), pair p.1 p.2 ss) := by
    calc
      Q.pr bad ≤ Q.pr (fun ss => (∃ x, single x ss) ∨
          ∃ p : Fin (T.S.N k) × Fin (T.S.N k), pair p.1 p.2 ss) :=
        finLaw_pr_mono Q bad _ hcover
      _ ≤ _ := finLaw_pr_or_le Q _ _
  have hsingle := finLaw_pr_exists_le_sum Q single
  have hpair := finLaw_pr_exists_le_sum Q (fun p : Fin (T.S.N k) × Fin (T.S.N k) =>
    pair p.1 p.2)
  have hfinal : Q.pr bad ≤
      (∑ x, Q.pr (single x)) + ∑ x, ∑ y, Q.pr (fun ss => pair x y ss) := by
    calc
      Q.pr bad ≤ Q.pr (fun ss => ∃ x, single x ss) +
          Q.pr (fun ss => ∃ p : Fin (T.S.N k) × Fin (T.S.N k), pair p.1 p.2 ss) := hsum
      _ ≤ (∑ x, Q.pr (single x)) + ∑ p : Fin (T.S.N k) × Fin (T.S.N k),
          Q.pr (fun ss => pair p.1 p.2 ss) := add_le_add hsingle hpair
      _ = (∑ x, Q.pr (single x)) + ∑ x, ∑ y, Q.pr (fun ss => pair x y ss) := by
          congr 1
          rw [Fintype.sum_prod_type]
  simpa [Q, bad, single, pair] using hfinal

private theorem finLaw_pr_and_const {α : Type*} [Fintype α]
    (P : FinLaw α) (c : Prop) (B : α → Prop) :
    P.pr (fun x => c ∧ B x) = if c then P.pr B else 0 := by
  classical
  by_cases h : c
  · simp [h]
  · simp [h, FinLaw.pr]

private theorem tiltedLaw_pr_eq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (x : Fin (T.S.N k))
    (z : Option (Fin (T.S.N k))) (B : X.Raw → Prop) :
    let good := Finset.univ.filter (fun s : X.Raw => X.survives s x z)
    (tiltedLaw X x z).pr B =
      if h : 0 < ∑ s ∈ good, X.rawLaw.w s then
        (FinLaw.cond X.rawLaw good h).pr B else X.rawLaw.pr B := by
  classical
  dsimp only
  unfold tiltedLaw
  by_cases h : 0 < ∑ s ∈ Finset.univ.filter (fun s : X.Raw => X.survives s x z),
      X.rawLaw.w s
  · simp only [dif_pos h]
  · simp only [dif_neg h]

private theorem tilted_pr_mul_survives {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (x : Fin (T.S.N k))
    (z : Option (Fin (T.S.N k))) (B : X.Raw → Prop) :
    X.rawLaw.pr (fun s => X.survives s x z) * (tiltedLaw X x z).pr B =
      X.rawLaw.pr (fun s => X.survives s x z ∧ B s) := by
  classical
  let S : X.Raw → Prop := fun s => X.survives s x z
  let p := X.rawLaw.pr S
  let good := Finset.univ.filter (fun s : X.Raw => X.survives s x z)
  have hpRewrite : X.rawLaw.pr (fun s => X.survives s x z) = X.rawLaw.pr S := by
    apply finLaw_pr_congr
    intro s
    rfl
  have hrightRewrite : X.rawLaw.pr (fun s => X.survives s x z ∧ B s) =
      X.rawLaw.pr (fun s => S s ∧ B s) := by
    apply finLaw_pr_congr
    intro s
    rfl
  rw [hpRewrite, hrightRewrite]
  have hden : (∑ s ∈ good, X.rawLaw.w s) = p := by
    simpa [good, p, S] using (finLaw_pr_filter X.rawLaw S).symm
  rw [tiltedLaw_pr_eq X x z B]
  by_cases hp : 0 < p
  · have hgood : 0 < ∑ s ∈ good, X.rawLaw.w s := by rw [hden]; exact hp
    rw [dif_pos hgood]
    have hcond := finLaw_pr_mul_cond X.rawLaw S B (by simpa [good] using hgood)
    exact hcond
  · have hp0 : p = 0 := le_antisymm (le_of_not_gt hp) (finLaw_pr_nonneg X.rawLaw S)
    have hzero : X.rawLaw.pr (fun s => S s ∧ B s) = 0 := by
      apply le_antisymm
      · exact (finLaw_pr_mono X.rawLaw (fun s => S s ∧ B s) S
          (fun _ h => h.1)).trans (le_of_eq hp0)
      · exact finLaw_pr_nonneg X.rawLaw _
    have hnotGood : ¬ 0 < ∑ s ∈ good, X.rawLaw.w s := by
      rw [hden, hp0]
      exact not_lt.mpr le_rfl
    have hpS : X.rawLaw.pr S = 0 := hp0
    rw [dif_neg hnotGood, hpS, hzero]
    ring

private theorem transfer_witness_pr_tilt {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) :
    (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
      X.survives ss.1 x z ∧ X.allowed x z ∧
        X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x z) =
      ∑ seed, P.seedLaw.w seed *
        (X.rawLaw.pr (fun s => X.survives s x z) *
          ((tiltedLaw X x z).pr (fun s => X.allowed x z ∧
            X.deviates (P.output seed (P.replies seed s P.steps)) x z))) := by
  classical
  let Q : FinLaw (X.Raw × P.Seed) := FinLaw.bind X.rawLaw (fun _ => P.seedLaw)
  have hbind := finLaw_bind_pr_pair_event X.rawLaw P.seedLaw
    (fun s => X.survives s x z)
    (fun seed s => X.allowed x z ∧
      X.deviates (P.output seed (P.replies seed s P.steps)) x z)
  calc
    _ = ∑ seed, P.seedLaw.w seed * X.rawLaw.pr (fun s =>
        X.survives s x z ∧ X.allowed x z ∧
          X.deviates (P.output seed (P.replies seed s P.steps)) x z) := by
          simpa [Q] using hbind
    _ = _ := by
          apply Finset.sum_congr rfl
          intro seed _
          rw [← tilted_pr_mul_survives X x z
            (fun s => X.allowed x z ∧
              X.deviates (P.output seed (P.replies seed s P.steps)) x z)]

private theorem finish_single_cauchy_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) (c : ℝ)
    (hSurv : SurvivalFacts X) (hTilt : TiltedDeviationBound P c) (seed : P.Seed) :
    (∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
      if X.allowed x none then
        ((2 : ℝ) ^ X.criticalCoords.card * X.rawLaw.pr (fun s => X.survives s x none)) *
          (tiltedLaw X x none).pr (fun s =>
            X.deviates (P.output seed (P.replies seed s P.steps)) x none)
      else 0) ^ 2 ≤
      ((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) ^ 2 *
        Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) *
          Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
  classical
  let i := D.geom.patchOf X.target
  let patch := (PT.tiling.P i).X
  let M : ℝ := (PT.tiling.P i).M
  let p : Fin (T.S.N k) → ℝ := fun x =>
    X.rawLaw.pr (fun s => X.survives s x none)
  let q : Fin (T.S.N k) → ℝ := fun x =>
    (tiltedLaw X x none).pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x none)
  let f : Fin (T.S.N k) → ℝ := fun x =>
    if X.allowed x none then (2 : ℝ) ^ X.criticalCoords.card * p x else 0
  let g : Fin (T.S.N k) → ℝ := fun x => if X.allowed x none then q x else 0
  have hX : (PT.tiling.P i).X.Nonempty := hPT.tiling_valid.patch_nonempty i |>.1
  have hMpos : 0 < M := by
    dsimp [M]
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast (Finset.card_pos.mpr hX)
  have hAeq : (∑ x ∈ patch, f x ^ 2) =
      ∑ x ∈ patch, if X.allowed x none then
        ((2 : ℝ) ^ X.criticalCoords.card * p x) ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : X.allowed x none <;> simp [f, h]
  have hAdiv :
      (∑ x ∈ patch, if X.allowed x none then
        ((2 : ℝ) ^ X.criticalCoords.card * p x) ^ 2 else 0) / M ≤
        Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) := by
    simpa [patch, M, p, i] using hSurv.2.1
  have hA : (∑ x ∈ patch, f x ^ 2) ≤
      M * Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) := by
    rw [← hAeq] at hAdiv
    simpa [mul_comm] using (div_le_iff₀ hMpos).1 hAdiv
  have hq_nonneg (x : Fin (T.S.N k)) : 0 ≤ q x := by
    exact finLaw_pr_nonneg (tiltedLaw X x none)
      (fun s => X.deviates (P.output seed (P.replies seed s P.steps)) x none)
  have hq_le (x : Fin (T.S.N k)) : q x ≤ 1 := by
    exact finLaw_pr_le_one (tiltedLaw X x none)
      (fun s => X.deviates (P.output seed (P.replies seed s P.steps)) x none)
  have hBsmall : (∑ x ∈ patch, g x ^ 2) ≤
      ∑ x ∈ patch, if X.allowed x none then q x else 0 := by
    apply Finset.sum_le_sum
    intro x _
    by_cases h : X.allowed x none
    · have hq := mul_nonneg (hq_nonneg x) (sub_nonneg.mpr (hq_le x))
      have hsq : q x ^ 2 ≤ q x := by nlinarith [hq]
      simpa [g, h] using hsq
    · simp [g, h]
  have hBdiv :
      (∑ x ∈ patch, if X.allowed x none then q x else 0) / M ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
    simpa [q, patch, i] using (hTilt seed).1
  have hB : (∑ x ∈ patch, g x ^ 2) ≤
      M * Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
    have hBg := (div_le_iff₀ hMpos).1 hBdiv
    exact hBsmall.trans (by simpa [mul_comm] using hBg)
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq patch f g
  have hsum : (∑ x ∈ patch, f x * g x) =
      ∑ x ∈ patch, if X.allowed x none then
        ((2 : ℝ) ^ X.criticalCoords.card * p x) * q x else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : X.allowed x none <;> simp [f, g, h]
  have hC :
      (∑ x ∈ patch, if X.allowed x none then
        ((2 : ℝ) ^ X.criticalCoords.card * p x) * q x else 0) ^ 2 ≤
      (M * Real.exp (κ.KB * Real.log (T.S.n k : ℝ))) *
          (M * Real.exp (-Real.rpow (T.S.n k : ℝ) c)) := by
    rw [hsum] at hCauchy
    have hGnonneg : 0 ≤ ∑ x ∈ patch, g x ^ 2 :=
      Finset.sum_nonneg fun x hx => sq_nonneg (g x)
    have hAupper : 0 ≤ M * Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) := by positivity
    have hstep1 := mul_le_mul_of_nonneg_right hA hGnonneg
    have hstep2 := mul_le_mul_of_nonneg_left hB hAupper
    exact hCauchy.trans (hstep1.trans hstep2)
  simpa [M, patch, i, p, q, pow_two, mul_assoc, mul_left_comm, mul_comm] using hC

set_option maxHeartbeats 500000 in
private theorem finish_pair_cauchy_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) (c : ℝ)
    (hSurv : SurvivalFacts X) (hTilt : TiltedDeviationBound P c) (seed : P.Seed) :
    (∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
      ∑ y ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
        if X.allowed x (some y) then
          ((4 : ℝ) ^ X.criticalCoords.card *
            X.rawLaw.pr (fun s => X.survives s x (some y))) *
              (tiltedLaw X x (some y)).pr (fun s =>
                X.deviates (P.output seed (P.replies seed s P.steps)) x (some y))
        else 0) ^ 2 ≤
      (((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) ^ 2 *
        Real.exp (κ.KB * Real.log (T.S.n k : ℝ))) *
      (((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) ^ 2 *
        Real.exp (-Real.rpow (T.S.n k : ℝ) c)) := by
  classical
  let i := D.geom.patchOf X.target
  let patch := (PT.tiling.P i).X
  let prodPatch := patch ×ˢ patch
  let M : ℝ := (PT.tiling.P i).M
  let p : Fin (T.S.N k) → Fin (T.S.N k) → ℝ := fun x y =>
    X.rawLaw.pr (fun s => X.survives s x (some y))
  let q : Fin (T.S.N k) → Fin (T.S.N k) → ℝ := fun x y =>
    (tiltedLaw X x (some y)).pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x (some y))
  let f : Fin (T.S.N k) × Fin (T.S.N k) → ℝ := fun xy =>
    if X.allowed xy.1 (some xy.2) then (4 : ℝ) ^ X.criticalCoords.card * p xy.1 xy.2 else 0
  let g : Fin (T.S.N k) × Fin (T.S.N k) → ℝ := fun xy =>
    if X.allowed xy.1 (some xy.2) then q xy.1 xy.2 else 0
  have hX : (PT.tiling.P i).X.Nonempty := hPT.tiling_valid.patch_nonempty i |>.1
  have hMpos : 0 < M := by
    dsimp [M]
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast (Finset.card_pos.mpr hX)
  have hM2pos : 0 < M ^ 2 := sq_pos_of_pos hMpos
  have hAeq : (∑ xy ∈ prodPatch, f xy ^ 2) =
      ∑ x ∈ patch, ∑ y ∈ patch,
        if X.allowed x (some y) then
          ((4 : ℝ) ^ X.criticalCoords.card * p x y) ^ 2 else 0 := by
    calc
      _ = ∑ xy ∈ prodPatch, if X.allowed xy.1 (some xy.2) then
            ((4 : ℝ) ^ X.criticalCoords.card * p xy.1 xy.2) ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro xy _
              by_cases h : X.allowed xy.1 (some xy.2) <;> simp [f, h]
      _ = _ := by
            rw [Finset.sum_product]
  have hAdiv :
      (∑ x ∈ patch, ∑ y ∈ patch,
        if X.allowed x (some y) then
          ((4 : ℝ) ^ X.criticalCoords.card * p x y) ^ 2 else 0) / M ^ 2 ≤
        Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) := by
    simpa [patch, M, p, i] using hSurv.2.2
  have hA : (∑ xy ∈ prodPatch, f xy ^ 2) ≤
      M ^ 2 * Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) := by
    rw [← hAeq] at hAdiv
    simpa [mul_comm] using (div_le_iff₀ hM2pos).1 hAdiv
  have hq_nonneg (x y : Fin (T.S.N k)) : 0 ≤ q x y := by
    exact finLaw_pr_nonneg (tiltedLaw X x (some y))
      (fun s => X.deviates (P.output seed (P.replies seed s P.steps)) x (some y))
  have hq_le (x y : Fin (T.S.N k)) : q x y ≤ 1 := by
    exact finLaw_pr_le_one (tiltedLaw X x (some y))
      (fun s => X.deviates (P.output seed (P.replies seed s P.steps)) x (some y))
  have hBsmall : (∑ xy ∈ prodPatch, g xy ^ 2) ≤
      ∑ xy ∈ prodPatch, if X.allowed xy.1 (some xy.2) then q xy.1 xy.2 else 0 := by
    apply Finset.sum_le_sum
    intro xy _
    by_cases h : X.allowed xy.1 (some xy.2)
    · have hq := mul_nonneg (hq_nonneg xy.1 xy.2) (sub_nonneg.mpr (hq_le xy.1 xy.2))
      have hsq : q xy.1 xy.2 ^ 2 ≤ q xy.1 xy.2 := by nlinarith [hq]
      simpa [g, h] using hsq
    · simp [g, h]
  have hBdiv :
      (∑ x ∈ patch, ∑ y ∈ patch,
        if X.allowed x (some y) then q x y else 0) / M ^ 2 ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
    simpa [patch, M, q, i] using (hTilt seed).2
  have hB : (∑ xy ∈ prodPatch, g xy ^ 2) ≤
      M ^ 2 * Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
    have hBsmall' : (∑ xy ∈ prodPatch,
        if X.allowed xy.1 (some xy.2) then q xy.1 xy.2 else 0) ≤
        M ^ 2 * Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
      have h := (div_le_iff₀ hM2pos).1 hBdiv
      rw [← Finset.sum_product'] at h
      simpa [prodPatch, mul_comm] using h
    exact hBsmall.trans hBsmall'
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq prodPatch f g
  have hsum : (∑ xy ∈ prodPatch, f xy * g xy) =
      ∑ x ∈ patch, ∑ y ∈ patch,
        if X.allowed x (some y) then
          ((4 : ℝ) ^ X.criticalCoords.card * p x y) * q x y else 0 := by
    calc
      _ = ∑ xy ∈ prodPatch,
          if X.allowed xy.1 (some xy.2) then
            ((4 : ℝ) ^ X.criticalCoords.card * p xy.1 xy.2) * q xy.1 xy.2 else 0 := by
              apply Finset.sum_congr rfl
              intro xy _
              by_cases h : X.allowed xy.1 (some xy.2) <;> simp [f, g, h]
      _ = _ := by rw [Finset.sum_product]
  have hC :
      (∑ x ∈ patch, ∑ y ∈ patch,
        if X.allowed x (some y) then
          ((4 : ℝ) ^ X.criticalCoords.card * p x y) * q x y else 0) ^ 2 ≤
        (M ^ 2 * Real.exp (κ.KB * Real.log (T.S.n k : ℝ))) *
          (M ^ 2 * Real.exp (-Real.rpow (T.S.n k : ℝ) c)) := by
    rw [hsum] at hCauchy
    have hg_nonneg : 0 ≤ ∑ xy ∈ prodPatch, g xy ^ 2 :=
      Finset.sum_nonneg fun xy hxy => sq_nonneg (g xy)
    have hAupper : 0 ≤ M ^ 2 * Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) := by positivity
    have hstep1 := mul_le_mul_of_nonneg_right hA hg_nonneg
    have hstep2 := mul_le_mul_of_nonneg_left hB hAupper
    exact hCauchy.trans (hstep1.trans hstep2)
  simpa [M, patch, i, p, q, f, g, mul_assoc, mul_left_comm, mul_comm] using hC

private theorem le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hnot
  have hlt : b < a := lt_of_not_ge hnot
  have ha' : 0 < a := lt_of_le_of_lt hb hlt
  have hprod : 0 < (a - b) * (a + b) :=
    mul_pos (sub_pos.mpr hlt) (add_pos_of_pos_of_nonneg ha' hb)
  nlinarith [hprod]

private noncomputable def finish_single_scaled_sum {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) (seed : P.Seed) : ℝ :=
  ∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
    if X.allowed x none then
      ((2 : ℝ) ^ X.criticalCoords.card *
        X.rawLaw.pr (fun s => X.survives s x none)) *
        (tiltedLaw X x none).pr (fun s =>
          X.deviates (P.output seed (P.replies seed s P.steps)) x none)
    else 0

private theorem finish_single_root_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) (c : ℝ)
    (hSurv : SurvivalFacts X) (hTilt : TiltedDeviationBound P c) (seed : P.Seed) :
    finish_single_scaled_sum X P seed ≤
        ((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) *
          Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2) := by
  classical
  let i := D.geom.patchOf X.target
  let patch := (PT.tiling.P i).X
  let M : ℝ := (PT.tiling.P i).M
  let p : Fin (T.S.N k) → ℝ := fun x => X.rawLaw.pr (fun s => X.survives s x none)
  let q : Fin (T.S.N k) → ℝ := fun x => (tiltedLaw X x none).pr (fun s =>
    X.deviates (P.output seed (P.replies seed s P.steps)) x none)
  let F : ℝ := finish_single_scaled_sum X P seed
  let R : ℝ := M * Real.exp
    ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2)
  have hX : (PT.tiling.P i).X.Nonempty := hPT.tiling_valid.patch_nonempty i |>.1
  have hMpos : 0 < M := by
    dsimp [M]
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast (Finset.card_pos.mpr hX)
  have hFnonneg : 0 ≤ F := by
    dsimp [F, finish_single_scaled_sum]
    apply Finset.sum_nonneg
    intro x _
    by_cases ha : X.allowed x none
    · have hp : 0 ≤ p x := finLaw_pr_nonneg X.rawLaw (fun s => X.survives s x none)
      have hq : 0 ≤ q x := finLaw_pr_nonneg (tiltedLaw X x none) (fun s =>
        X.deviates (P.output seed (P.replies seed s P.steps)) x none)
      simp only [ha, ↓reduceIte]
      exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hp) hq
    · simp [ha]
  have hRpos : 0 < R := mul_pos hMpos (Real.exp_pos _)
  have hCauchy := finish_single_cauchy_bound X P c hSurv hTilt seed
  have hCauchy' : F ^ 2 ≤ M ^ 2 * Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) *
      Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
    simpa [F, finish_single_scaled_sum, M, patch, i, p, q,
      mul_assoc, mul_left_comm, mul_comm] using hCauchy
  have hExpSq : Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) -
      Real.rpow (T.S.n k : ℝ) c) / 2) ^ 2 =
      Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) *
        Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
    let a := κ.KB * Real.log (T.S.n k : ℝ)
    let b := Real.rpow (T.S.n k : ℝ) c
    calc
      Real.exp ((a - b) / 2) ^ 2 = Real.exp ((a - b) / 2) * Real.exp ((a - b) / 2) := by ring
      _ = Real.exp (((a - b) / 2) + ((a - b) / 2)) := (Real.exp_add _ _).symm
      _ = Real.exp (a - b) := by congr 1 <;> ring
      _ = Real.exp a * Real.exp (-b) := by
        have heq : a - b = a + -b := by ring
        rw [heq, Real.exp_add]
      _ = _ := by simp [a, b]
  have hRsq : R ^ 2 = M ^ 2 * Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) *
      Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
    dsimp [R]
    rw [mul_pow]
    calc
      M ^ 2 * Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) -
          Real.rpow (T.S.n k : ℝ) c) / 2) ^ 2 =
        M ^ 2 * (Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) *
          Real.exp (-Real.rpow (T.S.n k : ℝ) c)) :=
            congrArg (fun e : ℝ => M ^ 2 * e) hExpSq
      _ = M ^ 2 * Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) *
          Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by ring
  have hFle : F ≤ R :=
    le_of_sq_le_sq hFnonneg hRpos.le (hCauchy'.trans_eq hRsq.symm)
  simpa [F, finish_single_scaled_sum, R, M, patch, i, p, q] using hFle

private noncomputable def finish_pair_scaled_sum {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) (seed : P.Seed) : ℝ :=
  ∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
    ∑ y ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
      if X.allowed x (some y) then
        ((4 : ℝ) ^ X.criticalCoords.card *
          X.rawLaw.pr (fun s => X.survives s x (some y))) *
          (tiltedLaw X x (some y)).pr (fun s =>
            X.deviates (P.output seed (P.replies seed s P.steps)) x (some y))
      else 0

set_option maxHeartbeats 500000 in
private theorem finish_pair_root_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) (c : ℝ)
    (hSurv : SurvivalFacts X) (hTilt : TiltedDeviationBound P c) (seed : P.Seed) :
    finish_pair_scaled_sum X P seed ≤
      ((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) ^ 2 *
        Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2) := by
  classical
  let i := D.geom.patchOf X.target
  let patch := (PT.tiling.P i).X
  let M : ℝ := (PT.tiling.P i).M
  let p : Fin (T.S.N k) → Fin (T.S.N k) → ℝ := fun x y =>
    X.rawLaw.pr (fun s => X.survives s x (some y))
  let q : Fin (T.S.N k) → Fin (T.S.N k) → ℝ := fun x y =>
    (tiltedLaw X x (some y)).pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x (some y))
  let F : ℝ := finish_pair_scaled_sum X P seed
  let R : ℝ := M ^ 2 * Real.exp
    ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2)
  have hX : (PT.tiling.P i).X.Nonempty := hPT.tiling_valid.patch_nonempty i |>.1
  have hMpos : 0 < M := by
    dsimp [M]
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast (Finset.card_pos.mpr hX)
  have hM2pos : 0 < M ^ 2 := sq_pos_of_pos hMpos
  have hFnonneg : 0 ≤ F := by
    dsimp [F, finish_pair_scaled_sum]
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    by_cases ha : X.allowed x (some y)
    · have hp : 0 ≤ p x y := finLaw_pr_nonneg X.rawLaw (fun s => X.survives s x (some y))
      have hq : 0 ≤ q x y := finLaw_pr_nonneg (tiltedLaw X x (some y)) (fun s =>
        X.deviates (P.output seed (P.replies seed s P.steps)) x (some y))
      simp only [ha, ↓reduceIte]
      exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hp) hq
    · simp [ha]
  have hRpos : 0 < R := mul_pos hM2pos (Real.exp_pos _)
  have hCauchy := finish_pair_cauchy_bound X P c hSurv hTilt seed
  have hCauchy' : F ^ 2 ≤
      (M ^ 2 * Real.exp (κ.KB * Real.log (T.S.n k : ℝ))) *
        (M ^ 2 * Real.exp (-Real.rpow (T.S.n k : ℝ) c)) := by
    simpa [F, finish_pair_scaled_sum, M, patch, i, p, q,
      mul_assoc, mul_left_comm, mul_comm] using hCauchy
  have hExpSq : Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) -
      Real.rpow (T.S.n k : ℝ) c) / 2) ^ 2 =
      Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) *
        Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
    let a := κ.KB * Real.log (T.S.n k : ℝ)
    let b := Real.rpow (T.S.n k : ℝ) c
    calc
      Real.exp ((a - b) / 2) ^ 2 = Real.exp ((a - b) / 2) * Real.exp ((a - b) / 2) := by ring
      _ = Real.exp (((a - b) / 2) + ((a - b) / 2)) := (Real.exp_add _ _).symm
      _ = Real.exp (a - b) := by congr 1 <;> ring
      _ = Real.exp a * Real.exp (-b) := by
        have heq : a - b = a + -b := by ring
        rw [heq, Real.exp_add]
      _ = _ := by simp [a, b]
  have hRsq : R ^ 2 =
      (M ^ 2 * Real.exp (κ.KB * Real.log (T.S.n k : ℝ))) *
        (M ^ 2 * Real.exp (-Real.rpow (T.S.n k : ℝ) c)) := by
    dsimp [R]
    rw [mul_pow]
    calc
      (M ^ 2) ^ 2 * Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) -
          Real.rpow (T.S.n k : ℝ) c) / 2) ^ 2 =
      (M ^ 2) ^ 2 * (Real.exp (κ.KB * Real.log (T.S.n k : ℝ)) *
          Real.exp (-Real.rpow (T.S.n k : ℝ) c)) :=
            congrArg (fun e : ℝ => (M ^ 2) ^ 2 * e) hExpSq
      _ = _ := by
        have hpow : Real.rpow (T.S.n k : ℝ) c = (T.S.n k : ℝ) ^ c := rfl
        rw [hpow]
        ring
  have hFle : F ≤ R :=
    le_of_sq_le_sq hFnonneg hRpos.le (hCauchy'.trans_eq hRsq.symm)
  simpa [F, finish_pair_scaled_sum, R, M, patch, i, p, q] using hFle

private theorem finish_mass_ratio_eventually {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in (Filter.atTop : Filter ℕ), ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ X : CriticalTransferData D,
        TransferGeometry X →
          ((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) /
            (2 : ℝ) ^ X.criticalCoords.card ≤
              Real.exp (20 * (κ.KB + 1) * Real.log (T.S.n k : ℝ)) := by
  have hnReal : Filter.Tendsto (fun k : ℕ => (T.S.n k : ℝ))
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ)).comp T.S.n_tendsto
  have hnLog : ∀ᶠ k in (Filter.atTop : Filter ℕ),
      1 ≤ Real.log (T.S.n k : ℝ) ∧ 1 ≤ (T.S.n k : ℝ) := by
    have hexp : ∀ᶠ k in (Filter.atTop : Filter ℕ),
        Real.exp 1 ≤ (T.S.n k : ℝ) := hnReal.eventually_ge_atTop (Real.exp 1)
    filter_upwards [hexp] with k hk
    have hnpos : 0 < (T.S.n k : ℝ) := lt_of_lt_of_le (by positivity) hk
    exact ⟨(Real.le_log_iff_exp_le hnpos).2 hk, le_trans (by norm_num) hk⟩
  filter_upwards [hnLog] with k hk
  rcases hk with ⟨hlog, hn⟩
  intro PT hPT D hD X hgeom
  classical
  let i := D.geom.patchOf X.target
  let n := T.S.n k
  let m := X.criticalCoords.card
  let C : ℝ := κ.KB + 4 * κ.A0 + 10
  have hsupport : (PT.tiling.P i).X ⊆ T.X k := by
    have h := hPT.tiling_valid.patch_supports i
    exact h.1.trans (h.2.1.trans Finset.sdiff_subset)
  have hMnat : (PT.tiling.P i).M ≤ T.S.N k := by
    calc
      (PT.tiling.P i).M = (PT.tiling.P i).X.card := (PT.tiling.P i).cardX.symm
      _ ≤ (T.X k).card := Finset.card_le_card hsupport
      _ ≤ T.S.N k := by simpa using Finset.card_le_univ (T.X k)
  have hMle : ((PT.tiling.P i).M : ℝ) ≤ (T.S.N k : ℝ) := by exact_mod_cast hMnat
  have hNle : (T.S.N k : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by
    exact_mod_cast T.S.N_le k
  have hmle : m ≤ n := by simpa [m, n] using Finset.card_le_univ X.criticalCoords
  have hdiff : (n : ℝ) - (m : ℝ) ≤ C * Real.log (T.S.n k : ℝ) := by
    have h := hgeom.critical_count
    dsimp [C, n, m] at h ⊢
    linarith
  have hsubcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    exact Nat.cast_sub hmle
  have hqbound : ((n - m : ℕ) : ℝ) ≤ C * Real.log (T.S.n k : ℝ) := by
    rw [hsubcast]
    exact hdiff
  have hpowDiv : (2 : ℝ) ^ n / (2 : ℝ) ^ m = (2 : ℝ) ^ (n - m) := by
    calc
      (2 : ℝ) ^ n / (2 : ℝ) ^ m =
          ((2 : ℝ) ^ (n - m) * (2 : ℝ) ^ m) / (2 : ℝ) ^ m := by
            rw [← pow_sub_mul_pow (2 : ℝ) hmle]
      _ = (2 : ℝ) ^ (n - m) := by field_simp
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hpowExp : (2 : ℝ) ^ (n - m) ≤ Real.exp ((n - m : ℕ) : ℝ) := by
    calc
      (2 : ℝ) ^ (n - m) ≤ (Real.exp 1) ^ (n - m) :=
        pow_le_pow_left₀ (by norm_num) hbase (n - m)
      _ = Real.exp ((n - m : ℕ) : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  have hratio0 : ((PT.tiling.P i).M : ℝ) / (2 : ℝ) ^ m ≤
      (n : ℝ) * Real.exp (C * Real.log (T.S.n k : ℝ)) := by
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn
    calc
      ((PT.tiling.P i).M : ℝ) / (2 : ℝ) ^ m ≤
          (T.S.N k : ℝ) / (2 : ℝ) ^ m :=
        div_le_div_of_nonneg_right hMle (by positivity)
      _ ≤ ((n : ℝ) * (2 : ℝ) ^ n) / (2 : ℝ) ^ m :=
        div_le_div_of_nonneg_right hNle (by positivity)
      _ = (n : ℝ) * ((2 : ℝ) ^ n / (2 : ℝ) ^ m) := by ring
      _ = (n : ℝ) * (2 : ℝ) ^ (n - m) := by rw [hpowDiv]
      _ ≤ (n : ℝ) * Real.exp ((n - m : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hpowExp (by positivity)
      _ ≤ (n : ℝ) * Real.exp (C * Real.log (T.S.n k : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hqbound) (by positivity)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn
  have hrow : 0 ≤ rowMeanConstant κ := by
    have ha : 0 < κ.a := by rw [hκ.a_eq]; positivity [hκ.θ_rng.1]
    unfold rowMeanConstant
    positivity
  have hA0le : κ.A0 ≤ κ.KB := by
    have h := hD.thresholds.1
    have hpos : 0 ≤ Real.exp (100 * κ.Kbd) + 100 * rowMeanConstant κ :=
      add_nonneg (Real.exp_nonneg _) (mul_nonneg (by norm_num) hrow)
    linarith
  have hPpos : 1 ≤ κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    omega
  have hRpos : 1 ≤ κ.R := by
    rw [hκ.R_eq]
    exact Nat.one_le_pow _ _ hPpos
  have hRreal : (1 : ℝ) ≤ κ.R := by exact_mod_cast hRpos
  have hKBge : 1 ≤ κ.KB := by
    have h := hκ.KB_big
    nlinarith
  have hCbound : C + 1 ≤ 20 * (κ.KB + 1) := by
    dsimp [C]
    nlinarith [hA0le, hKBge]
  have hexpRatio :
      (n : ℝ) * Real.exp (C * Real.log (T.S.n k : ℝ)) =
        Real.exp ((C + 1) * Real.log (T.S.n k : ℝ)) := by
    calc
      (n : ℝ) * Real.exp (C * Real.log (T.S.n k : ℝ)) =
          Real.exp (Real.log (T.S.n k : ℝ)) *
            Real.exp (C * Real.log (T.S.n k : ℝ)) := by rw [Real.exp_log hnpos]
      _ = Real.exp (Real.log (T.S.n k : ℝ) + C * Real.log (T.S.n k : ℝ)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp ((C + 1) * Real.log (T.S.n k : ℝ)) := by congr 1 <;> ring
  calc
    ((PT.tiling.P i).M : ℝ) / (2 : ℝ) ^ m ≤
        (n : ℝ) * Real.exp (C * Real.log (T.S.n k : ℝ)) := hratio0
    _ = Real.exp ((C + 1) * Real.log (T.S.n k : ℝ)) := hexpRatio
    _ ≤ Real.exp (20 * (κ.KB + 1) * Real.log (T.S.n k : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCbound (by positivity))

private theorem finish_single_raw_sum_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) (c : ℝ)
    (hSurv : SurvivalFacts X) (hTilt : TiltedDeviationBound P c) :
    (∑ x, (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
      X.survives ss.1 x none ∧ X.allowed x none ∧
        X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x none)) ≤
      (((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) /
        (2 : ℝ) ^ X.criticalCoords.card) *
        Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2) := by
  classical
  let i := D.geom.patchOf X.target
  let patch := (PT.tiling.P i).X
  let M : ℝ := (PT.tiling.P i).M
  let d := X.criticalCoords.card
  let p : Fin (T.S.N k) → ℝ := fun x => X.rawLaw.pr (fun s => X.survives s x none)
  let q : Fin (T.S.N k) → P.Seed → ℝ := fun x seed =>
    (tiltedLaw X x none).pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x none)
  let Q : FinLaw (X.Raw × P.Seed) := FinLaw.bind X.rawLaw (fun _ => P.seedLaw)
  have h_expand :
      (∑ x, Q.pr (fun ss => X.survives ss.1 x none ∧ X.allowed x none ∧
        X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x none)) =
      ∑ seed, P.seedLaw.w seed * ∑ x,
        p x * (if X.allowed x none then q x seed else 0) := by
    calc
      _ = ∑ x, ∑ seed, P.seedLaw.w seed *
          (p x * (if X.allowed x none then q x seed else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            calc
              Q.pr (fun ss => X.survives ss.1 x none ∧ X.allowed x none ∧
                  X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x none) =
                ∑ seed, P.seedLaw.w seed *
                  (X.rawLaw.pr (fun s => X.survives s x none) *
                    (tiltedLaw X x none).pr (fun s => X.allowed x none ∧
                      X.deviates (P.output seed (P.replies seed s P.steps)) x none)) :=
                        transfer_witness_pr_tilt X P x none
              _ = ∑ seed, P.seedLaw.w seed *
                  (p x * (if X.allowed x none then q x seed else 0)) := by
                    apply Finset.sum_congr rfl
                    intro seed _
                    rw [finLaw_pr_and_const]
      _ = ∑ seed, P.seedLaw.w seed * ∑ x,
          p x * (if X.allowed x none then q x seed else 0) :=
            finset_sum_weighted_swap P.seedLaw.w
              (fun x seed => p x * (if X.allowed x none then q x seed else 0))
  have hsupport (seed : P.Seed) :
      (∑ x, p x * (if X.allowed x none then q x seed else 0)) =
        ∑ x ∈ patch, p x * (if X.allowed x none then q x seed else 0) := by
    apply finset_sum_univ_eq_of_support patch _
    intro x hxnot
    by_cases ha : X.allowed x none
    · have hxenv : x ∈ PT.envelope i := by
        change x ∈ PT.envelope i ∧ _ at ha
        exact ha.1
      exact (hxnot (hPT.envelope_subset i hxenv)).elim
    · simp [ha]
  have hnormalize (seed : P.Seed) :
      (∑ x ∈ patch, p x * (if X.allowed x none then q x seed else 0)) =
        ((2 : ℝ) ^ d)⁻¹ * finish_single_scaled_sum X P seed := by
    let a := (2 : ℝ) ^ d
    have ha : a ≠ 0 := pow_ne_zero _ (by norm_num)
    calc
      (∑ x ∈ patch, p x * (if X.allowed x none then q x seed else 0)) =
          ∑ x ∈ patch, a⁻¹ *
            (if X.allowed x none then (a * p x) * q x seed else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : X.allowed x none
              · simp only [if_pos hx]
                calc
                  p x * q x seed = a⁻¹ * (a * (p x * q x seed)) := by field_simp [ha]
                  _ = a⁻¹ * ((a * p x) * q x seed) := by ring
              · simp [a, hx]
      _ = a⁻¹ * ∑ x ∈ patch,
          if X.allowed x none then (a * p x) * q x seed else 0 := by
            rw [Finset.mul_sum]
      _ = _ := by
            have hrootSum : finish_single_scaled_sum X P seed =
                ∑ x ∈ patch, if X.allowed x none then (a * p x) * q x seed else 0 := by
              simp [finish_single_scaled_sum, a, d, p, q, patch, i]
            rw [hrootSum]
  have hseedBound : ∀ seed,
      P.seedLaw.w seed * ∑ x, p x * (if X.allowed x none then q x seed else 0) ≤
        P.seedLaw.w seed * (((2 : ℝ) ^ d)⁻¹ *
          (((PT.tiling.P i).M : ℝ) *
            Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2))) := by
    intro seed
    have hr := finish_single_root_bound X P c hSurv hTilt seed
    have hn := hnormalize seed
    have hs := hsupport seed
    have hscaled : ∑ x ∈ patch, p x * (if X.allowed x none then q x seed else 0) ≤
        ((2 : ℝ)^d)⁻¹ * (((PT.tiling.P i).M : ℝ) *
          Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2)) := by
      rw [hn]
      exact mul_le_mul_of_nonneg_left (by simpa [i] using hr) (inv_nonneg.mpr (by positivity))
    rw [hs]
    exact mul_le_mul_of_nonneg_left hscaled (P.seedLaw.nonneg seed)
  calc
    _ = ∑ seed, P.seedLaw.w seed * ∑ x,
          p x * (if X.allowed x none then q x seed else 0) := h_expand
    _ ≤ ∑ seed, P.seedLaw.w seed * (((2 : ℝ) ^ d)⁻¹ *
          (((PT.tiling.P i).M : ℝ) *
            Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2))) :=
          Finset.sum_le_sum fun seed _ => hseedBound seed
    _ = (∑ seed, P.seedLaw.w seed) *
        (((2 : ℝ) ^ d)⁻¹ * (((PT.tiling.P i).M : ℝ) *
          Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2))) := by
          rw [← Finset.sum_mul]
    _ = _ := by
          rw [P.seedLaw.sum_one]
          simp [div_eq_mul_inv]
          ring

set_option maxHeartbeats 1000000 in
private theorem finish_pair_raw_sum_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) (c : ℝ)
    (hSurv : SurvivalFacts X) (hTilt : TiltedDeviationBound P c) :
    (∑ x, ∑ y, (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
      X.survives ss.1 x (some y) ∧ X.allowed x (some y) ∧
        X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x (some y))) ≤
      (((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) ^ 2 /
        (4 : ℝ) ^ X.criticalCoords.card) *
        Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2) := by
  classical
  let i := D.geom.patchOf X.target
  let patch := (PT.tiling.P i).X
  let M : ℝ := (PT.tiling.P i).M
  let d := X.criticalCoords.card
  let p : Fin (T.S.N k) → Fin (T.S.N k) → ℝ := fun x y =>
    X.rawLaw.pr (fun s => X.survives s x (some y))
  let q : Fin (T.S.N k) → Fin (T.S.N k) → P.Seed → ℝ := fun x y seed =>
    (tiltedLaw X x (some y)).pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x (some y))
  let Q : FinLaw (X.Raw × P.Seed) := FinLaw.bind X.rawLaw (fun _ => P.seedLaw)
  have htriple :
      (∑ x, ∑ y, ∑ seed, P.seedLaw.w seed *
        (p x y * (if X.allowed x (some y) then q x y seed else 0))) =
      ∑ seed, P.seedLaw.w seed * ∑ x, ∑ y,
        p x y * (if X.allowed x (some y) then q x y seed else 0) := by
    calc
      (∑ x, ∑ y, ∑ seed, P.seedLaw.w seed *
          (p x y * (if X.allowed x (some y) then q x y seed else 0))) =
        ∑ x, ∑ seed, ∑ y, P.seedLaw.w seed *
          (p x y * (if X.allowed x (some y) then q x y seed else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_comm]
      _ = ∑ x, ∑ seed, P.seedLaw.w seed * ∑ y,
          p x y * (if X.allowed x (some y) then q x y seed else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro seed _
            rw [← Finset.mul_sum]
      _ = ∑ seed, ∑ x, P.seedLaw.w seed * ∑ y,
          p x y * (if X.allowed x (some y) then q x y seed else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ seed, P.seedLaw.w seed * ∑ x, ∑ y,
          p x y * (if X.allowed x (some y) then q x y seed else 0) := by
            apply Finset.sum_congr rfl
            intro seed _
            rw [← Finset.mul_sum]
  have h_expand :
      (∑ x, ∑ y, Q.pr (fun ss => X.survives ss.1 x (some y) ∧
        X.allowed x (some y) ∧
          X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x (some y))) =
      ∑ seed, P.seedLaw.w seed * ∑ x, ∑ y,
        p x y * (if X.allowed x (some y) then q x y seed else 0) := by
    calc
      _ = ∑ x, ∑ y, ∑ seed, P.seedLaw.w seed *
          (p x y * (if X.allowed x (some y) then q x y seed else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            calc
              Q.pr (fun ss => X.survives ss.1 x (some y) ∧
                  X.allowed x (some y) ∧
                    X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x (some y)) =
                ∑ seed, P.seedLaw.w seed *
                  (X.rawLaw.pr (fun s => X.survives s x (some y)) *
                    (tiltedLaw X x (some y)).pr (fun s => X.allowed x (some y) ∧
                      X.deviates (P.output seed (P.replies seed s P.steps)) x (some y))) :=
                        transfer_witness_pr_tilt X P x (some y)
              _ = ∑ seed, P.seedLaw.w seed *
                  (p x y * (if X.allowed x (some y) then q x y seed else 0)) := by
                    apply Finset.sum_congr rfl
                    intro seed _
                    rw [finLaw_pr_and_const]
      _ = ∑ seed, P.seedLaw.w seed * ∑ x, ∑ y,
          p x y * (if X.allowed x (some y) then q x y seed else 0) := htriple
  have hsupport (seed : P.Seed) :
      (∑ x, ∑ y, p x y * (if X.allowed x (some y) then q x y seed else 0)) =
        ∑ x ∈ patch, ∑ y ∈ patch,
          p x y * (if X.allowed x (some y) then q x y seed else 0) := by
    let prodPatch := patch ×ˢ patch
    have hprod : (∑ xy : Fin (T.S.N k) × Fin (T.S.N k),
        p xy.1 xy.2 * (if X.allowed xy.1 (some xy.2) then q xy.1 xy.2 seed else 0)) =
        ∑ xy ∈ prodPatch,
          p xy.1 xy.2 * (if X.allowed xy.1 (some xy.2) then q xy.1 xy.2 seed else 0) := by
      apply finset_sum_univ_eq_of_support prodPatch _
      intro xy hnot
      by_cases ha : X.allowed xy.1 (some xy.2)
      · change xy.1 ∈ PT.envelope i ∧ (∀ y, some xy.2 = some y → _) at ha
        have hx : xy.1 ∈ patch := hPT.envelope_subset i ha.1
        have hy' := ha.2 xy.2 rfl
        have hy : xy.2 ∈ patch := hPT.envelope_subset i hy'.1
        exact (hnot (Finset.mem_product.mpr ⟨hx, hy⟩)).elim
      · simp [ha]
    calc
      (∑ x, ∑ y, p x y * (if X.allowed x (some y) then q x y seed else 0)) =
          ∑ xy : Fin (T.S.N k) × Fin (T.S.N k),
            p xy.1 xy.2 * (if X.allowed xy.1 (some xy.2) then q xy.1 xy.2 seed else 0) := by
              rw [← Finset.sum_product']
              have huniv :
                  (Finset.univ : Finset (Fin (T.S.N k))) ×ˢ Finset.univ =
                    (Finset.univ : Finset (Fin (T.S.N k) × Fin (T.S.N k))) := by
                ext xy
                simp
              rw [huniv]
      _ = _ := by simpa [prodPatch] using hprod
      _ = _ := by rw [Finset.sum_product]; simp
  have hnormalize (seed : P.Seed) :
      (∑ x ∈ patch, ∑ y ∈ patch,
        p x y * (if X.allowed x (some y) then q x y seed else 0)) =
        ((4 : ℝ) ^ d)⁻¹ * finish_pair_scaled_sum X P seed := by
    let a := (4 : ℝ) ^ d
    have ha : a ≠ 0 := pow_ne_zero _ (by norm_num)
    calc
      (∑ x ∈ patch, ∑ y ∈ patch,
          p x y * (if X.allowed x (some y) then q x y seed else 0)) =
        ∑ x ∈ patch, ∑ y ∈ patch,
          a⁻¹ * (if X.allowed x (some y) then (a * p x y) * q x y seed else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            by_cases hy : X.allowed x (some y)
            · simp only [if_pos hy]
              calc
                p x y * q x y seed = a⁻¹ * (a * (p x y * q x y seed)) := by field_simp [ha]
                _ = a⁻¹ * ((a * p x y) * q x y seed) := by ring
            · simp [hy]
      _ = a⁻¹ * ∑ x ∈ patch, ∑ y ∈ patch,
          if X.allowed x (some y) then (a * p x y) * q x y seed else 0 := by
            calc
              (∑ x ∈ patch, ∑ y ∈ patch,
                  a⁻¹ * (if X.allowed x (some y) then (a * p x y) * q x y seed else 0)) =
                ∑ x ∈ patch, a⁻¹ * ∑ y ∈ patch,
                  if X.allowed x (some y) then (a * p x y) * q x y seed else 0 := by
                    apply Finset.sum_congr rfl
                    intro x _
                    rw [Finset.mul_sum]
              _ = a⁻¹ * ∑ x ∈ patch, ∑ y ∈ patch,
                  if X.allowed x (some y) then (a * p x y) * q x y seed else 0 := by
                    rw [Finset.mul_sum]
      _ = _ := by
            have hrootSum : finish_pair_scaled_sum X P seed =
                ∑ x ∈ patch, ∑ y ∈ patch,
                  if X.allowed x (some y) then (a * p x y) * q x y seed else 0 := by
              simp [finish_pair_scaled_sum, a, d, p, q, patch, i]
            rw [hrootSum]
  have hseedBound : ∀ seed,
      P.seedLaw.w seed * ∑ x, ∑ y, p x y *
        (if X.allowed x (some y) then q x y seed else 0) ≤
      P.seedLaw.w seed * (((4 : ℝ) ^ d)⁻¹ *
        ((((PT.tiling.P i).M : ℝ) ^ 2) *
          Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2))) := by
    intro seed
    have hr := finish_pair_root_bound X P c hSurv hTilt seed
    have hn := hnormalize seed
    have hs := hsupport seed
    have hscaled : ∑ x ∈ patch, ∑ y ∈ patch,
        p x y * (if X.allowed x (some y) then q x y seed else 0) ≤
      ((4 : ℝ) ^ d)⁻¹ * (((PT.tiling.P i).M : ℝ) ^ 2 *
        Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2)) := by
      rw [hn]
      exact mul_le_mul_of_nonneg_left (by simpa [i] using hr) (inv_nonneg.mpr (by positivity))
    rw [hs]
    exact mul_le_mul_of_nonneg_left hscaled (P.seedLaw.nonneg seed)
  calc
    _ = ∑ seed, P.seedLaw.w seed * ∑ x, ∑ y,
          p x y * (if X.allowed x (some y) then q x y seed else 0) := h_expand
    _ ≤ ∑ seed, P.seedLaw.w seed * (((4 : ℝ) ^ d)⁻¹ *
          ((((PT.tiling.P i).M : ℝ) ^ 2) *
            Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2))) :=
          Finset.sum_le_sum fun seed _ => hseedBound seed
    _ = (∑ seed, P.seedLaw.w seed) * (((4 : ℝ) ^ d)⁻¹ *
        (((PT.tiling.P i).M : ℝ) ^ 2 *
          Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2))) := by
          rw [← Finset.sum_mul]
    _ = _ := by
          rw [P.seedLaw.sum_one]
          simp [div_eq_mul_inv]
          ring

private theorem finish_raw_bad_prob_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    (X : CriticalTransferData D) (P : TransferProtocol X) (c : ℝ)
    (hSurv : SurvivalFacts X) (hTilt : TiltedDeviationBound P c) :
    (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
      ∃ x z, X.allowed x z ∧ X.survives ss.1 x z ∧
        X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x z) ≤
      (((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) /
        (2 : ℝ) ^ X.criticalCoords.card) *
          Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2) +
      (((PT.tiling.P (D.geom.patchOf X.target)).M : ℝ) ^ 2 /
        (4 : ℝ) ^ X.criticalCoords.card) *
          Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) c) / 2) := by
  calc
    _ ≤
        (∑ x, (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
          X.survives ss.1 x none ∧ X.allowed x none ∧
            X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x none)) +
        ∑ x, ∑ y, (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
          X.survives ss.1 x (some y) ∧ X.allowed x (some y) ∧
            X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x (some y)) :=
              transfer_bad_event_union_bound X P
    _ ≤ _ := add_le_add (finish_single_raw_sum_bound X P c hSurv hTilt)
      (finish_pair_raw_sum_bound X P c hSurv hTilt)

private theorem four_pow_eq_two_pow_sq (d : ℕ) :
    (4 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 2 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
      rw [pow_succ, ih, pow_succ]
      ring

private theorem finish_exponent_slack_eventually {κ : CConsts} (T : Stage)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k in (Filter.atTop : Filter ℕ),
      Real.log 4 + 50 * (κ.KB + 1) * Real.log (T.S.n k : ℝ) ≤
        Real.rpow (T.S.n k : ℝ) c / 4 ∧
      Real.rpow (T.S.n k : ℝ) (c / 2) ≤ Real.rpow (T.S.n k : ℝ) c / 4 := by
  have hnR : Filter.Tendsto (fun k : ℕ => (T.S.n k : ℝ))
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ)).comp T.S.n_tendsto
  have htR : Filter.Tendsto (fun k : ℕ => Real.rpow (T.S.n k : ℝ) c)
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    (tendsto_rpow_atTop hc).comp hnR
  have huR : Filter.Tendsto (fun k : ℕ => Real.rpow (T.S.n k : ℝ) (c / 2))
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    (tendsto_rpow_atTop (by linarith : 0 < c / 2)).comp hnR
  have hlogLittle :=
    ((isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero).comp hnR
  let A : ℝ := 50 * (κ.KB + 1)
  have hAconst : Filter.Tendsto (fun _ : ℕ => A)
      (Filter.atTop : Filter ℕ) (nhds A) := tendsto_const_nhds
  have hratio : Filter.Tendsto (fun k : ℕ =>
      A * (Real.log (T.S.n k : ℝ) / Real.rpow (T.S.n k : ℝ) c))
      (Filter.atTop : Filter ℕ) (nhds 0) := by
    simpa [A, Function.comp_def] using hAconst.mul hlogLittle
  have hsmall : ∀ᶠ k in (Filter.atTop : Filter ℕ),
      A * (Real.log (T.S.n k : ℝ) / Real.rpow (T.S.n k : ℝ) c) < 1 / 8 :=
    hratio.eventually (Iio_mem_nhds (by norm_num))
  have hnpos : ∀ᶠ k in (Filter.atTop : Filter ℕ), 0 < (T.S.n k : ℝ) := by
    filter_upwards [hnR.eventually_ge_atTop (1 : ℝ)] with k hk
    exact lt_of_lt_of_le (by norm_num) hk
  have huLarge : ∀ᶠ k in (Filter.atTop : Filter ℕ),
      16 ≤ Real.rpow (T.S.n k : ℝ) (c / 2) :=
    huR.eventually_ge_atTop 16
  have htLarge : ∀ᶠ k in (Filter.atTop : Filter ℕ),
      8 * Real.log 4 ≤ Real.rpow (T.S.n k : ℝ) c :=
    htR.eventually_ge_atTop (8 * Real.log 4)
  filter_upwards [hsmall, hnpos, huLarge, htLarge] with k hsmall hnpos huLarge htLarge
  let t := Real.rpow (T.S.n k : ℝ) c
  let u := Real.rpow (T.S.n k : ℝ) (c / 2)
  have htpos : 0 < t := Real.rpow_pos_of_pos hnpos _
  have hsmall' : A * Real.log (T.S.n k : ℝ) < t / 8 := by
    have hdiv : (A * Real.log (T.S.n k : ℝ)) / t < 1 / 8 := by
      simpa [A, t, div_eq_mul_inv, mul_assoc] using hsmall
    have hlt := (div_lt_iff₀ htpos).mp hdiv
    nlinarith [hlt]
  have hlog4 : Real.log 4 ≤ t / 8 := by
    have := htLarge
    dsimp [t] at this
    linarith
  have hslack₁ : Real.log 4 + A * Real.log (T.S.n k : ℝ) ≤ t / 4 := by
    linarith
  have hpow : t = u ^ 2 := by
    dsimp [t, u]
    calc
      Real.rpow (T.S.n k : ℝ) c =
          Real.rpow (T.S.n k : ℝ) ((c / 2) * 2) := by congr 1 <;> ring
      _ = Real.rpow (Real.rpow (T.S.n k : ℝ) (c / 2)) (2 : ℝ) :=
        Real.rpow_mul hnpos.le (c / 2) 2
      _ = (Real.rpow (T.S.n k : ℝ) (c / 2)) ^ 2 := by
        exact Real.rpow_natCast _ 2
  have huPos : 0 < u := Real.rpow_pos_of_pos hnpos _
  have huBound : u ≤ t / 4 := by
    have hu16 : 16 ≤ u := by simpa [u] using huLarge
    have hsq : 16 * u ≤ u ^ 2 := by
      nlinarith [mul_nonneg huPos.le (sub_nonneg.mpr hu16)]
    rw [hpow]
    nlinarith
  exact ⟨by simpa [A, t] using hslack₁, by simpa [t, u] using huBound⟩

theorem finish_from_survival_tilt {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (ctilt : ℝ) (hc : 0 < ctilt) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ᶠ k in (Filter.atTop : Filter ℕ),
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
        ∀ D : LateData hPT, D.Spec → SmallErrors κ T k PT D.geom (Real.log 2 / 1000) →
        ∀ X : CriticalTransferData D, TransferGeometry X → SurvivalFacts X →
          ∀ P : TransferProtocol X, TiltedDeviationBound P ctilt →
            X.experiment.pr (fun z => D.prefixFailure X.failure z.2) ≤
              Real.exp (-Real.rpow (T.S.n k : ℝ) c1) := by
  refine ⟨ctilt / 2, by linarith, ?_⟩
  have hnR : Filter.Tendsto (fun k : ℕ => (T.S.n k : ℝ))
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ)).comp T.S.n_tendsto
  have hnLog : ∀ᶠ k in (Filter.atTop : Filter ℕ),
      1 ≤ Real.log (T.S.n k : ℝ) ∧ 1 ≤ (T.S.n k : ℝ) := by
    have hexp : ∀ᶠ k in (Filter.atTop : Filter ℕ),
        Real.exp 1 ≤ (T.S.n k : ℝ) := hnR.eventually_ge_atTop (Real.exp 1)
    filter_upwards [hexp] with k hk
    have hnpos : 0 < (T.S.n k : ℝ) := lt_of_lt_of_le (by positivity) hk
    exact ⟨(Real.le_log_iff_exp_le hnpos).2 hk, le_trans (by norm_num) hk⟩
  have hMassEventual := finish_mass_ratio_eventually hκ T
  have hSlackEventual := finish_exponent_slack_eventually (κ := κ) T ctilt hc
  have hAll₁ := hMassEventual.and hSlackEventual
  have hAll := hAll₁.and hnLog
  filter_upwards [hAll] with k hk
  rcases hk with ⟨⟨hMass, hSlack⟩, htol⟩
  rcases htol with ⟨hlog, hn⟩
  intro PT hPT D hD hSmall X hgeom hSurv P hTilt
  classical
  let i := D.geom.patchOf X.target
  let d := X.criticalCoords.card
  let M : ℝ := (PT.tiling.P i).M
  let ρ : ℝ := M / (2 : ℝ) ^ d
  let L : ℝ := 20 * (κ.KB + 1) * Real.log (T.S.n k : ℝ)
  let t : ℝ := Real.rpow (T.S.n k : ℝ) ctilt
  let half : ℝ := Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - t) / 2)
  have hKB0 : 0 ≤ κ.KB := le_trans (mul_nonneg (by norm_num) (by positivity)) hκ.KB_big
  have hlog0 : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hρ : ρ ≤ Real.exp L := by simpa [ρ, M, i, d, L] using hMass PT hPT D hD X hgeom
  have hρ0 : 0 ≤ ρ := by dsimp [ρ, M]; positivity
  have hρ2 : ρ ^ 2 ≤ Real.exp (2 * L) := by
    have hstep1 : ρ ^ 2 ≤ Real.exp L * ρ := by
      simpa [pow_two] using mul_le_mul_of_nonneg_right hρ hρ0
    have hstep2 : Real.exp L * ρ ≤ Real.exp L * Real.exp L :=
      mul_le_mul_of_nonneg_left hρ (Real.exp_nonneg L)
    have hexp : Real.exp L * Real.exp L = Real.exp (2 * L) := by
      calc
        Real.exp L * Real.exp L = Real.exp (L + L) := (Real.exp_add _ _).symm
        _ = Real.exp (2 * L) := by congr 1 <;> ring
    exact hstep1.trans (hstep2.trans_eq hexp)
  have hρ1 : ρ ≤ Real.exp (2 * L) := by
    exact hρ.trans (Real.exp_le_exp.mpr (by linarith [hL0]))
  have hρsum : ρ + ρ ^ 2 ≤ 2 * Real.exp (2 * L) := by
    nlinarith [hρ1, hρ2]
  have hfour : (4 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 2 := four_pow_eq_two_pow_sq d
  have hρpair : M ^ 2 / (4 : ℝ) ^ d = ρ ^ 2 := by
    dsimp [ρ]
    rw [hfour, div_pow]
  have hRaw0 := finish_raw_bad_prob_bound X P ctilt hSurv hTilt
  have hRaw :
      (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
        ∃ x z, X.allowed x z ∧ X.survives ss.1 x z ∧
          X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x z) ≤
        ρ * half + ρ ^ 2 * half := by
    calc
      _ ≤ (M / (2 : ℝ) ^ d) * half + (M ^ 2 / (4 : ℝ) ^ d) * half := by
        simpa [M, i, d, t, half] using hRaw0
      _ = _ := by rw [hρpair]
  have hBadExp :
      (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
        ∃ x z, X.allowed x z ∧ X.survives ss.1 x z ∧
          X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x z) ≤
        2 * Real.exp (2 * L) * half := by
    calc
      _ ≤ (ρ + ρ ^ 2) * half := by
        calc
          _ ≤ ρ * half + ρ ^ 2 * half := hRaw
          _ = (ρ + ρ ^ 2) * half := by ring
      _ ≤ 2 * Real.exp (2 * L) * half :=
        mul_le_mul_of_nonneg_right hρsum (Real.exp_nonneg _)
  have hSmallI : (max 1 (PT.tiling.P i).h : ℝ) *
      (∑ j : Fin D.geom.r, D.error X.target j) ≤ Real.log 2 / 1000 := by
    simpa [LateData.error, i] using hSmall i
  have hErr : 1000 * (max 1 (PT.tiling.P i).h : ℝ) *
      (∑ j : Fin D.geom.r, D.error X.target j) ≤ Real.log 2 := by
    nlinarith [hSmallI]
  have hErrExp : Real.exp (1000 * (max 1 (PT.tiling.P i).h : ℝ) *
      (∑ j : Fin D.geom.r, D.error X.target j)) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hErr
      _ = 2 := Real.exp_log (by norm_num)
  have hReduction := P.reduction
  have hProb : X.experiment.pr (fun z => D.prefixFailure X.failure z.2) ≤
      4 * Real.exp (2 * L +
        (κ.KB * Real.log (T.S.n k : ℝ) - t) / 2) := by
    calc
      _ ≤ Real.exp (1000 * (max 1 (PT.tiling.P i).h : ℝ) *
            (∑ j : Fin D.geom.r, D.error X.target j)) *
          (FinLaw.bind X.rawLaw (fun _ => P.seedLaw)).pr (fun ss =>
            ∃ x z, X.allowed x z ∧ X.survives ss.1 x z ∧
              X.deviates (P.output ss.2 (P.replies ss.2 ss.1 P.steps)) x z) := hReduction
      _ ≤ Real.exp (1000 * (max 1 (PT.tiling.P i).h : ℝ) *
            (∑ j : Fin D.geom.r, D.error X.target j)) *
          (2 * Real.exp (2 * L) * half) :=
            mul_le_mul_of_nonneg_left hBadExp (Real.exp_nonneg _)
      _ ≤ 2 * (2 * Real.exp (2 * L) * half) :=
            mul_le_mul_of_nonneg_right hErrExp (by positivity)
      _ = 4 * Real.exp (2 * L +
            (κ.KB * Real.log (T.S.n k : ℝ) - t) / 2) := by
              dsimp [half]
              calc
                2 * (2 * Real.exp (2 * L) *
                    Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - t) / 2)) =
                  4 * (Real.exp (2 * L) *
                    Real.exp ((κ.KB * Real.log (T.S.n k : ℝ) - t) / 2)) := by ring
                _ = _ := by rw [← Real.exp_add]
  have hArg : Real.log 4 + 2 * L +
      (κ.KB * Real.log (T.S.n k : ℝ) - t) / 2 ≤ -t / 4 := by
    have hcoeff : 2 * L + κ.KB * Real.log (T.S.n k : ℝ) / 2 ≤
        50 * (κ.KB + 1) * Real.log (T.S.n k : ℝ) := by
      dsimp [L]
      nlinarith [hKB0, hlog0]
    have hs := hSlack.1
    dsimp [t] at hs ⊢
    nlinarith [hcoeff]
  have hprob' : X.experiment.pr (fun z => D.prefixFailure X.failure z.2) ≤
      Real.exp (-t / 4) := by
    calc
      _ ≤ 4 * Real.exp (2 * L +
          (κ.KB * Real.log (T.S.n k : ℝ) - t) / 2) := hProb
      _ = Real.exp (Real.log 4 + 2 * L +
          (κ.KB * Real.log (T.S.n k : ℝ) - t) / 2) := by
            calc
              4 * Real.exp (2 * L + (κ.KB * Real.log (T.S.n k : ℝ) - t) / 2) =
                  Real.exp (Real.log 4) *
                    Real.exp (2 * L + (κ.KB * Real.log (T.S.n k : ℝ) - t) / 2) := by
                      rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
              _ = Real.exp (Real.log 4 + (2 * L +
                    (κ.KB * Real.log (T.S.n k : ℝ) - t) / 2)) :=
                      (Real.exp_add _ _).symm
              _ = _ := by congr 1 <;> ring
      _ ≤ Real.exp (-t / 4) := Real.exp_le_exp.mpr hArg
  have hRate : t / 4 ≥ Real.rpow (T.S.n k : ℝ) (ctilt / 2) := by
    simpa [t] using hSlack.2
  have hNeg : -t / 4 ≤ -Real.rpow (T.S.n k : ℝ) (ctilt / 2) := by nlinarith [hRate]
  have hfinal := hprob'.trans (Real.exp_le_exp.mpr hNeg)
  simpa [t, div_eq_mul_inv] using hfinal

private theorem real_finset_prod_le_of_pointwise {α : Type*} (s : Finset α)
    (f g : α → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∏ x ∈ s, f x ≤ ∏ x ∈ s, g x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfs : ∀ x ∈ s, 0 ≤ f x := fun x hx => hf x (Finset.mem_insert_of_mem hx)
      have hgs : ∀ x ∈ s, 0 ≤ g x := fun x hx => hg x (Finset.mem_insert_of_mem hx)
      have hfgs : ∀ x ∈ s, f x ≤ g x := fun x hx => hfg x (Finset.mem_insert_of_mem hx)
      have hfa := hfg a (Finset.mem_insert_self a s)
      have hga := hg a (Finset.mem_insert_self a s)
      have hprodF : 0 ≤ ∏ x ∈ s, f x := Finset.prod_nonneg hfs
      exact (mul_le_mul_of_nonneg_right hfa hprodF).trans
        (mul_le_mul_of_nonneg_left (ih hfs hgs hfgs) hga)

private theorem critical_survival_probability_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hgeom : TransferGeometry X)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (u : ℝ) (hu : 0 ≤ u)
    (hcell : ∀ a ∈ X.criticalCoords,
      (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
        Hits (T.S.E k) PT.tiling.c x
          (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a)) ∧
        ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y
          (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a))) ≤ u) :
    X.rawLaw.pr (fun s => X.survives s x z) ≤ u ^ X.criticalCoords.card := by
  classical
  let factors : ∀ C : D.geom.Cell,
      FinLaw (D.fresh.Pool C × D.fresh.State C) := fun C =>
    if C ∈ X.criticalCells then D.typicalFresh C
    else FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)
  let hitAt : ∀ C : D.geom.Cell,
      D.fresh.Pool C × D.fresh.State C → Fin (T.S.n k) → Prop := fun C Ps a =>
    Hits (T.S.E k) PT.tiling.c x (D.fresh.label C Ps.2 (flipPos X.target a)) ∧
      ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y
        (D.fresh.label C Ps.2 (flipPos X.target a))
  let cellEvent : ∀ C : D.geom.Cell,
      D.fresh.Pool C × D.fresh.State C → Prop := fun C Ps =>
    ∀ a, a ∈ X.criticalCoords →
      D.geom.cellOf (flipPos X.target a) = C → hitAt C Ps a
  have hEvent (s : X.Raw) : X.survives s x z ↔ ∀ C, cellEvent C (s C) := by
    constructor
    · intro hs C a ha hC
      have h := hs a ha
      have h' : hitAt (D.geom.cellOf (flipPos X.target a))
          (s (D.geom.cellOf (flipPos X.target a))) a := by
        simpa [hitAt, CriticalTransferData.criticalLabel, CriticalTransferData.state,
          LateData.earlyLabel] using h
      cases hC
      exact h'
    · intro hs a ha
      have h := hs (D.geom.cellOf (flipPos X.target a)) a ha rfl
      simpa [hitAt, CriticalTransferData.criticalLabel, CriticalTransferData.state,
        LateData.earlyLabel] using h
  have hpi : X.rawLaw = FinLaw.pi factors := rfl
  have hprob : X.rawLaw.pr (fun s => X.survives s x z) =
      ∏ C, (factors C).pr (cellEvent C) := by
    calc
      X.rawLaw.pr (fun s => X.survives s x z) =
          X.rawLaw.pr (fun s => ∀ C, cellEvent C (s C)) :=
            finLaw_pr_congr X.rawLaw _ _ hEvent
      _ = (FinLaw.pi factors).pr (fun s => ∀ C, cellEvent C (s C)) := by rw [hpi]
      _ = ∏ C, (factors C).pr (cellEvent C) := finLaw_pi_pr_forall factors cellEvent
  have hFactor : ∀ C, (factors C).pr (cellEvent C) ≤
      if C ∈ X.criticalCells then u else 1 := by
    intro C
    by_cases hC : C ∈ X.criticalCells
    · obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hC
      subst C
      have hSub : ∀ Ps, cellEvent (D.geom.cellOf (flipPos X.target a)) Ps →
          hitAt (D.geom.cellOf (flipPos X.target a)) Ps a := by
        intro Ps he
        exact he a ha rfl
      have hmono := finLaw_pr_mono (D.typicalFresh (D.geom.cellOf (flipPos X.target a)))
        (cellEvent (D.geom.cellOf (flipPos X.target a)))
        (fun Ps => hitAt (D.geom.cellOf (flipPos X.target a)) Ps a) hSub
      have hcell' := hcell a ha
      have hmem : D.geom.cellOf (flipPos X.target a) ∈ X.criticalCells :=
        Finset.mem_image.mpr ⟨a, ha, rfl⟩
      have hfac : factors (D.geom.cellOf (flipPos X.target a)) =
          D.typicalFresh (D.geom.cellOf (flipPos X.target a)) := by
        simp [factors, hmem]
      simpa [hfac, hmem] using le_trans hmono hcell'
    · have hNo : ∀ a, a ∈ X.criticalCoords →
          D.geom.cellOf (flipPos X.target a) ≠ C := by
        intro a ha hEq
        apply hC
        exact Finset.mem_image.mpr ⟨a, ha, hEq⟩
      have htrue : ∀ Ps, cellEvent C Ps := by
        intro Ps a ha hEq
        exact (hNo a ha hEq).elim
      have hiff : ∀ Ps, cellEvent C Ps ↔ True := by
        intro Ps
        exact ⟨fun _ => True.intro, fun _ => htrue Ps⟩
      have hpr : (factors C).pr (cellEvent C) = 1 := by
        calc
          (factors C).pr (cellEvent C) = (factors C).pr (fun _ => True) :=
            finLaw_pr_congr (factors C) (cellEvent C) (fun _ => True) hiff
          _ = 1 := finLaw_pr_true (factors C)
      simp [hC, hpr]
  have hFactorsNonneg : ∀ C, 0 ≤ (factors C).pr (cellEvent C) :=
    fun C => finLaw_pr_nonneg (factors C) (cellEvent C)
  have hprod : (∏ C, (factors C).pr (cellEvent C)) ≤
      ∏ C, if C ∈ X.criticalCells then u else 1 := by
    apply real_finset_prod_le_of_pointwise Finset.univ
    · intro C _
      exact hFactorsNonneg C
    · intro C _
      by_cases hC : C ∈ X.criticalCells <;> simp [hC, hu]
    · intro C _
      exact hFactor C
  have hcard : X.criticalCells.card = X.criticalCoords.card := by
    apply Finset.card_image_iff.mpr
    intro a ha a' ha' hEq
    exact hgeom.distinct_cells a ha a' ha' hEq
  rw [hprob]
  calc
    (∏ C, (factors C).pr (cellEvent C)) ≤
        ∏ C, if C ∈ X.criticalCells then u else 1 := hprod
    _ = u ^ X.criticalCoords.card := by
        rw [Finset.prod_ite_mem]
        simp [hcard]

private theorem eventually_degree_tolerances {κ : CConsts} (T : Stage) :
    ∀ᶠ k in (Filter.atTop : Filter ℕ),
      κ.Kbd / (T.S.n k : ℝ) ^ (1 / 2 : ℝ) < 1 / 100 ∧
      4 * κ.KB * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ)) < 1 / 100 ∧
      10 * (Real.log (T.S.n k : ℝ) ^ κ.Cb) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ) < 1 / 100 ∧
      κ.KB * Real.rpow (T.S.n k : ℝ) (-3) ≤ 1 / 100 ∧
      1 ≤ Real.log (T.S.n k : ℝ) ∧ 1 ≤ (T.S.n k : ℝ) := by
  have hnR : Filter.Tendsto (fun k : ℕ => (T.S.n k : ℝ))
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun n : ℕ => (n : ℝ))
        (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ)).comp T.S.n_tendsto
  have hroot : Filter.Tendsto (fun k : ℕ => (T.S.n k : ℝ) ^ (1 / 2 : ℝ))
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hnR
  have hinv : Filter.Tendsto (fun k : ℕ =>
      ((T.S.n k : ℝ) ^ (1 / 2 : ℝ))⁻¹)
      (Filter.atTop : Filter ℕ) (nhds 0) := by
    exact hroot.inv_tendsto_atTop
  have hlog :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp hnR
  have hlogCb :=
    ((isLittleO_log_rpow_rpow_atTop κ.Cb (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp hnR
  have hneg := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp hnR
  have h1 : ∀ᶠ k in (Filter.atTop : Filter ℕ),
      κ.Kbd * ((T.S.n k : ℝ) ^ (1 / 2 : ℝ))⁻¹ < 1 / 100 := by
    have hconst : Filter.Tendsto (fun _ : ℕ => κ.Kbd)
        (Filter.atTop : Filter ℕ) (nhds κ.Kbd) := tendsto_const_nhds
    have hlim : Filter.Tendsto (fun k : ℕ =>
        κ.Kbd * ((T.S.n k : ℝ) ^ (1 / 2 : ℝ))⁻¹)
        (Filter.atTop : Filter ℕ) (nhds 0) := by
      simpa using hconst.mul hinv
    exact hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  have h2 : ∀ᶠ k in (Filter.atTop : Filter ℕ),
      4 * κ.KB * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ)) < 1 / 100 := by
    have hconst : Filter.Tendsto (fun _ : ℕ => 4 * κ.KB)
        (Filter.atTop : Filter ℕ) (nhds (4 * κ.KB)) := tendsto_const_nhds
    have hlim : Filter.Tendsto (fun k : ℕ =>
        4 * κ.KB * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ)))
        (Filter.atTop : Filter ℕ) (nhds 0) := by
      simpa [Function.comp_def, mul_assoc] using hconst.mul hlog
    filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))] with k hk
    nlinarith [hk]
  have h3 : ∀ᶠ k in (Filter.atTop : Filter ℕ),
      10 * (Real.log (T.S.n k : ℝ) ^ κ.Cb) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ) < 1 / 100 := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (10 : ℝ))
        (Filter.atTop : Filter ℕ) (nhds 10) := tendsto_const_nhds
    have hlim : Filter.Tendsto (fun k : ℕ =>
        10 * (Real.log (T.S.n k : ℝ) ^ κ.Cb) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ))
        (Filter.atTop : Filter ℕ) (nhds 0) := by
      simpa [Function.comp_def, div_eq_mul_inv, mul_assoc] using hconst.mul hlogCb
    filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))] with k hk
    nlinarith [hk]
  have h4 : ∀ᶠ k in (Filter.atTop : Filter ℕ),
      κ.KB * Real.rpow (T.S.n k : ℝ) (-3) ≤ 1 / 100 := by
    have hconst : Filter.Tendsto (fun _ : ℕ => κ.KB)
        (Filter.atTop : Filter ℕ) (nhds κ.KB) := tendsto_const_nhds
    have hlim : Filter.Tendsto (fun k : ℕ =>
        κ.KB * Real.rpow (T.S.n k : ℝ) (-3))
        (Filter.atTop : Filter ℕ) (nhds 0) := by
      simpa [Function.comp_def] using hconst.mul hneg
    filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))] with k hk
    exact le_of_lt hk
  have h5 : ∀ᶠ k in (Filter.atTop : Filter ℕ), 1 ≤ Real.log (T.S.n k : ℝ) := by
    have hexp : ∀ᶠ k in (Filter.atTop : Filter ℕ), Real.exp 1 ≤ (T.S.n k : ℝ) :=
      hnR.eventually_ge_atTop (Real.exp 1)
    filter_upwards [hexp] with k hk
    have hnpos : 0 < (T.S.n k : ℝ) := lt_of_lt_of_le (by positivity) hk
    exact (Real.le_log_iff_exp_le hnpos).2 hk
  have h6 : ∀ᶠ k in (Filter.atTop : Filter ℕ), 1 ≤ (T.S.n k : ℝ) :=
    hnR.eventually_ge_atTop 1
  filter_upwards [h1, h2, h3, h4, h5, h6] with k h1 h2 h3 h4 h5 h6
  exact ⟨by simpa [div_eq_mul_inv] using h1, h2, h3, h4, h5, h6⟩

private theorem low_profile_degree_close {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible) (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (i : Fin PT.tiling.m)
    (x : Fin (T.S.N k)) (hx : x ∈ PT.envelope i)
    (hbd : κ.Kbd / (T.S.n k : ℝ) ^ (1 / 2 : ℝ) < 1 / 100)
    (hdir : 4 * κ.KB * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ)) < 1 / 100)
    (hclu : 10 * (Real.log (T.S.n k : ℝ) ^ κ.Cb) /
      (T.S.n k : ℝ) ^ (1 / 2 : ℝ) < 1 / 100)
    (hn : 1 ≤ (T.S.n k : ℝ)) (hlog : 1 ≤ Real.log (T.S.n k : ℝ)) :
    |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤ 1 / 100 := by
  classical
  have hnpos : 0 < (T.S.n k : ℝ) := lt_of_lt_of_le (by norm_num) hn
  have hrootPos : 0 < (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hrootLe : (T.S.n k : ℝ) ^ (1 / 2 : ℝ) ≤ (T.S.n k : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hn
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
    simpa only [Real.rpow_one] using h
  have hKB : 0 ≤ κ.KB := by
    have hR : 0 ≤ (κ.R : ℝ) := by positivity
    exact le_trans (mul_nonneg (by norm_num) hR) hκ.KB_big
  have hNumLog : 0 ≤ 4 * κ.KB * Real.log (T.S.n k : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hKB) (by positivity)
  cases hmode : PT.tiling.mode with
  | bounded =>
      have hown := hPT.envelope_degree i x hx
      have hwindow :
          |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤ κ.Kbd / (T.S.n k : ℝ) := by
        simpa [OwnDegOK, hmode] using hown
      have hKbd : 0 ≤ κ.Kbd := le_trans (by norm_num) hκ.bounded.2.2.2.1
      have hdiv : κ.Kbd / (T.S.n k : ℝ) ≤
          κ.Kbd / (T.S.n k : ℝ) ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left hKbd hrootPos hrootLe
      exact le_trans hwindow (le_trans hdiv (le_of_lt hbd))
  | lowDirect =>
      have hown := hPT.envelope_degree i x hx
      have hwindow := by simpa [OwnDegOK, hmode] using hown
      rcases hwindow with ⟨hlo, hup⟩
      have hdd := hPT.tiling_valid.direct_data (Or.inl hmode) i
      rcases hdd with ⟨_, _, _, _, _, hhigh⟩
      have hnotHigh : PT.tiling.mode ≠ .highDirect := by simp [hmode]
      have hg : (PT.tiling.P i).g ≤ κ.KB * Real.log (T.S.n k : ℝ) := by
        apply le_of_not_gt
        intro hgt
        exact hnotHigh (hhigh.2.mpr hgt)
      have hg0 : 0 ≤ ((PT.tiling.P i).g : ℝ) := by positivity
      have hbias0 : 0 ≤ deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2 := by
        have hgn : 0 ≤ ((PT.tiling.P i).g : ℝ) / (4 * (T.S.n k : ℝ)) :=
          div_nonneg hg0 (by positivity)
        linarith
      have hUpper :
          |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
            4 * (PT.tiling.P i).g / (T.S.n k : ℝ) := by
        rw [abs_of_nonneg hbias0]
        linarith
      have hGnum : 4 * (PT.tiling.P i).g ≤ 4 * κ.KB * Real.log (T.S.n k : ℝ) := by
        nlinarith [hg]
      have hratio : 4 * (PT.tiling.P i).g / (T.S.n k : ℝ) ≤
          4 * κ.KB * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) := by
        exact div_le_div_of_nonneg_right hGnum (by positivity)
      have hratio' : 4 * κ.KB * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ≤
          4 * κ.KB * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ)) := by
        calc
          4 * κ.KB * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ≤
              4 * κ.KB * Real.log (T.S.n k : ℝ) /
                (T.S.n k : ℝ) ^ (1 / 2 : ℝ) :=
            div_le_div_of_nonneg_left hNumLog hrootPos hrootLe
          _ = 4 * κ.KB *
              (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ)) := by ring
      exact le_trans hUpper (le_trans hratio (le_trans hratio' (le_of_lt hdir)))
  | lowCluster =>
      have hown := hPT.envelope_degree i x hx
      have hwindow := by simpa [OwnDegOK, hmode] using hown
      have hCb : 0 < κ.Cb := by
        have ha : 0 < 100 * κ.aC / κ.aB :=
          div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
        have := hκ.Cb_big
        linarith
      have hMlo : 1 ≤ (κ.Mlo : ℝ) := by
        have := hκ.Mlo_big
        linarith
      have hden : (20 : ℝ) ≤ 20 * (κ.Mlo : ℝ) := by nlinarith
      have hfrac : 1 / (20 * (κ.Mlo : ℝ)) ≤ 1 / 20 :=
        one_div_le_one_div_of_le (by norm_num) hden
      have hcq : κ.cq < 1 := lt_trans hκ.cq_rng.2 (lt_of_le_of_lt hfrac (by norm_num))
      have hcd := hPT.tiling_valid.cluster_data (Or.inl hmode) i
      rcases hcd with ⟨_, _, _, _, _, _, _, _, _, hqiff, _, _⟩
      have hqpow : (PT.tiling.P i).q ≤ Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq :=
        hqiff.mp hmode
      have hq : (PT.tiling.P i).q ≤ Real.log (T.S.n k : ℝ) := by
        have hpow := Real.rpow_le_rpow_of_exponent_le hlog hcq.le
        exact hqpow.trans (by simpa [Real.rpow_one] using hpow)
      have hqBias : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb ≤
          Real.log (T.S.n k : ℝ) ^ κ.Cb :=
        Real.rpow_le_rpow (by positivity) hq hCb.le
      have hown' : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
          10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb / (T.S.n k : ℝ) := by
        simpa [OwnDegOK, hmode] using hown
      have hnum : 0 ≤ 10 * Real.log (T.S.n k : ℝ) ^ κ.Cb := by positivity
      have hratio : 10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb /
          (T.S.n k : ℝ) ≤ 10 * Real.log (T.S.n k : ℝ) ^ κ.Cb /
            (T.S.n k : ℝ) := by
        have hnumq := mul_le_mul_of_nonneg_left hqBias (by norm_num : (0 : ℝ) ≤ 10)
        exact div_le_div_of_nonneg_right hnumq (by positivity)
      have hratio' : 10 * Real.log (T.S.n k : ℝ) ^ κ.Cb /
          (T.S.n k : ℝ) ≤ 10 * Real.log (T.S.n k : ℝ) ^ κ.Cb /
            (T.S.n k : ℝ) ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left hnum hrootPos hrootLe
      exact le_trans hown' (le_trans hratio (le_trans hratio' (le_of_lt hclu)))
  | highDirect => simp [Mode.isLow, hmode] at hLow
  | highSmall => simp [Mode.isLow, hmode] at hLow
  | highLarge => simp [Mode.isLow, hmode] at hLow

private theorem critical_cell_survival_lower {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hκ : κ.Admissible) (hD : D.Spec)
    (htol : κ.Kbd / (T.S.n k : ℝ) ^ (1 / 2 : ℝ) < 1 / 100 ∧
      4 * κ.KB * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ)) < 1 / 100 ∧
      10 * (Real.log (T.S.n k : ℝ) ^ κ.Cb) / (T.S.n k : ℝ) ^ (1 / 2 : ℝ) < 1 / 100 ∧
      κ.KB * Real.rpow (T.S.n k : ℝ) (-3) ≤ 1 / 100 ∧
      1 ≤ Real.log (T.S.n k : ℝ) ∧ 1 ≤ (T.S.n k : ℝ))
    (Xgeo : TransferGeometry X) {a : Fin (T.S.n k)} (ha : a ∈ X.criticalCoords)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hallowed : X.allowed x z) :
    (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
      Hits (T.S.E k) PT.tiling.c x
        (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a)) ∧
      ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y
        (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a))) ≥ 0.15 := by
  rcases htol with ⟨hbd, hdir, hclu, hdelta, hlog, hn⟩
  obtain ⟨hodd, hpatch, hclass⟩ := critical_label_geometry X ha
  let i := D.geom.patchOf X.target
  rcases hallowed with ⟨hx, hz⟩
  have hdegx := low_profile_degree_close hκ hPT D.low_mode i x hx hbd hdir hclu hn hlog
  have hdegxLower : (1 / 2 : ℝ) - 1 / 100 ≤ deg (T.S.E k) PT.tiling.c
      (PT.π i).w x := by
    have h := (abs_le.mp hdegx).1
    nlinarith
  have hdegxLabel : (1 / 2 : ℝ) - 1 / 100 ≤ deg (T.S.E k) PT.tiling.c
      (PT.π (D.geom.patchOf (flipPos X.target a))).w x := by
    simpa [i, hpatch] using hdegxLower
  cases z with
  | none =>
      simpa using fresh_label_hit_lower_single hD (flipPos X.target a) hodd hclass x hdegxLabel hdelta
  | some y =>
      have hyz := hz y rfl
      rcases hyz with ⟨hy, hnonconflict⟩
      have hdegy := low_profile_degree_close hκ hPT D.low_mode i y hy hbd hdir hclu hn hlog
      have hdegzLower : (1 / 2 : ℝ) - 1 / 100 ≤ deg (T.S.E k) PT.tiling.c
          (PT.π i).w y := by
        have h := (abs_le.mp hdegy).1
        nlinarith
      have hdegzLabel : (1 / 2 : ℝ) - 1 / 100 ≤ deg (T.S.E k) PT.tiling.c
          (PT.π (D.geom.patchOf (flipPos X.target a))).w y := by
        simpa [i, hpatch] using hdegzLower
      have hcorr : |pairCorr (T.S.E k) true
          (PT.π (D.geom.patchOf (flipPos X.target a))) x y| ≤ 1 / 100 := by
        have hbase : |pairCorr (T.S.E k) true (PT.π (D.geom.patchOf X.target)) x y| ≤ κ.ξ := by
          simpa [LateData.nonconflict] using hnonconflict
        rw [← hpatch] at hbase
        have hξ : κ.ξ ≤ 1 / 100 := by
          have hbound := hκ.ξ_rng.2
          have hα : 0 < κ.α := hκ.α_rng.1
          have hαu : κ.α < 1 / 100 := by
            have h := hκ.α_rng.2
            norm_num at h
            exact h
          have hu : 0 ≤ (κ.u : ℝ) := by positivity
          have hexp : -(10 * (κ.u : ℝ) + 100) ≤ 0 := by nlinarith
          have hrpow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
          have hmul := mul_le_mul_of_nonneg_left hrpow hα.le
          have hmul' : κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ κ.α := by
            simpa using hmul
          exact le_of_lt (lt_trans (lt_of_lt_of_le hbound hmul') hαu)
        exact le_trans hbase hξ
      simpa [Option.some.injEq] using
        fresh_label_hit_lower_pair hD (flipPos X.target a) hodd hclass x y
          hdegxLabel hdegzLabel hcorr hdelta

private theorem critical_cell_survival_upper {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hD : D.Spec) {a : Fin (T.S.n k)}
    (ha : a ∈ X.criticalCoords) (x : Fin (T.S.N k))
    (z : Option (Fin (T.S.N k))) :
    (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
      Hits (T.S.E k) PT.tiling.c x
        (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a)) ∧
      ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y
        (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a))) ≤
      match z with
      | none =>
          (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
            deg (T.S.E k) PT.tiling.c
              (PT.π (D.geom.patchOf (flipPos X.target a))).w x
      | some y =>
          (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
            ((deg (T.S.E k) PT.tiling.c
                (PT.π (D.geom.patchOf (flipPos X.target a))).w x +
              deg (T.S.E k) PT.tiling.c
                (PT.π (D.geom.patchOf (flipPos X.target a))).w y) / 2 - 1 / 4 +
              corr (T.S.E k) PT.tiling.c
                (PT.π (D.geom.patchOf (flipPos X.target a))).w x y / 4) := by
  obtain ⟨hodd, _, hclass⟩ := critical_label_geometry X ha
  cases z with
  | none =>
      simpa using fresh_label_hit_upper_single hD (flipPos X.target a) hodd hclass x
  | some y =>
      simpa [Option.some.injEq] using
        fresh_label_hit_upper_pair hD (flipPos X.target a) hodd hclass x y

theorem critical_raw_single_survival_upper {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hD : D.Spec) (hgeom : TransferGeometry X)
    (x : Fin (T.S.N k)) :
    X.rawLaw.pr (fun s => X.survives s x none) ≤
      ((1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
        deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf X.target)).w x) ^
          X.criticalCoords.card := by
  let i := D.geom.patchOf X.target
  let u := (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
    deg (T.S.E k) PT.tiling.c (PT.π i).w x
  have hKB : 0 ≤ κ.KB := le_trans
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10 ^ 6) (by positivity)) D.constants.KB_big
  have hc : 0 ≤ 1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3) := by
    have hr : 0 ≤ Real.rpow (T.S.n k : ℝ) (-3) := Real.rpow_nonneg (by positivity) _
    exact add_nonneg (by norm_num) (mul_nonneg hKB hr)
  have hdeg : 0 ≤ deg (T.S.E k) PT.tiling.c (PT.π i).w x := by
    unfold deg hit
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg ((PT.π i).nonneg y) (by split_ifs <;> norm_num)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hcell : ∀ a ∈ X.criticalCoords,
      (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
        Hits (T.S.E k) PT.tiling.c x
          (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a)) ∧
        ∀ y, none = some y → Hits (T.S.E k) PT.tiling.c y
          (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a))) ≤ u := by
    intro a ha
    obtain ⟨_, hpatch, _⟩ := critical_label_geometry X ha
    have h := critical_cell_survival_upper hD ha x none
    simpa [u, i, hpatch] using h
  simpa [u, i] using critical_survival_probability_le hgeom x none u hu hcell

theorem critical_raw_pair_survival_upper {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} {D : LateData hPT}
    {X : CriticalTransferData D} (hD : D.Spec) (hgeom : TransferGeometry X)
    (x y : Fin (T.S.N k)) :
    X.rawLaw.pr (fun s => X.survives s x (some y)) ≤
      ((1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
        ((deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf X.target)).w x +
          deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf X.target)).w y) / 2 - 1 / 4 +
          corr (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf X.target)).w x y / 4)) ^
          X.criticalCoords.card := by
  let i := D.geom.patchOf X.target
  let base := (deg (T.S.E k) PT.tiling.c (PT.π i).w x +
    deg (T.S.E k) PT.tiling.c (PT.π i).w y) / 2 - 1 / 4 +
    corr (T.S.E k) PT.tiling.c (PT.π i).w x y / 4
  let u := (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) * base
  have hKB : 0 ≤ κ.KB := le_trans
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10 ^ 6) (by positivity)) D.constants.KB_big
  have hc : 0 ≤ 1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3) := by
    have hr : 0 ≤ Real.rpow (T.S.n k : ℝ) (-3) := Real.rpow_nonneg (by positivity) _
    exact add_nonneg (by norm_num) (mul_nonneg hKB hr)
  have hbase : 0 ≤ base := by
    dsimp [base]
    rw [← pairHitMass_identity (T.S.E k) PT.tiling.c (PT.π i) x y]
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg ((PT.π i).nonneg z) (by split_ifs <;> norm_num)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hcell : ∀ a ∈ X.criticalCoords,
      (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
        Hits (T.S.E k) PT.tiling.c x
          (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a)) ∧
        ∀ z, some y = some z → Hits (T.S.E k) PT.tiling.c z
          (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a))) ≤ u := by
    intro a ha
    obtain ⟨_, hpatch, _⟩ := critical_label_geometry X ha
    have h := critical_cell_survival_upper hD ha x (some y)
    simpa [u, base, i, hpatch] using h
  simpa [u, base, i] using critical_survival_probability_le hgeom x (some y) u hu hcell

theorem likelihood_nonneg (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) (t : ℕ) :
    0 ≤ likelihood P seed x z s t := by
  unfold likelihood
  exact div_nonneg
    (finLaw_pr_nonneg (tiltedLaw X x z)
      (fun s' => P.replies seed s' t = P.replies seed s t))
    (finLaw_pr_nonneg X.rawLaw
      (fun s' => P.replies seed s' t = P.replies seed s t))

theorem likelihood_one_at_zero (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) :
    likelihood P seed x z s 0 = 1 := by
  classical
  simp [likelihood, P.replies_zero, finLaw_pr_true]

theorem stoppingTime_le_steps (P : TransferProtocol X) (seed : P.Seed)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) (cstop : ℝ) :
    stoppingTime P seed x z s cstop ≤ P.steps := by
  classical
  dsimp only [stoppingTime]
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    have hrange : (Finset.range (P.steps + 1)).filter (fun t =>
        factorException P seed x z s t ∨
          Real.exp (Real.rpow (T.S.n k : ℝ) cstop) < likelihood P seed x z s t)
        ⊆ Finset.range (P.steps + 1) := Finset.filter_subset _ _
    have hm' := hrange hm
    have hlt : (Finset.min' _ h) < P.steps + 1 := by
      simpa only [Finset.mem_range] using hm'
    omega
  · omega

theorem critical_cell_hit_bound_eventually {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in (Filter.atTop : Filter ℕ), ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ X : CriticalTransferData D,
        TransferGeometry X →
        ∀ a, a ∈ X.criticalCoords → ∀ x z, X.allowed x z →
          (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
            Hits (T.S.E k) PT.tiling.c x
              (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a)) ∧
            ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y
              (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a))) ≥ 0.15 := by
  classical
  filter_upwards [eventually_degree_tolerances T] with k htol
  intro PT hPT D hD X hgeom a ha x z hallowed
  exact critical_cell_survival_lower hκ hD htol hgeom ha x z hallowed

theorem protocol_cylinder_facts (P : TransferProtocol X) : CylinderFacts P := by
  classical
  intro seed t transcript ht
  let cylinders : Fin (T.S.n k) → X.Raw → Prop := fun a s =>
    transcript.length = t ∧ ∀ i, i < t →
      P.request seed (transcript.take i) = a →
        P.answer seed (transcript.take i) s = transcript.getD i P.defaultReply
  refine ⟨cylinders, ?_, ?_⟩
  · intro a s s' hss
    change (transcript.length = t ∧ ∀ i, i < t →
      P.request seed (transcript.take i) = a →
        P.answer seed (transcript.take i) s = transcript.getD i P.defaultReply) ↔
      (transcript.length = t ∧ ∀ i, i < t →
      P.request seed (transcript.take i) = a →
        P.answer seed (transcript.take i) s' = transcript.getD i P.defaultReply)
    constructor
    · rintro ⟨hlen, hc⟩
      refine ⟨hlen, ?_⟩
      intro i hi hreq
      have hl := P.answer_local seed (transcript.take i) s s' (by
        intro C hC
        exact hss C (by simpa [hreq] using hC))
      calc
        P.answer seed (transcript.take i) s' = P.answer seed (transcript.take i) s := hl.symm
        _ = transcript.getD i P.defaultReply := hc i hi hreq
    · rintro ⟨hlen, hc⟩
      refine ⟨hlen, ?_⟩
      intro i hi hreq
      have hl := P.answer_local seed (transcript.take i) s s' (by
        intro C hC
        exact hss C (by simpa [hreq] using hC))
      calc
        P.answer seed (transcript.take i) s = P.answer seed (transcript.take i) s' := hl
        _ = transcript.getD i P.defaultReply := hc i hi hreq
  · intro s
    change (P.replies seed s t = transcript ↔ ∀ a, cylinders a s)
    constructor
    · intro hrep
      have hpath := (replies_eq_iff_path P seed s t transcript).1 hrep
      refine fun a => ⟨hpath.1, ?_⟩
      intro i hi _
      exact hpath.2 i hi
    · intro hall
      have hseed : Nonempty P.Seed := by
        by_contra hn
        letI : IsEmpty P.Seed := not_nonempty_iff.mp hn
        have hs := P.seedLaw.sum_one
        simp at hs
      have a₀ : Fin (T.S.n k) := P.request (Classical.choice hseed) []
      have hpath₀ := hall a₀
      have hlen : transcript.length = t := hpath₀.1
      have hpath : ∀ i, i < t →
          P.answer seed (transcript.take i) s = transcript.getD i P.defaultReply := by
        intro i hi
        exact (hall (P.request seed (transcript.take i))).2 i hi rfl
      exact (replies_eq_iff_path P seed s t transcript).2 ⟨hlen, hpath⟩

end HypercubeRamsey.S18.Lane_q_s18_n3
