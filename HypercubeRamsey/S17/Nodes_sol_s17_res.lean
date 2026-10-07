import HypercubeRamsey.S17.Nodes_q_s17_res1
import Mathlib.Order.WellFounded
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace HypercubeRamsey.Lane_sol_s17_res

open Classical
open scoped BigOperators

abbrev TreeCode (m : ℕ) := (Fin m → Fin m) × (Fin m → Fin m)

def TreeSpec {m : ℕ} (Q : TreeCode m) : Prop :=
  (∀ j : Fin m, j.val = 0 → (Q.1 j).val = 0 ∧ (Q.2 j).val = 0) ∧
  (∀ j : Fin m, 0 < j.val →
    (Q.2 j).val < j.val ∧ (Q.1 j).val = (Q.1 (Q.2 j)).val + 1 ∧
    ∀ i : Fin m, (Q.2 j).val < i.val → i.val < j.val →
      (Q.1 j).val ≤ (Q.1 i).val)

private theorem depth_le_index {m : ℕ} {Q : TreeCode m} (hQ : TreeSpec Q)
    (j : Fin m) : (Q.1 j).val ≤ j.val := by
  have h : ∀ n, ∀ j : Fin m, j.val = n → (Q.1 j).val ≤ j.val := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      by_cases hz : j.val = 0
      · exact le_of_eq (by simpa [hz] using (hQ.1 j hz).1)
      · obtain ⟨hp, hd, _⟩ := hQ.2 j (by omega)
        have hb := ih (Q.2 j).val (by omega) (Q.2 j) rfl
        omega
  exact h j.val j rfl

private theorem depth_step {m : ℕ} {Q : TreeCode m} (hQ : TreeSpec Q)
    (i j : Fin m) (hj : j.val = i.val + 1) :
    (Q.1 j).val ≤ (Q.1 i).val + 1 := by
  obtain ⟨hp, hd, hi⟩ := hQ.2 j (by omega)
  by_cases he : Q.2 j = i
  · simpa [he] using le_of_eq hd
  · have hlt : (Q.2 j).val < i.val := by
      have hne : (Q.2 j).val ≠ i.val := fun h => he (Fin.ext h)
      omega
    exact (hi i hlt (by omega)).trans (by omega)

private def opening {m : ℕ} (Q : {Q : TreeCode m // TreeSpec Q})
    (j : Fin m) : Fin (2 * m) :=
  ⟨2 * j.val - (Q.1.1 j).val, by omega⟩

private theorem opening_strictMono {m : ℕ}
    (Q : {Q : TreeCode m // TreeSpec Q}) : StrictMono (opening Q) := by
  cases m with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have h1 := depth_le_index Q.2 i.castSucc
    have h2 := depth_le_index Q.2 i.succ
    have hs := depth_step Q.2 i.castSucc i.succ (by simp)
    change 2 * i.val - (Q.1.1 i.castSucc).val <
      2 * (i.val + 1) - (Q.1.1 i.succ).val
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2 hs
    omega

private theorem tree_eq_of_depth_eq {m : ℕ} {Q R : TreeCode m}
    (hQ : TreeSpec Q) (hR : TreeSpec R) (hd : Q.1 = R.1) : Q = R := by
  apply Prod.ext hd
  funext j
  by_cases hz : j.val = 0
  · apply Fin.ext
    exact (hQ.1 j hz).2.trans (hR.1 j hz).2.symm
  · obtain ⟨hp, hdepth, hint⟩ := hQ.2 j (by omega)
    obtain ⟨rp, rdepth, rint⟩ := hR.2 j (by omega)
    apply Fin.ext
    have hjd : (Q.1 j).val = (R.1 j).val := congrArg (fun f => (f j).val) hd
    have hpd : (Q.1 (Q.2 j)).val = (R.1 (Q.2 j)).val :=
      congrArg (fun f => (f (Q.2 j)).val) hd
    have hrd : (Q.1 (R.2 j)).val = (R.1 (R.2 j)).val :=
      congrArg (fun f => (f (R.2 j)).val) hd
    rcases lt_trichotomy (Q.2 j).val (R.2 j).val with hlt | he | hlt
    · have hh := hint (R.2 j) hlt rp
      omega
    · exact he
    · have hh := rint (Q.2 j) hlt hp
      omega

private def shapeEncoding {m : ℕ} (Q : {Q : TreeCode m // TreeSpec Q}) :
    Finset (Fin (2 * m)) := Finset.univ.image (opening Q)

private theorem shapeEncoding_injective {m : ℕ} :
    Function.Injective (shapeEncoding (m := m)) := by
  intro Q R h
  have hr : Set.range (opening Q) = Set.range (opening R) := by
    ext x
    have hm := congrArg (fun s : Finset (Fin (2 * m)) => x ∈ s) h
    simpa [shapeEncoding] using hm
  have hopen := (opening_strictMono Q).range_inj_of_wellFoundedLT (opening_strictMono R) |>.mp hr
  apply Subtype.ext
  apply tree_eq_of_depth_eq Q.2 R.2
  funext j
  apply Fin.ext
  have hh := congrArg (fun f => (f j).val) hopen
  have hQ := depth_le_index Q.2 j
  have hR := depth_le_index R.2 j
  change 2 * j.val - (Q.1.1 j).val = 2 * j.val - (R.1.1 j).val at hh
  omega

theorem tree_card_le (m : ℕ) :
    Fintype.card {Q : TreeCode m // TreeSpec Q} ≤ 4 ^ m := by
  classical
  calc
    Fintype.card {Q : TreeCode m // TreeSpec Q} ≤
        Fintype.card (Finset (Fin (2 * m))) :=
      Fintype.card_le_of_injective shapeEncoding shapeEncoding_injective
    _ = 4 ^ m := by
      simp only [Fintype.card_finset, Fintype.card_fin]
      rw [pow_mul]
      norm_num

private noncomputable def localRank {α : Type*} [Fintype α]
    (b : ℕ) (B : α → Finset α) (hB : ∀ x, (B x).card ≤ b)
    (x : α) (y : {y : α // y ∈ B x}) : Fin b :=
  let r := Fintype.equivFin {y : α // y ∈ B x} y
  ⟨r.val, by
    have hh : Fintype.card {y : α // y ∈ B x} ≤ b := by
      simpa only [Fintype.card_coe] using hB x
    exact lt_of_lt_of_le r.isLt hh⟩

private theorem localRank_injective {α : Type*} [Fintype α]
    (b : ℕ) (B : α → Finset α) (hB : ∀ x, (B x).card ≤ b) (x : α) :
    Function.Injective (localRank b B hB x) := by
  intro y z h
  apply (Fintype.equivFin {y : α // y ∈ B x}).injective
  apply Fin.ext
  have hh := congrArg (fun z : Fin b => z.val) h
  exact hh

private theorem localRank_eq {α : Type*} [Fintype α]
    (b : ℕ) (B : α → Finset α) (hB : ∀ x, (B x).card ≤ b)
    (x z y w : α) (hy : y ∈ B x) (hw : w ∈ B z) (hxz : x = z)
    (hr : localRank b B hB x ⟨y, hy⟩ = localRank b B hB z ⟨w, hw⟩) : y = w := by
  subst z
  exact congrArg Subtype.val (localRank_injective b B hB x hr)

def LocalLabels {α : Type*} {m : ℕ} (p : Fin m → Fin m)
    (B : α → Finset α) (root : α) (f : Fin m → α) : Prop :=
  ∀ j, f j ∈ B (if j.val = 0 then root else f (p j))

private noncomputable def labelEncoding {α : Type*} [Fintype α]
    {m : ℕ} (p : Fin m → Fin m) (B : α → Finset α)
    (b : ℕ) (hB : ∀ x, (B x).card ≤ b) (root : α)
    (f : {f : Fin m → α // LocalLabels p B root f}) : Fin m → Fin b :=
  fun j => localRank b B hB (if j.val = 0 then root else f.1 (p j))
    ⟨f.1 j, f.2 j⟩

private theorem labelEncoding_injective {α : Type*} [Fintype α]
    {m : ℕ} (p : Fin m → Fin m) (hp : ∀ j, 0 < j.val → (p j).val < j.val)
    (B : α → Finset α) (b : ℕ) (hB : ∀ x, (B x).card ≤ b) (root : α) :
    Function.Injective (labelEncoding p B b hB root) := by
  intro f g he
  apply Subtype.ext
  funext j
  have aux : ∀ n, ∀ j : Fin m, j.val = n → f.1 j = g.1 j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      have hs : (if j.val = 0 then root else f.1 (p j)) =
          (if j.val = 0 then root else g.1 (p j)) := by
        by_cases hz : j.val = 0
        · simp [hz]
        · simp only [hz, if_false]
          exact ih (p j).val (by have := hp j (by omega); omega) (p j) rfl
      have hr := congrFun he j
      change localRank b B hB _ ⟨f.1 j, f.2 j⟩ =
        localRank b B hB _ ⟨g.1 j, g.2 j⟩ at hr
      exact localRank_eq b B hB _ _ _ _ (f.2 j) (g.2 j) hs hr
  exact aux j.val j rfl

theorem localLabels_card_le {α : Type*} [Fintype α]
    {m : ℕ} (p : Fin m → Fin m) (hp : ∀ j, 0 < j.val → (p j).val < j.val)
    (B : α → Finset α) (b : ℕ) (hB : ∀ x, (B x).card ≤ b) (root : α) :
    Fintype.card {f : Fin m → α // LocalLabels p B root f} ≤ b ^ m := by
  classical
  calc
    Fintype.card {f : Fin m → α // LocalLabels p B root f} ≤
        Fintype.card (Fin m → Fin b) :=
      Fintype.card_le_of_injective (labelEncoding p B b hB root)
        (labelEncoding_injective p hp B b hB root)
    _ = b ^ m := by simp [Fintype.card_fun]

private theorem shift_val {m : ℕ} (p i : Fin m) :
    (p.succ.succAbove i).val = if i.val ≤ p.val then i.val else i.val + 1 := by
  by_cases h : i.val ≤ p.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt]
    · rfl
    · change i.val < p.val + 1
      omega
  · rw [if_neg h, Fin.succAbove_of_le_castSucc]
    · rfl
    · change p.val + 1 ≤ i.val
      omega

private def insertTree {m : ℕ} (Q : TreeCode m) (p : Fin m) : TreeCode (m + 1) :=
  (Fin.insertNth p.succ ⟨(Q.1 p).val + 1, by have := (Q.1 p).isLt; omega⟩
    (fun i => (Q.1 i).castSucc),
   Fin.insertNth p.succ (p.succ.succAbove p)
    (fun i => p.succ.succAbove (Q.2 i)))

private theorem insertTree_spec {m : ℕ} {Q : TreeCode m} (hQ : TreeSpec Q)
    (p : Fin m) : TreeSpec (insertTree Q p) := by
  let a := p.succ
  have hv (i : Fin m) := shift_val p i
  have hmono := Fin.strictMono_succAbove a
  constructor
  · intro j hj
    rcases Fin.eq_self_or_eq_succAbove a j with rfl | ⟨i, rfl⟩
    · change p.val + 1 = 0 at hj
      omega
    · have hi : i.val = 0 := by
        change (p.succ.succAbove i).val = 0 at hj
        have hh := hv i
        split_ifs at hh <;> omega
      obtain ⟨hd, hp⟩ := hQ.1 i hi
      simp only [insertTree, a, Fin.insertNth_apply_succAbove, Fin.val_castSucc]
      constructor
      · exact hd
      · have hh := hv (Q.2 i)
        split_ifs at hh <;> omega
  · intro j hj
    rcases Fin.eq_self_or_eq_succAbove a j with rfl | ⟨i, rfl⟩
    · simp only [insertTree, a, Fin.insertNth_apply_same]
      refine ⟨?_, ?_, ?_⟩
      · have hh := hv p
        simp only [le_refl, if_true] at hh
        change (p.succ.succAbove p).val < p.val + 1
        omega
      · simp only [Fin.insertNth_apply_succAbove, Fin.val_castSucc]
      · intro i hi hj
        have hh := hv p
        simp only [le_refl, if_true] at hh
        change (p.succ.succAbove p).val < i.val at hi
        change i.val < p.val + 1 at hj
        omega
    · have hi : 0 < i.val := by
        change 0 < (p.succ.succAbove i).val at hj
        have hh := hv i
        split_ifs at hh <;> omega
      obtain ⟨hp, hd, hint⟩ := hQ.2 i hi
      simp only [insertTree, a, Fin.insertNth_apply_succAbove, Fin.val_castSucc]
      refine ⟨?_, ?_, ?_⟩
      · exact hmono hp
      · exact hd
      · intro j hj1 hj2
        rcases Fin.eq_self_or_eq_succAbove a j with rfl | ⟨l, rfl⟩
        · simp only [a, Fin.insertNth_apply_same]
          have hh1 := hv (Q.2 i)
          have hh2 := hv i
          change (p.succ.succAbove (Q.2 i)).val < p.val + 1 at hj1
          change p.val + 1 < (p.succ.succAbove i).val at hj2
          have hqp : (Q.2 i).val ≤ p.val := by split_ifs at hh1 <;> omega
          have hpi : p.val < i.val := by split_ifs at hh2 <;> omega
          by_cases he : Q.2 i = p
          · simpa [he] using le_of_eq hd
          · have hlt : (Q.2 i).val < p.val := by
              have hne : (Q.2 i).val ≠ p.val := fun h => he (Fin.ext h)
              omega
            exact (hint p hlt hpi).trans (by omega)
        · simp only [a, Fin.insertNth_apply_succAbove, Fin.val_castSucc]
          exact hint l (hmono.lt_iff_lt.mp hj1) (hmono.lt_iff_lt.mp hj2)

private def Encoded {α : Type*} [DecidableEq α] (R : α → α → Prop)
    (root : α) (s : Finset α) : Prop :=
  ∃ m, ∃ hm : 0 < m, ∃ Q : TreeCode m, ∃ f : Fin m → α,
    TreeSpec Q ∧ Function.Injective f ∧ Finset.univ.image f = s ∧
      f ⟨0, hm⟩ = root ∧ ∀ j, 0 < j.val → R (f (Q.2 j)) (f j)

private theorem encoded_singleton {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (root : α) : Encoded R root {root} := by
  refine ⟨1, by omega, (fun _ => 0, fun _ => 0), (fun _ => root), ?_, ?_, ?_, rfl, ?_⟩
  · constructor
    · intro j hj; simp
    · intro j hj; omega
  · intro i j h; exact Subsingleton.elim _ _
  · simp
  · intro j hj; omega

private theorem encoded_insert {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (root : α) {s : Finset α} (h : Encoded R root s)
    {x y : α} (hx : x ∈ s) (hy : y ∉ s) (hR : R x y) :
    Encoded R root (insert y s) := by
  obtain ⟨m, hm, Q, f, hQ, hf, hs, hroot, hedge⟩ := h
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (hs.symm ▸ hx)
  let a := p.succ
  let g : Fin (m + 1) → α := Fin.insertNth a y f
  have hgnew : g a = y := by simp [g]
  have hgold (i : Fin m) : g (a.succAbove i) = f i := by simp [g]
  have hyf (i : Fin m) : y ≠ f i := by
    intro he
    apply hy
    rw [← hs, he]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  refine ⟨m + 1, by omega, insertTree Q p, g, insertTree_spec hQ p, ?_, ?_, ?_, ?_⟩
  · intro i j he
    rcases Fin.eq_self_or_eq_succAbove a i with rfl | ⟨i, rfl⟩ <;>
      rcases Fin.eq_self_or_eq_succAbove a j with rfl | ⟨j, rfl⟩
    · rfl
    · simp only [hgnew, hgold] at he
      exact (hyf j he).elim
    · simp only [hgnew, hgold] at he
      exact (hyf i he.symm).elim
    · exact congrArg a.succAbove (hf (by simpa only [hgold] using he))
  · ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      ← hs]
    constructor
    · rintro ⟨i, hi⟩
      rcases Fin.eq_self_or_eq_succAbove a i with rfl | ⟨i, rfl⟩
      · exact Or.inl (by simpa only [hgnew] using hi.symm)
      · exact Or.inr ⟨i, by simpa only [hgold] using hi⟩
    · rintro (rfl | ⟨i, hi⟩)
      · exact ⟨a, hgnew⟩
      · exact ⟨a.succAbove i, (hgold i).trans hi⟩
  · have hz : a.succAbove (⟨0, hm⟩ : Fin m) = (⟨0, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      have hh := shift_val p (⟨0, hm⟩ : Fin m)
      simpa only [Nat.zero_le, if_true] using hh
    rw [← hz, hgold]
    exact hroot
  · intro j hj
    rcases Fin.eq_self_or_eq_succAbove a j with rfl | ⟨i, rfl⟩
    · simpa only [insertTree, a, Fin.insertNth_apply_same, hgold, hgnew, hp] using hR
    · have hi : 0 < i.val := by
        have hh := shift_val p i
        change 0 < (p.succ.succAbove i).val at hj
        split_ifs at hh <;> omega
      simpa only [insertTree, a, Fin.insertNth_apply_succAbove, hgold] using hedge i hi

private theorem encoded_extend_path {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (root : α) (s : Finset α) {t : Finset α}
    (ht : t ⊆ s) (hEnc : Encoded R root t) {x : α}
    (hpath : Relation.ReflTransGen (fun a b => a ∈ s ∧ b ∈ s ∧ R a b) root x) :
    ∃ u, t ⊆ u ∧ u ⊆ s ∧ Encoded R root u ∧ x ∈ u := by
  induction hpath with
  | refl =>
    obtain ⟨m, hm, Q, f, hQ, hf, hs, hr, he⟩ := hEnc
    refine ⟨t, Finset.Subset.refl _, ht, ?_, ?_⟩
    · exact ⟨m, hm, Q, f, hQ, hf, hs, hr, he⟩
    · rw [← hs, ← hr]
      exact Finset.mem_image.mpr ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩
  | @tail b c hab hbc ih =>
    obtain ⟨u, htu, hus, hEu, hbu⟩ := ih
    by_cases hc : c ∈ u
    · exact ⟨u, htu, hus, hEu, hc⟩
    · refine ⟨insert c u, htu.trans (Finset.subset_insert _ _), ?_,
        encoded_insert R root hEu hbu hc hbc.2.2, by simp⟩
      exact Finset.insert_subset hbc.2.1 hus

theorem spanning_preorder {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (root : α) (s : Finset α) (hroot : root ∈ s)
    (hconn : ∀ x ∈ s,
      Relation.ReflTransGen (fun a b => a ∈ s ∧ b ∈ s ∧ R a b) root x) :
    ∃ m, ∃ hm : 0 < m, ∃ Q : TreeCode m, ∃ f : Fin m → α,
      TreeSpec Q ∧ Function.Injective f ∧ Finset.univ.image f = s ∧
        f ⟨0, hm⟩ = root ∧ ∀ j, 0 < j.val → R (f (Q.2 j)) (f j) := by
  have aux : ∀ X : Finset α, X ⊆ s →
      ∃ u, u ⊆ s ∧ Encoded R root u ∧ X ⊆ u := by
    intro X
    induction X using Finset.induction_on with
    | empty =>
      intro h
      exact ⟨{root}, by simpa using hroot, encoded_singleton R root,
        Finset.empty_subset _⟩
    | @insert a X ha ih =>
      intro hX
      obtain ⟨u, hus, hEu, hXu⟩ := ih ((Finset.subset_insert _ _).trans hX)
      obtain ⟨v, huv, hvs, hEv, hav⟩ :=
        encoded_extend_path R root s hus hEu (hconn a (hX (by simp)))
      exact ⟨v, hvs, hEv, Finset.insert_subset hav (hXu.trans huv)⟩
  obtain ⟨u, hus, hEu, hsu⟩ := aux s (Finset.Subset.refl _)
  have heq : u = s := Finset.Subset.antisymm hus hsu
  subst u
  exact hEu

end HypercubeRamsey.Lane_sol_s17_res
