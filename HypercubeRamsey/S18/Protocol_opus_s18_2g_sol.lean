import HypercubeRamsey.S18.Run_sol_s18_n4

namespace HypercubeRamsey.S18.Lane_sol_s18_2g_o2

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : LateData hPT)

theorem beforeHistory_self (i : Fin (D.geom.r + 1))
    (h : D.encoding.base.History i) : D.beforeHistory h i le_rfl = h := by
  apply Prod.ext
  · rfl
  · funext b
    rfl

section Trajectory

variable (H : ∀ i : Fin (D.geom.r + 1), D.encoding.base.History i)
    (rows : ∀ j : Fin D.geom.r, D.encoding.base.ClassRows j)
    (hstep : ∀ j : Fin D.geom.r,
      H j.succ = D.encoding.base.extend j (H j.castSucc) (rows j))

include hstep

theorem beforeHistory_of_extends (i t : Fin (D.geom.r + 1)) (hit : i.val ≤ t.val) :
    D.beforeHistory (H t) i hit = H i := by
  revert hit
  induction t using Fin.induction with
  | zero =>
    intro hit
    have hi : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hit)
    subst i
    exact beforeHistory_self D _ _
  | succ j ih =>
    intro hit
    by_cases heq : i = j.succ
    · subst i
      exact beforeHistory_self D _ _
    · have hne : i.val ≠ j.val + 1 := fun hv => heq (Fin.ext hv)
      have hit' : i.val ≤ j.val + 1 := hit
      have hij : i.val ≤ j.val := by omega
      rw [hstep j, Lane_sol_s18_n4.beforeHistory_extend D i j hij]
      exact ih hij

theorem pastRows_of_extends (j : Fin D.geom.r) (t : Fin (D.geom.r + 1))
    (hjt : j.val < t.val) : D.pastRows (H t) j hjt = rows j := by
  revert hjt
  induction t using Fin.induction with
  | zero =>
    intro hjt
    change j.val < 0 at hjt
    omega
  | succ i ih =>
    intro hjt
    by_cases heq : j = i
    · subst j
      rw [hstep i, Lane_sol_s18_n4.pastRows_extend_self]
    · have hne : j.val ≠ i.val := fun hv => heq (Fin.ext hv)
      have hjt' : j.val < i.val + 1 := hjt
      have hji : j.val < i.val := by omega
      rw [hstep i, Lane_sol_s18_n4.pastRows_extend_earlier D j i hji]
      exact ih hji

end Trajectory

theorem idxOf_lt_of_key_lt {α : Type*} [BEq α] [LawfulBEq α]
    (l : List α) (key : α → ℕ) (hsorted : l.Pairwise (fun a b => key a ≤ key b))
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : key a < key b) :
    l.idxOf a < l.idxOf b := by
  have ha' := List.idxOf_lt_length_of_mem ha
  have hb' := List.idxOf_lt_length_of_mem hb
  apply Nat.lt_of_not_ge
  intro hle
  by_cases heq : l.idxOf b = l.idxOf a
  · have hba : b = a := by
      calc
        b = l[l.idxOf b] := (List.getElem_idxOf hb').symm
        _ = l[l.idxOf a] := by simp only [heq]
        _ = a := List.getElem_idxOf ha'
    have hf : key a < key a := by simpa only [hba] using hab
    exact Nat.lt_irrefl _ hf
  · have hlt : l.idxOf b < l.idxOf a := by omega
    have hba : key b ≤ key a := by
      simpa only [List.getElem_idxOf] using hsorted.rel_getElem_of_lt hb' ha' hlt
    exact Nat.not_le_of_gt hab hba

end HypercubeRamsey.S18.Lane_sol_s18_2g_o2
