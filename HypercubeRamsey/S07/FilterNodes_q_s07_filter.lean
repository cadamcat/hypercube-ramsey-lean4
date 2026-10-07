import HypercubeRamsey.S07.GeometryNodes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.S07

open Classical
open Filter
open scoped BigOperators

theorem filterMass_nonneg {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) : 0 ≤ filterMass E G ν L := by
  unfold filterMass
  exact Finset.sum_nonneg fun y _ => by split_ifs <;> [exact ν.nonneg y; exact le_rfl]

theorem one_sub_npow_nonneg_q {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ 1 - (n : ℝ) ^ (-2 : ℝ) := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hpow : (n : ℝ) ^ (-2 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num)
  linarith

theorem filt_nonneg_q {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) (y : Fin N) : 0 ≤ filt E G ν L y := by
  by_cases h : 0 < filterMass E G ν L
  · exact (filt_probability_and_support E G ν L h).1 y
  · simp [filt, h]

theorem inv_one_sub_npow_sq_le_exp {n : ℕ} (hn : 2 ≤ n) :
    (1 - (n : ℝ) ^ (-2 : ℝ))⁻¹ ≤ Real.exp (2 * (n : ℝ) ^ (-2 : ℝ)) := by
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  let a : ℝ := (n : ℝ) ^ (-2 : ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpow2 : a ≤ 1 / 4 := by
    dsimp [a]
    calc
      (n : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hnreal (by norm_num)
      _ = 1 / 4 := by
        norm_num [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  have hden : 0 < 1 - a := by linarith
  have hsmallProd : 0 ≤ a * (1 - 2 * a) := mul_nonneg ha (by linarith)
  have hsmall : (1 - a)⁻¹ ≤ 1 + 2 * a := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    nlinarith
  have hexp : 1 + 2 * a ≤ Real.exp (2 * a) := by
    nlinarith [Real.add_one_le_exp (2 * a)]
  simpa [a] using hsmall.trans hexp

theorem delTheta_pos_q {d : ℝ} {n s ℓ q : ℕ}
    (Γ : GridGeom d n s ℓ q) (hn : 2 ≤ n) (hd : 0 ≤ d) (c w : Γ.Cell) :
    0 < delTheta Γ c w := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hbase : 0 < 1 - (n : ℝ) ^ (-2 : ℝ) := by
    have hpow : (n : ℝ) ^ (-2 : ℝ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num)
    linarith
  unfold delTheta
  split_ifs with h
  · exact hbase
  · exact mul_pos hbase (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _)

theorem delTheta_inv_le_exp {d : ℝ} {n s ℓ q : ℕ}
    (Γ : GridGeom d n s ℓ q) (hn : 2 ≤ n) (hd : 0 ≤ d) (c w : Γ.Cell) :
    (delTheta Γ c w)⁻¹ ≤
      Real.exp ((if w.1 = c.1 then 0 else (d / 80) * Real.log (n : ℝ)) +
        2 * (n : ℝ) ^ (-2 : ℝ)) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbaseInv := inv_one_sub_npow_sq_le_exp hn
  by_cases hcw : w.1 = c.1
  · simpa [delTheta, hcw] using hbaseInv
  · have hexpPow : (n : ℝ) ^ (d / 80) = Real.exp ((d / 80) * Real.log (n : ℝ)) := by
      rw [Real.rpow_def_of_pos hnreal]
      congr 1
      ring
    have hinvPow : ((n : ℝ) ^ (-(d / 80)))⁻¹ = (n : ℝ) ^ (d / 80) := by
      rw [Real.rpow_neg (by positivity) (d / 80)]
      simp
    have htheta : delTheta Γ c w =
        (1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ (-(d / 80)) := by
      simp [delTheta, hcw]
    rw [htheta, mul_inv_rev, hinvPow, hexpPow]
    simp only [if_neg hcw]
    calc
      Real.exp ((d / 80) * Real.log (n : ℝ)) *
          (1 - (n : ℝ) ^ (-2 : ℝ))⁻¹ =
        (1 - (n : ℝ) ^ (-2 : ℝ))⁻¹ *
          Real.exp ((d / 80) * Real.log (n : ℝ)) := by ring
      _ ≤ Real.exp (2 * (n : ℝ) ^ (-2 : ℝ)) *
          Real.exp ((d / 80) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hbaseInv (Real.exp_nonneg _)
      _ = Real.exp ((d / 80) * Real.log (n : ℝ) +
          2 * (n : ℝ) ^ (-2 : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem evenCapRemainder_bound (d : ℝ) (hd : 0 < d) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (n : ℝ) ^ (d / 2) + (d / 80) * ((gS d n * gL d n : ℕ) : ℝ) *
          Real.log (n : ℝ) + 2 / (n : ℝ) ≤ (1 / 50 : ℝ) * (gQ d n : ℝ) := by
  have hp₁ : 0 < 7 * d / 2 := by positivity
  have hp₂ : 0 < 4 * d + 1 := by positivity
  have hT₁ : Tendsto (fun n : ℕ => (n : ℝ) ^ (7 * d / 2)) atTop atTop :=
    (tendsto_rpow_atTop hp₁).comp tendsto_natCast_atTop_atTop
  have hT₂ : Tendsto (fun n : ℕ => (n : ℝ) ^ (4 * d + 1)) atTop atTop :=
    (tendsto_rpow_atTop hp₂).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 (hT₁.eventually_ge_atTop (400 : ℝ))
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1 (hT₂.eventually_ge_atTop (800 : ℝ))
  refine ⟨max 1 (max n₁ n₂), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 (max n₁ n₂)) hn
  have hmax : max n₁ n₂ ≤ n := (le_max_right 1 (max n₁ n₂)).trans hn
  have hn₁' : n₁ ≤ n := (le_max_left n₁ n₂).trans hmax
  have hn₂' : n₂ ≤ n := (le_max_right n₁ n₂).trans hmax
  have hpow₁ : (400 : ℝ) ≤ (n : ℝ) ^ (7 * d / 2) :=
    hn₁ n hn₁'
  have hpow₂ : (800 : ℝ) ≤ (n : ℝ) ^ (4 * d + 1) :=
    hn₂ n hn₂'
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hx : 1 ≤ (n : ℝ) ^ d := Real.one_le_rpow hnreal hd.le
  have hs : (gS d n : ℝ) ≤ 2 * (n : ℝ) ^ d := by
    have hceil : (gS d n : ℝ) < (n : ℝ) ^ d + 1 := by
      simpa [gS] using Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ d by positivity)
    dsimp [gS] at hceil ⊢
    linarith
  have hℓ : (gL d n : ℝ) ≤ (n : ℝ) ^ d := by
    dsimp [gL]
    exact Nat.floor_le (show 0 ≤ (n : ℝ) ^ d by positivity)
  have hsℓ : ((gS d n * gL d n : ℕ) : ℝ) ≤
      2 * (n : ℝ) ^ d * (n : ℝ) ^ d := by
    rw [Nat.cast_mul]
    calc
      (gS d n : ℝ) * (gL d n : ℝ) ≤
          (2 * (n : ℝ) ^ d) * (gL d n : ℝ) :=
        mul_le_mul_of_nonneg_right hs (by exact_mod_cast (Nat.zero_le (gL d n)))
      _ ≤ (2 * (n : ℝ) ^ d) * (n : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left hℓ (by positivity)
      _ = 2 * (n : ℝ) ^ d * (n : ℝ) ^ d := rfl
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ (2 * d) / (2 * d) :=
    Real.log_natCast_le_rpow_div n (by positivity)
  have hpowd : (n : ℝ) ^ d * (n : ℝ) ^ d = (n : ℝ) ^ (2 * d) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hpowmul : (n : ℝ) ^ (2 * d) * (n : ℝ) ^ (2 * d) =
      (n : ℝ) ^ (4 * d) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hfilter :
      (d / 80) * ((gS d n * gL d n : ℕ) : ℝ) * Real.log (n : ℝ) ≤
        (1 / 80 : ℝ) * (n : ℝ) ^ (4 * d) := by
    have hcoeff : 0 ≤ d / 80 := div_nonneg hd.le (by norm_num)
    calc
      (d / 80) * ((gS d n * gL d n : ℕ) : ℝ) * Real.log (n : ℝ) =
          ((d / 80) * Real.log (n : ℝ)) *
            ((gS d n * gL d n : ℕ) : ℝ) := by ring
      _ ≤ ((d / 80) * Real.log (n : ℝ)) *
            (2 * (n : ℝ) ^ d * (n : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hsℓ (mul_nonneg hcoeff (Real.log_nonneg hnreal))
      _ ≤ ((d / 80) * (2 * (n : ℝ) ^ d * (n : ℝ) ^ d)) *
            ((n : ℝ) ^ (2 * d) / (2 * d)) := by
          rw [show ((d / 80) * Real.log (n : ℝ)) *
              (2 * (n : ℝ) ^ d * (n : ℝ) ^ d) =
                ((d / 80) * (2 * (n : ℝ) ^ d * (n : ℝ) ^ d)) *
                  Real.log (n : ℝ) by ring]
          exact mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (1 / 80 : ℝ) * (n : ℝ) ^ (4 * d) := by
          have hpowd' : 2 * (n : ℝ) ^ d * (n : ℝ) ^ d =
              2 * (n : ℝ) ^ (2 * d) := by
            calc
              2 * (n : ℝ) ^ d * (n : ℝ) ^ d =
                  2 * ((n : ℝ) ^ d * (n : ℝ) ^ d) := by ring
              _ = 2 * (n : ℝ) ^ (2 * d) := by rw [hpowd]
          rw [hpowd']
          calc
            ((d / 80) * (2 * (n : ℝ) ^ (2 * d)) *
                ((n : ℝ) ^ (2 * d) / (2 * d))) =
                ((d / 80) * (2 / (2 * d))) *
                  ((n : ℝ) ^ (2 * d) * (n : ℝ) ^ (2 * d)) := by ring
            _ = (1 / 80 : ℝ) * (n : ℝ) ^ (4 * d) := by
              rw [hpowmul]
              field_simp [ne_of_gt hd]
  have hmu : (n : ℝ) ^ (d / 2) ≤ (1 / 400 : ℝ) * (n : ℝ) ^ (4 * d) := by
    have hpow : (n : ℝ) ^ (d / 2) * (n : ℝ) ^ (7 * d / 2) =
        (n : ℝ) ^ (4 * d) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    have hm : (400 : ℝ) * (n : ℝ) ^ (d / 2) ≤
        (n : ℝ) ^ (d / 2) * (n : ℝ) ^ (7 * d / 2) := by
      have hm' := mul_le_mul_of_nonneg_left hpow₁
        (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) (d / 2))
      nlinarith
    calc
      (n : ℝ) ^ (d / 2) = (1 / 400 : ℝ) * (400 * (n : ℝ) ^ (d / 2)) := by ring
      _ ≤ (1 / 400 : ℝ) *
            ((n : ℝ) ^ (d / 2) * (n : ℝ) ^ (7 * d / 2)) :=
          mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = (1 / 400 : ℝ) * (n : ℝ) ^ (4 * d) := by rw [hpow]
  have hpowerr : (n : ℝ) ^ (4 * d) * (n : ℝ) =
      (n : ℝ) ^ (4 * d + 1) := by
    calc
      (n : ℝ) ^ (4 * d) * (n : ℝ) =
          (n : ℝ) ^ (4 * d) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ (4 * d + 1) := by rw [← Real.rpow_add hnpos]
  have herr : 2 / (n : ℝ) ≤ (1 / 400 : ℝ) * (n : ℝ) ^ (4 * d) := by
    rw [div_le_iff₀ hnpos]
    calc
      (2 : ℝ) ≤ (1 / 400 : ℝ) * (n : ℝ) ^ (4 * d + 1) := by nlinarith [hpow₂]
      _ = (1 / 400 : ℝ) * (n : ℝ) ^ (4 * d) * (n : ℝ) := by rw [← hpowerr]; ring
  have hrem :
      (n : ℝ) ^ (d / 2) + (d / 80) * ((gS d n * gL d n : ℕ) : ℝ) *
          Real.log (n : ℝ) + 2 / (n : ℝ) ≤ (7 / 400 : ℝ) * (n : ℝ) ^ (4 * d) := by
    calc
      _ ≤ (1 / 400 : ℝ) * (n : ℝ) ^ (4 * d) +
            (1 / 80 : ℝ) * (n : ℝ) ^ (4 * d) +
            (1 / 400 : ℝ) * (n : ℝ) ^ (4 * d) := by
          exact add_le_add (add_le_add hmu hfilter) herr
      _ = (7 / 400 : ℝ) * (n : ℝ) ^ (4 * d) := by ring
  have hq : (n : ℝ) ^ (4 * d) ≤ (gQ d n : ℝ) := by
    dsimp [gQ]
    exact Nat.le_ceil _
  have hcoeff : (7 / 400 : ℝ) ≤ 1 / 50 := by norm_num
  calc
    _ ≤ (7 / 400 : ℝ) * (n : ℝ) ^ (4 * d) := hrem
    _ ≤ (7 / 400 : ℝ) * (gQ d n : ℝ) :=
      mul_le_mul_of_nonneg_left hq (by norm_num)
    _ ≤ (1 / 50 : ℝ) * (gQ d n : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff (by exact_mod_cast (Nat.zero_le (gQ d n)))

theorem filterMass_le_of_mem {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) {L₁ L₂ : List (Fin N)}
    (h : ∀ x, x ∈ L₁ → x ∈ L₂) :
    filterMass E G ν L₂ ≤ filterMass E G ν L₁ := by
  unfold filterMass
  apply Finset.sum_le_sum
  intro y _
  by_cases hp₂ : passesAnchors E G L₂ y
  · have hp₁ : passesAnchors E G L₁ y := by
      intro x hx
      exact hp₂ x (h x hx)
    simp [hp₁, hp₂]
  · by_cases hp₁ : passesAnchors E G L₁ y
    · simp [hp₁, hp₂, ν.nonneg y]
    · simp [hp₁, hp₂]

theorem filterMass_congr_mem {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) {L₁ L₂ : List (Fin N)}
    (h : ∀ x, x ∈ L₁ ↔ x ∈ L₂) :
    filterMass E G ν L₁ = filterMass E G ν L₂ := by
  apply le_antisymm
  · exact filterMass_le_of_mem E G ν (L₁ := L₂) (L₂ := L₁)
      (fun x hx => (h x).mpr hx)
  · exact filterMass_le_of_mem E G ν (L₁ := L₁) (L₂ := L₂)
      (fun x hx => (h x).mp hx)

theorem mem_append_erase_of_mem_suffix {α : Type*} [BEq α] [LawfulBEq α]
    {L₁ L₂ : List α} {a x : α} (ha : a ∈ L₂) (hx : x ∈ L₁) :
    x ∈ (L₁ ++ L₂).erase a := by
  by_cases hxa : x = a
  · subst x
    rw [List.erase_append_left _ hx]
    exact List.mem_append.mpr (Or.inr ha)
  · apply (List.mem_erase_of_ne hxa).2
    exact List.mem_append.mpr (Or.inl hx)

theorem crossOrder_perm {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (g h₀ : Γ.Key) (hh₀ : h₀ ∈ Γ.crossKeys g) :
    List.Perm (Γ.crossOrder g h₀) (Γ.crossKeys g) := by
  rw [GridGeom.crossOrder]
  exact (List.perm_append_singleton h₀ (Γ.crossKeys g |>.erase h₀)).trans
    (List.perm_cons_erase hh₀).symm

theorem mem_map_erase {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {L : List α} (hL : L.Nodup) {a : α} (ha : a ∈ L) (f : α → β) (x : β) :
    x ∈ (L.map f).erase (f a) ↔ x ∈ (L.erase a).map f := by
  induction L generalizing a with
  | nil => simp at ha
  | cons b bs ih =>
      rcases List.nodup_cons.mp hL with ⟨hb, hbs⟩
      by_cases hba : b = a
      · subst b
        simp [List.map_cons]
      · have ha' : a ∈ bs := by simpa [eq_comm, hba] using ha
        have hcons : (b :: bs).erase a = b :: bs.erase a := by
          exact List.erase_cons_tail (by simpa [hba])
        by_cases hfb : f b = f a
        · have hfaMem : f a ∈ bs.map f := List.mem_map.mpr ⟨a, ha', rfl⟩
          have hlhs : x ∈ ((f b) :: bs.map f).erase (f a) ↔ x ∈ bs.map f := by
            simp [hfb]
          have hrhs : x ∈ ((b :: bs).erase a).map f ↔
              x = f a ∨ x ∈ (bs.erase a).map f := by
            simp [hcons, hfb]
          rw [List.map_cons, hlhs, hrhs]
          constructor
          · intro hx
            by_cases hxa : x = f a
            · exact Or.inl hxa
            · right
              have hxErase : x ∈ (bs.map f).erase (f a) :=
                (List.mem_erase_of_ne hxa).2 hx
              exact (ih hbs ha').mp hxErase
          · intro hx
            rcases hx with hxa | hxTail
            · subst x
              exact hfaMem
            · have hxErase := (ih hbs ha').mpr hxTail
              exact List.mem_of_mem_erase hxErase
        · have hskip : ((f b) :: bs.map f).erase (f a) =
              f b :: (bs.map f).erase (f a) := by
            exact List.erase_cons_tail (by simpa [hfb])
          have hlhs : x ∈ ((f b) :: bs.map f).erase (f a) ↔
              x = f b ∨ x ∈ (bs.map f).erase (f a) := by simp [hskip]
          have hrhs : x ∈ ((b :: bs).erase a).map f ↔
              x = f b ∨ x ∈ (bs.erase a).map f := by simp [hcons]
          rw [List.map_cons, hlhs, hrhs]
          constructor
          · intro hx
            rcases hx with hxb | hxTail
            · exact Or.inl hxb
            · exact Or.inr ((ih hbs ha').mp hxTail)
          · intro hx
            rcases hx with hxb | hxTail
            · exact Or.inl hxb
            · exact Or.inr ((ih hbs ha').mpr hxTail)

theorem crossValidRow_retention {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (i : M.ι) (a : Γ.Key → Fin N) (g : Γ.Key) (hn : 1 ≤ n) (hd : 0 ≤ d)
    (hloc : GeomLocal Γ) (hcross : CrossValidRow Γ M i a g) :
    (n : ℝ) ^ (-(2 * (d / 80) * (s : ℝ))) ≤
      filterMass E G (M.ν i) ((Γ.crossKeys g).map a) := by
  classical
  let r : ℝ := (n : ℝ) ^ (-(d / 80))
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := le_trans (by norm_num) hnreal
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos hnpos _
  have hrle : r ≤ 1 := by
    dsimp [r]
    exact Real.rpow_le_one_of_one_le_of_nonpos hnreal (by linarith)
  have hlen : (Γ.crossKeys g).length ≤ 2 * s := by
    simpa [GridGeom.crossKeys] using hloc.keyNbrs_card g
  by_cases hnil : Γ.crossKeys g = []
  · rw [hnil]
    simp only [List.map_nil]
    have hd80 : 0 ≤ d / 80 := div_nonneg hd (by norm_num)
    have hds : 0 ≤ (d / 80) * (s : ℝ) := mul_nonneg hd80 (Nat.cast_nonneg s)
    have hexp : -(2 * (d / 80) * (s : ℝ)) ≤ 0 := by nlinarith
    calc
      (n : ℝ) ^ (-(2 * (d / 80) * (s : ℝ))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hnreal hexp
      _ = filterMass E G (M.ν i) [] := by
        simp [filterMass, passesAnchors, (M.ν i).sum_eq_one]
  · obtain ⟨h₀, hh₀⟩ := List.exists_mem_of_ne_nil (Γ.crossKeys g) hnil
    let order := Γ.crossOrder g h₀
    have hmemOrder : ∀ h, h ∈ order ↔ h ∈ Γ.crossKeys g := by
      intro h
      change h ∈ ((Γ.crossKeys g).erase h₀ ++ [h₀]) ↔ h ∈ Γ.crossKeys g
      rw [List.mem_append, List.mem_singleton]
      constructor
      · rintro (hh | hh)
        · exact List.mem_of_mem_erase hh
        · subst h
          exact hh₀
      · intro hh
        by_cases heq : h = h₀
        · exact Or.inr heq
        · exact Or.inl ((List.mem_erase_of_ne heq).2 hh)
    have hlenOrder : order.length = (Γ.crossKeys g).length := by
      dsimp [order, GridGeom.crossOrder]
      simp only [List.length_append, List.length_singleton]
      exact List.length_erase_add_one hh₀
    have hprefix : ∀ k ≤ order.length,
        r ^ k ≤ filterMass E G (M.ν i) ((order.map a).take k) := by
      intro k hk
      induction k with
      | zero =>
          simp [filterMass, passesAnchors, (M.ν i).sum_eq_one]
      | succ k ih =>
          have hprev := ih (by omega)
          have hklt : k < order.length := by omega
          have hstep := hcross h₀ hh₀ k (by simpa [hlenOrder] using hklt)
          calc
            r ^ (k + 1) = r * (r ^ k) := by rw [pow_succ]; ring
            _ ≤ r * filterMass E G (M.ν i) ((order.map a).take k) :=
              mul_le_mul_of_nonneg_left hprev hrpos.le
            _ ≤ filterMass E G (M.ν i) ((order.map a).take (k + 1)) := hstep
    have hfull : r ^ order.length ≤ filterMass E G (M.ν i) (order.map a) := by
      have ht : (order.map a).take order.length = order.map a := by
        rw [show order.length = (order.map a).length by simp]
        exact List.take_length
      simpa [ht] using hprefix order.length le_rfl
    have hlabels : ∀ x, x ∈ order.map a ↔ x ∈ (Γ.crossKeys g).map a := by
      intro x
      simp only [List.mem_map]
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, (hmemOrder h).mp hh, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, (hmemOrder h).mpr hh, rfl⟩
    have hmass := filterMass_congr_mem E G (M.ν i) hlabels
    have hpow : r ^ (2 * s) = (n : ℝ) ^ (-(2 * (d / 80) * (s : ℝ))) := by
      dsimp [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnnonneg]
      congr 1
      push_cast
      ring
    have hlenOrderBound : order.length ≤ 2 * s := by omega
    have hpowBound : r ^ (2 * s) ≤ r ^ order.length := by
      have hgap : order.length + (2 * s - order.length) = 2 * s := by omega
      rw [← hgap, pow_add]
      calc
        r ^ order.length * r ^ (2 * s - order.length) ≤
            r ^ order.length * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hrpos.le hrle)
            (pow_nonneg hrpos.le order.length)
        _ = r ^ order.length := by simp
    calc
      (n : ℝ) ^ (-(2 * (d / 80) * (s : ℝ))) = r ^ (2 * s) := hpow.symm
      _ ≤ r ^ order.length := hpowBound
      _ ≤ filterMass E G (M.ν i) (order.map a) := hfull
      _ = filterMass E G (M.ν i) ((Γ.crossKeys g).map a) := hmass

end HypercubeRamsey.S07
