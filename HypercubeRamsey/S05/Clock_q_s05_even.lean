import HypercubeRamsey.S05.Centres
import HypercubeRamsey.Tools.CubeGeometry

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey

private theorem bool_eq_of_ne {a b c : Bool} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Every vertex of an `n`-cube has at most `n` neighbors. -/
theorem cube_adj_neighbors_card_le (n : ℕ) (x : CubeVertex n) :
    (Finset.univ.filter fun y : CubeVertex n => (cube n).Adj x y).card ≤ n := by
  classical
  cases n with
  | zero =>
      have hEmpty : Finset.univ.filter (fun y : CubeVertex 0 => (cube 0).Adj x y) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro y _
        have hyx : y = x := Subsingleton.elim _ _
        subst y
        exact (cube 0).loopless.irrefl x
      rw [hEmpty]
      simp
  | succ n =>
    let fallback : Fin (n + 1) := ⟨0, by omega⟩
    let S : Finset (CubeVertex (n + 1)) := Finset.univ.filter fun y => (cube (n + 1)).Adj x y
    let coord (y : {y : CubeVertex (n + 1) // (cube (n + 1)).Adj x y}) : Fin (n + 1) :=
      Classical.choose (Finset.card_eq_one.mp (show
        (Finset.univ.filter fun i : Fin (n + 1) => x i ≠ y.1 i).card = 1 from y.2))
    have coord_mem (y : {y : CubeVertex (n + 1) // (cube (n + 1)).Adj x y}) :
        x (coord y) ≠ y.1 (coord y) := by
      have hs := Classical.choose_spec
        (Finset.card_eq_one.mp (show
          (Finset.univ.filter fun i : Fin (n + 1) => x i ≠ y.1 i).card = 1 from y.2))
      have hm : coord y ∈ Finset.univ.filter fun i : Fin (n + 1) => x i ≠ y.1 i := by
        rw [hs]
        simp [coord]
      exact (Finset.mem_filter.mp hm).2
    have coord_other (y : {y : CubeVertex (n + 1) // (cube (n + 1)).Adj x y})
        (i : Fin (n + 1)) (hi : i ≠ coord y) : y.1 i = x i := by
      have hs := Classical.choose_spec
        (Finset.card_eq_one.mp (show
          (Finset.univ.filter fun j : Fin (n + 1) => x j ≠ y.1 j).card = 1 from y.2))
      have hnot : i ∉ Finset.univ.filter fun j : Fin (n + 1) => x j ≠ y.1 j := by
        rw [hs]
        simpa [coord] using hi
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [ne_comm] using hne⟩)
    let f (y : CubeVertex (n + 1)) : Fin (n + 1) :=
      if hy : (cube (n + 1)).Adj x y then coord ⟨y, hy⟩ else fallback
    have hcoord_sub : ∀ {y z : {y : CubeVertex (n + 1) // (cube (n + 1)).Adj x y}},
        coord y = coord z → y = z := by
      intro y z hyz
      apply Subtype.ext
      funext i
      by_cases hi : i = coord y
      · subst i
        have hz := coord_mem z
        have hz' : x (coord y) ≠ z.1 (coord y) := by simpa [hyz] using hz
        exact bool_eq_of_ne (coord_mem y) hz'
      · rw [coord_other y i hi, coord_other z i (by rw [← hyz]; exact hi)]
    have hcoord : Set.InjOn f S := by
      intro y hy z hz hyz
      have hyAdj := (Finset.mem_filter.mp hy).2
      have hzAdj := (Finset.mem_filter.mp hz).2
      have hcoords : coord ⟨y, hyAdj⟩ = coord ⟨z, hzAdj⟩ := by
        simpa [f, hyAdj, hzAdj] using hyz
      have hySub : (⟨y, hyAdj⟩ : {y : CubeVertex (n + 1) // (cube (n + 1)).Adj x y}) = ⟨z, hzAdj⟩ :=
        hcoord_sub hcoords
      exact congrArg Subtype.val hySub
    have himage : S.card = (S.image f).card := (Finset.card_image_of_injOn hcoord).symm
    have hsub : S.image f ⊆ Finset.univ := Finset.subset_univ _
    have hcard : (S.image f).card ≤ n + 1 := by
      calc
        (S.image f).card ≤ Finset.univ.card := Finset.card_le_card hsub
        _ = n + 1 := by simp
    rw [himage]
    exact hcard

/-- Odd roles adjacent to a fixed even role. -/
noncomputable def oddAdjSet5 {n : ℕ} (v : EvenRole5 n) : Finset (OddRole5 n) :=
  Finset.univ.filter fun b => (cube n).Adj v.1 b.1

/-- Even roles whose odd-neighbor scope contains a fixed odd role. -/
noncomputable def oddAdjIncidence5 {n : ℕ} (b : OddRole5 n) : Finset (EvenRole5 n) :=
  Finset.univ.filter fun v => b ∈ oddAdjSet5 v

theorem oddAdjSet5_card_le {n : ℕ} (v : EvenRole5 n) : (oddAdjSet5 v).card ≤ n := by
  classical
  let S := oddAdjSet5 v
  have himage : S.card = (S.image Subtype.val).card :=
    (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hsub : S.image Subtype.val ⊆
      Finset.univ.filter (fun y : CubeVertex n => (cube n).Adj v.1 y) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  calc
    S.card = (S.image Subtype.val).card := himage
    _ ≤ (Finset.univ.filter (fun y : CubeVertex n => (cube n).Adj v.1 y)).card :=
      Finset.card_le_card hsub
    _ ≤ n := cube_adj_neighbors_card_le n v.1

theorem oddAdjIncidence5_card_le {n : ℕ} (b : OddRole5 n) :
    (oddAdjIncidence5 b).card ≤ n := by
  classical
  let S := oddAdjIncidence5 b
  have himage : S.card = (S.image Subtype.val).card :=
    (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hsub : S.image Subtype.val ⊆
      Finset.univ.filter (fun y : CubeVertex n => (cube n).Adj b.1 y) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
    have hmem := (Finset.mem_filter.mp hv).2
    change b ∈ Finset.univ.filter (fun y : OddRole5 n => (cube n).Adj v.1 y.1) at hmem
    have hadj := (Finset.mem_filter.mp hmem).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.symm⟩
  calc
    S.card = (S.image Subtype.val).card := himage
    _ ≤ (Finset.univ.filter (fun y : CubeVertex n => (cube n).Adj b.1 y)).card :=
      Finset.card_le_card hsub
    _ ≤ n := cube_adj_neighbors_card_le n b.1

theorem evenRole5_nonempty {n : ℕ} (hn : 0 < n) : Nonempty (EvenRole5 n) := by
  let x : CubeVertex n := fun _ => false
  have hx : IsEvenRole x := by simp [IsEvenRole, x]
  exact ⟨⟨x, hx⟩⟩

theorem oddAdjSet5_nonempty {n : ℕ} (v : EvenRole5 n) (hn : 0 < n) :
    (oddAdjSet5 v).Nonempty := by
  classical
  let i : Fin n := ⟨0, hn⟩
  let y := cubeFlip v.1 i
  have hadj : (cube n).Adj v.1 y := by
    simpa [y] using cubeFlip_adj v.1 i
  have hodd : ¬ IsEvenRole y := by
    intro he
    exact ((cubeFlip_parity v.1 i).mp he) v.2
  refine ⟨⟨y, hodd⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩

theorem oddRole5_nonempty {n : ℕ} (hn : 0 < n) : Nonempty (OddRole5 n) := by
  obtain ⟨v⟩ := evenRole5_nonempty hn
  obtain ⟨b, _⟩ := oddAdjSet5_nonempty v hn
  exact ⟨b⟩

namespace FinProb

theorem pr_le_one5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) : P.pr A ≤ 1 := by
  classical
  unfold pr
  calc
    (∑ ω, if A ω then P.w ω else 0) ≤ ∑ ω, P.w ω := by
      apply Finset.sum_le_sum
      intro ω _
      split_ifs with hA
      · rfl
      · exact P.nonneg ω
    _ = 1 := P.sum_eq_one

end FinProb

/-- Bounded-sum failure estimate used to feed the Section 3 clock sampler. -/
theorem product_bad_cost_prob5 {n : ℕ} {O : Type} [Fintype O]
    (hn : 2 ≤ n) (row : OddRole5 n → FinProb O)
    (cost : EvenRole5 n → OddRole5 n → O → ℝ) (M t₀ t₁ P : ℝ)
    (hM : 0 ≤ M)
    (hcost : ∀ v b o, 0 ≤ cost v b o ∧ cost v b o ≤ M)
    (hoff : ∀ v b o, ¬ (cube n).Adj v.1 b.1 → cost v b o = 0)
    (hmean : ∀ v, ∑ b, (row b).expect (cost v b) ≤ t₀)
    (hgap : t₀ ≤ t₁)
    (hexp : Real.exp (-(2 * (t₁ - t₀) ^ 2 / ((n : ℝ) * M ^ 2))) ≤
      (n : ℝ) ^ (-(P + 1))) :
    ∀ v, (FinProb.pi row).pr (fun ω => t₁ < ∑ b, cost v b (ω b)) ≤ (n : ℝ) ^ (-P) := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnR2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (-P) = (n : ℝ) ^ (-(P + 1)) * n := by
    calc
      (n : ℝ) ^ (-P) = (n : ℝ) ^ (-(P + 1) + 1) := by congr 1 <;> ring
      _ = (n : ℝ) ^ (-(P + 1)) * n := by
        rw [Real.rpow_add_one (ne_of_gt hnR)]
  let bad (v : EvenRole5 n) (ω : OddRole5 n → O) : Prop :=
    t₁ < ∑ b, cost v b (ω b)
  intro v
  by_cases hM0 : M = 0
  · have hz : ∀ b o, cost v b o = 0 := by
      intro b o
      exact le_antisymm (by simpa [hM0] using (hcost v b o).2) (hcost v b o).1
    have hsum : (∑ b, (row b).expect (cost v b)) = 0 := by
      simp [FinProb.expect, hz]
    have ht₀ : 0 ≤ t₀ := by rw [← hsum]; exact hmean v
    have ht₁ : 0 ≤ t₁ := ht₀.trans hgap
    have hpr : (FinProb.pi row).pr (bad v) = 0 := by
      simp [FinProb.pr, bad, hz, ht₁]
    rw [hpr]
    positivity
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    by_cases hgap0 : t₁ - t₀ = 0
    · have hexp0 : 1 ≤ (n : ℝ) ^ (-(P + 1)) := by
        simpa [hgap0] using hexp
      have hpowlower : 1 ≤ (n : ℝ) ^ (-P) := by
        calc
          1 ≤ (n : ℝ) := by linarith
          _ ≤ (n : ℝ) ^ (-(P + 1)) * n := by
            simpa using mul_le_mul_of_nonneg_right hexp0 hnR.le
          _ = (n : ℝ) ^ (-P) := hpow.symm
      exact (FinProb.pr_le_one5 (FinProb.pi row) (bad v)).trans hpowlower
    · have hgapPos : 0 < t₁ - t₀ := by
        rcases eq_or_lt_of_le (sub_nonneg.mpr hgap) with h | h
        · exact (hgap0 h.symm).elim
        · exact h
      let S := oddAdjSet5 v
      let upper (b : OddRole5 n) : ℝ :=
        if (cube n).Adj v.1 b.1 then M else 0
      have hX : ∀ b o, 0 ≤ cost v b o ∧ cost v b o ≤ upper b := by
        intro b o
        by_cases hadj : (cube n).Adj v.1 b.1
        · simpa [upper, hadj] using hcost v b o
        · have hz := hoff v b o hadj
          simp [upper, hadj, hz]
      have hwidth_eq : (∑ b : OddRole5 n, (upper b - 0) ^ 2) =
          (S.card : ℝ) * M ^ 2 := by
        calc
          (∑ b : OddRole5 n, (upper b - 0) ^ 2) =
              ∑ b : OddRole5 n, (if (cube n).Adj v.1 b.1 then (1 : ℝ) else 0) * M ^ 2 := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases hadj : (cube n).Adj v.1 b.1 <;> simp [upper, hadj]
          _ = (∑ b : OddRole5 n, if (cube n).Adj v.1 b.1 then (1 : ℝ) else 0) * M ^ 2 :=
            (Finset.sum_mul _ _ _).symm
          _ = (S.card : ℝ) * M ^ 2 := by
            rw [Finset.sum_boole]
            rfl
      have hScard : (S.card : ℝ) ≤ n := by
        dsimp [S]
        exact_mod_cast oddAdjSet5_card_le v
      have hSpos : 0 < (S.card : ℝ) := by
        have hp := Finset.card_pos.mpr (oddAdjSet5_nonempty v (by omega))
        exact_mod_cast hp
      have hwidthpos : 0 < ∑ b : OddRole5 n, (upper b - 0) ^ 2 := by
        rw [hwidth_eq]
        positivity
      have hwidthle : (∑ b : OddRole5 n, (upper b - 0) ^ 2) ≤ (n : ℝ) * M ^ 2 := by
        rw [hwidth_eq]
        exact mul_le_mul_of_nonneg_right hScard (sq_nonneg M)
      have hdenpos : 0 < (n : ℝ) * M ^ 2 := by positivity
      have hrecip : ((n : ℝ) * M ^ 2)⁻¹ ≤
          (∑ b : OddRole5 n, (upper b - 0) ^ 2)⁻¹ := inv_anti₀ hwidthpos hwidthle
      have hdiv : 2 * (t₁ - t₀) ^ 2 / ((n : ℝ) * M ^ 2) ≤
          2 * (t₁ - t₀) ^ 2 / (∑ b : OddRole5 n, (upper b - 0) ^ 2) := by
        have hm := mul_le_mul_of_nonneg_left hrecip (by positivity : 0 ≤ 2 * (t₁ - t₀) ^ 2)
        simpa [div_eq_mul_inv] using hm
      have hexpcomp : Real.exp (-2 * (t₁ - t₀) ^ 2 /
          (∑ b : OddRole5 n, (upper b - 0) ^ 2)) ≤
          Real.exp (-(2 * (t₁ - t₀) ^ 2 / ((n : ℝ) * M ^ 2))) := by
        apply Real.exp_le_exp.mpr
        convert neg_le_neg hdiv using 1 <;> ring
      have htail := xChernoff row (fun b o => cost v b o) (fun _ => 0) upper hX
        hwidthpos (t₁ - t₀) hgapPos
      have hsubset : ∀ ω : OddRole5 n → O,
          bad v ω → t₁ - t₀ ≤
            |(∑ b, cost v b (ω b)) - ∑ b, (row b).expect (cost v b)| := by
        intro ω hbad
        have hmeanω := hmean v
        have hcenter : t₁ - t₀ ≤ (∑ b, cost v b (ω b)) - ∑ b, (row b).expect (cost v b) := by
          dsimp [bad] at hbad
          linarith
        exact hcenter.trans (le_abs_self _)
      have hprtail : (FinProb.pi row).pr (bad v) ≤
          2 * Real.exp (-2 * (t₁ - t₀) ^ 2 /
            (∑ b : OddRole5 n, (upper b - 0) ^ 2)) := by
        exact (FinProb.pr_mono _ _ _ hsubset).trans htail
      calc
        (FinProb.pi row).pr (bad v) ≤
            2 * Real.exp (-2 * (t₁ - t₀) ^ 2 /
              (∑ b : OddRole5 n, (upper b - 0) ^ 2)) := hprtail
        _ ≤ 2 * Real.exp (-(2 * (t₁ - t₀) ^ 2 / ((n : ℝ) * M ^ 2))) :=
          mul_le_mul_of_nonneg_left hexpcomp (by norm_num)
        _ ≤ 2 * (n : ℝ) ^ (-(P + 1)) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)
        _ ≤ (n : ℝ) ^ (-P) := by
          rw [hpow]
          have hfac : 2 * (n : ℝ) ^ (-(P + 1)) ≤ n * (n : ℝ) ^ (-(P + 1)) := by
            exact mul_le_mul_of_nonneg_right hnR2 (Real.rpow_nonneg hnR.le _)
          nlinarith [hfac]

end HypercubeRamsey
