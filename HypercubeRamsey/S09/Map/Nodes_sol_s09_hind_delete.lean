import HypercubeRamsey.S09.Map.Device

namespace HypercubeRamsey.Lane_sol_s09_hind

open HypercubeRamsey OAI.HypercubeRamsey Classical

private theorem filter_count_loss {α : Type*} [DecidableEq α]
    (C B : Finset α) (test active : α → Prop) [DecidablePred test] [DecidablePred active]
    (htest : ∀ x, test x → active x) :
    (C.filter test).card ≤ (B.filter test).card + ((C \ B).filter active).card := by
  classical
  have hsub : C.filter test ⊆ B.filter test ∪ (C \ B).filter active := by
    intro x hx
    obtain ⟨hxC, hxTest⟩ := Finset.mem_filter.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxB, hxTest⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxC, hxB⟩, htest x hxTest⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

variable {P : Params9} {hc : HeightChoice9 P} {n : ℕ}

theorem eligible_count_loss (C B : Finset (Pos9 P hc n))
    (Pp : Pos9 P hc n → Bool) (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    eligCount9 C Pp v j ≤ eligCount9 B Pp v j +
      ((C \ B).filter (fun x => Pp x = true)).card := by
  classical
  simpa only [eligCount9, Finset.filter_congr_decidable] using filter_count_loss C B
    (fun c => Pp c = true ∧ c.slice = specialWord9 (P.m n) v ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n ∧ c.level = j)
    (fun c => Pp c = true) (fun _ h => h.1)

theorem same_crowd_loss (C B : Finset (Pos9 P hc n))
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n)
    (j : Fin (hc.levels n + 1)) (R : ℕ) :
    crowdSame9 C Pp A v j R ≤ crowdSame9 B Pp A v j R +
      ((C \ B).filter (activeAt9 Pp A)).card := by
  classical
  simpa only [crowdSame9, Finset.filter_congr_decidable] using filter_count_loss C B
    (fun c => activeAt9 Pp A c ∧ c.slice = specialWord9 (P.m n) v ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ R ∧ c.level = j)
    (activeAt9 Pp A) (fun _ h => h.1)

theorem adjacent_crowd_loss (C B : Finset (Pos9 P hc n))
    (Pp A : Pos9 P hc n → Bool) (v : CubeVertex n) (j : Fin (hc.levels n + 1)) :
    crowdAdj9 C Pp A v j ≤ crowdAdj9 B Pp A v j +
      ((C \ B).filter (activeAt9 Pp A)).card := by
  classical
  simpa only [crowdAdj9, Finset.filter_congr_decidable] using filter_count_loss C B
    (fun c => activeAt9 Pp A c ∧ _root_.hammingDist c.slice (specialWord9 (P.m n) v) = 1 ∧
      _root_.hammingDist c.location (residualWord9 (P.m n) v) ≤ P.radius n - 1 ∧ c.level = j)
    (activeAt9 Pp A) (fun _ h => h.1)

theorem bad_and_count_transfer (C B : Finset (Pos9 P hc n)) (hBC : B ⊆ C)
    (Pp A : Pos9 P hc n → Bool) (t t' s s' : ℝ)
    (ht : t' ≤ t)
    (hthreshold : (n : ℝ) ^ ((P.χ : ℝ) / 2) ≤
      (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps'))
    (hposLoss : (((C \ B).filter (fun x => Pp x = true)).card : ℝ) ≤
      (s - s') * (n : ℝ) ^ (10 : ℝ))
    (hactLoss : (((C \ B).filter (activeAt9 Pp A)).card : ℝ) ≤
      (t - t') * (n : ℝ) ^ ((P.χ : ℝ) / 2))
    (v : CubeVertex n) (j : Fin (hc.levels n + 1))
    (hbad : badIn9 C t Pp A v j)
    (hcount : s * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 C Pp v j : ℝ)) :
    badIn9 B t' Pp A v j ∧
      s' * (n : ℝ) ^ (10 : ℝ) ≤ (eligCount9 B Pp v j : ℝ) := by
  classical
  have hcountLoss := eligible_count_loss C B Pp v j
  have hcountLossR : (eligCount9 C Pp v j : ℝ) ≤ (eligCount9 B Pp v j : ℝ) +
      (((C \ B).filter (fun x => Pp x = true)).card : ℝ) := by exact_mod_cast hcountLoss
  refine ⟨?_, by nlinarith⟩
  rcases hbad with hhole | ⟨j', hj', hcrowd⟩
  · exact Or.inl (fun x hx hs hd hl => hhole x (hBC hx) hs hd hl)
  · refine Or.inr ⟨j', hj', ?_⟩
    rcases hcrowd with hsame | hadj | hplus
    · have hloss := same_crowd_loss C B Pp A v j' (P.radius n)
      have hlossR : (crowdSame9 C Pp A v j' (P.radius n) : ℝ) ≤
          (crowdSame9 B Pp A v j' (P.radius n) : ℝ) +
            (((C \ B).filter (activeAt9 Pp A)).card : ℝ) := by exact_mod_cast hloss
      exact Or.inl (by nlinarith)
    · have hloss := adjacent_crowd_loss C B Pp A v j'
      have hlossR : (crowdAdj9 C Pp A v j' : ℝ) ≤
          (crowdAdj9 B Pp A v j' : ℝ) +
            (((C \ B).filter (activeAt9 Pp A)).card : ℝ) := by exact_mod_cast hloss
      exact Or.inr (Or.inl (by nlinarith))
    · have hactLossPlus : (((C \ B).filter (activeAt9 Pp A)).card : ℝ) ≤
          (t - t') * (n : ℝ) ^ (1 - (P.σ : ℝ) + hc.eps') :=
        hactLoss.trans (mul_le_mul_of_nonneg_left hthreshold (sub_nonneg.mpr ht))
      have hloss := same_crowd_loss C B Pp A v j' (P.radius n + 1)
      have hlossR : (crowdSame9 C Pp A v j' (P.radius n + 1) : ℝ) ≤
          (crowdSame9 B Pp A v j' (P.radius n + 1) : ℝ) +
            (((C \ B).filter (activeAt9 Pp A)).card : ℝ) := by exact_mod_cast hloss
      exact Or.inr (Or.inr (by nlinarith))

/-- Private center domains are pairwise disjoint after deleting every other support. -/
noncomputable def privateDomain (C : Finset (Pos9 P hc n)) {q : ℕ}
    (S : Fin q → Finset (Pos9 P hc n)) (i : Fin q) : Finset (Pos9 P hc n) :=
  (C ∩ S i) \ ((Finset.univ.erase i).biUnion S)

theorem privateDomain_subset (C : Finset (Pos9 P hc n)) {q : ℕ}
    (S : Fin q → Finset (Pos9 P hc n)) (i : Fin q) :
    privateDomain C S i ⊆ C ∩ S i := Finset.sdiff_subset

theorem privateDomain_disjoint (C : Finset (Pos9 P hc n)) {q : ℕ}
    (S : Fin q → Finset (Pos9 P hc n)) (i j : Fin q) (hij : i ≠ j) :
    Disjoint (privateDomain C S i) (privateDomain C S j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hxi' := Finset.mem_sdiff.mp hxi
  have hxj' := Finset.mem_sdiff.mp hxj
  have hxSj : x ∈ S j := (Finset.mem_inter.mp hxj'.1).2
  exact hxi'.2 (Finset.mem_biUnion.mpr
    ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩, hxSj⟩)

theorem privateDomain_loss_subset (C : Finset (Pos9 P hc n)) {q : ℕ}
    (S : Fin q → Finset (Pos9 P hc n)) (i : Fin q) :
    ((C ∩ S i) \ privateDomain C S i) ⊆
      (Finset.univ.erase i).biUnion (fun j => S i ∩ S j) := by
  classical
  intro x hx
  obtain ⟨hxC, hxnot⟩ := Finset.mem_sdiff.mp hx
  have hxSi : x ∈ S i := (Finset.mem_inter.mp hxC).2
  have hxUnion : x ∈ (Finset.univ.erase i).biUnion S := by
    by_contra h
    exact hxnot (Finset.mem_sdiff.mpr ⟨hxC, h⟩)
  obtain ⟨j, hj, hxSj⟩ := Finset.mem_biUnion.mp hxUnion
  exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_inter.mpr ⟨hxSi, hxSj⟩⟩

private theorem filtered_union_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (S : α → Finset β) (test : β → Prop) [DecidablePred test] :
    ((I.biUnion S).filter test).card ≤ ∑ i ∈ I, ((S i).filter test).card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert, Finset.filter_union, Finset.sum_insert ha]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem privateDomain_count_loss (C : Finset (Pos9 P hc n)) {q : ℕ}
    (hq : 0 < q) (S : Fin q → Finset (Pos9 P hc n)) (i : Fin q)
    (test : Pos9 P hc n → Prop) [DecidablePred test] (δ : ℝ) (hδ : 0 ≤ δ)
    (hpair : ∀ j : Fin q, i ≠ j → (((S i ∩ S j).filter test).card : ℝ) ≤ δ / q) :
    ((((C ∩ S i) \ privateDomain C S i).filter test).card : ℝ) ≤ δ := by
  classical
  let I : Finset (Fin q) := Finset.univ.erase i
  have hsub : ((C ∩ S i) \ privateDomain C S i).filter test ⊆
      (I.biUnion (fun j => S i ∩ S j)).filter test :=
    Finset.filter_subset_filter _ (privateDomain_loss_subset C S i)
  have hcount := (Finset.card_le_card hsub).trans
    (filtered_union_card_le I (fun j => S i ∩ S j) test)
  have hcountR : ((((C ∩ S i) \ privateDomain C S i).filter test).card : ℝ) ≤
      ∑ j ∈ I, (((S i ∩ S j).filter test).card : ℝ) := by exact_mod_cast hcount
  have hsum : (∑ j ∈ I, (((S i ∩ S j).filter test).card : ℝ)) ≤
      (I.card : ℝ) * (δ / q) := by
    calc
      _ ≤ ∑ _j ∈ I, δ / q := by
        apply Finset.sum_le_sum
        intro j hj
        exact hpair j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = _ := by simp
  have hcard : I.card ≤ q := by
    exact (Finset.card_le_card (Finset.erase_subset i Finset.univ)).trans (by simp)
  have hcardR : (I.card : ℝ) ≤ (q : ℝ) := by exact_mod_cast hcard
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  calc
    _ ≤ (I.card : ℝ) * (δ / q) := hcountR.trans hsum
    _ ≤ (q : ℝ) * (δ / q) := mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = δ := by field_simp

end HypercubeRamsey.Lane_sol_s09_hind
