import Mathlib

universe u

namespace HypercubeRamsey

theorem xRamseyBinom_p_tools_binom {V : Type u} [Fintype V] (G : SimpleGraph V) (s t : ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hcard : Nat.choose (s + t - 2) (s - 1) ≤ Fintype.card V) :
    (∃ C : Finset V, C.card = s ∧
      ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v) ∨
    (∃ I : Finset V, I.card = t ∧
      ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) := by
  classical
  have hmain : ∀ n s t, s + t = n → ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
      (hs : 1 ≤ s) (ht : 1 ≤ t)
      (hcard : Nat.choose (s + t - 2) (s - 1) ≤ Fintype.card V),
      (∃ C : Finset V, C.card = s ∧ ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v) ∨
      (∃ I : Finset V, I.card = t ∧ ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s t hst V _ G hs ht hcard
      have hchoosePos : 0 < Nat.choose (s + t - 2) (s - 1) :=
        Nat.choose_pos (by omega)
      have hVPos : 0 < Fintype.card V := lt_of_lt_of_le hchoosePos hcard
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hVPos
      by_cases hs1 : s = 1
      · subst s
        left
        refine ⟨{v}, by simp, ?_⟩
        intro u hu w hw huw
        simp only [Finset.mem_singleton] at hu hw
        subst u
        subst w
        exact (huw rfl).elim
      · by_cases ht1 : t = 1
        · subst t
          right
          refine ⟨{v}, by simp, ?_⟩
          intro u hu w hw huw
          simp only [Finset.mem_singleton] at hu hw
          subst u
          subst w
          exact (huw rfl).elim
        · have hs2 : 2 ≤ s := by omega
          have ht2 : 2 ≤ t := by omega
          let Nbr : Finset V := G.neighborFinset v
          let Other : Finset V := Finset.univ.erase v \ Nbr
          have hvnotNbr : v ∉ Nbr := by
            simp [Nbr, SimpleGraph.mem_neighborFinset, G.loopless]
          have hNbrSub : Nbr ⊆ Finset.univ.erase v := by
            intro x hx
            simp only [Finset.mem_erase, Finset.mem_univ]
            constructor
            · intro hxv
              subst x
              have : G.Adj v v := by simpa [Nbr] using hx
              exact G.loopless.irrefl v this
            · trivial
          have hOtherCard : Other.card = Fintype.card V - 1 - Nbr.card := by
            dsimp [Other]
            rw [Finset.card_sdiff_of_subset hNbrSub]
            simp
          have hdecomp : Nbr.card + Other.card + 1 = Fintype.card V := by
            rw [hOtherCard]
            have hNbrLe : Nbr.card ≤ Fintype.card V - 1 := by
              have := Finset.card_le_card hNbrSub
              simpa using this
            omega
          have hPascal : Nat.choose (s + t - 2) (s - 1) =
              Nat.choose (s + t - 3) (s - 2) + Nat.choose (s + t - 3) (s - 1) := by
            rw [show s + t - 2 = (s + t - 3) + 1 by omega,
              show s - 1 = (s - 2) + 1 by omega, Nat.choose_succ_succ']
          let Vnbr := {x : V // x ∈ Nbr}
          let Vother := {x : V // x ∈ Other}
          letI : Fintype Vnbr := Fintype.ofFinite Vnbr
          letI : Fintype Vother := Fintype.ofFinite Vother
          have hcardNbr : Fintype.card Vnbr = Nbr.card := by
            change Fintype.card {x : V // x ∈ Nbr} = Nbr.card
            simp
          have hcardOther : Fintype.card Vother = Other.card := by
            change Fintype.card {x : V // x ∈ Other} = Other.card
            simp
          let Gn : SimpleGraph Vnbr := G.induce {x | x ∈ Nbr}
          let Go : SimpleGraph Vother := G.induce {x | x ∈ Other}
          let embN : Vnbr ↪ V := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
          let embO : Vother ↪ V := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
          let liftN : Finset Vnbr → Finset V := fun S => S.map embN
          let liftO : Finset Vother → Finset V := fun S => S.map embO
          have hliftN_card (S : Finset Vnbr) : (liftN S).card = S.card := by
            simp [liftN]
          have hliftO_card (S : Finset Vother) : (liftO S).card = S.card := by
            simp [liftO]
          have hliftN_adj (S : Finset Vnbr)
              (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Gn.Adj x y) :
              ∀ x ∈ liftN S, ∀ y ∈ liftN S, x ≠ y → G.Adj x y := by
            intro x hx y hy hxy
            rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
            rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
            have hab : a ≠ b := by intro h; apply hxy; cases h; rfl
            change G.Adj a.val b.val
            simpa [Gn] using hS a ha b hb hab
          have hliftO_adj (S : Finset Vother)
              (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Go.Adj x y) :
              ∀ x ∈ liftO S, ∀ y ∈ liftO S, x ≠ y → G.Adj x y := by
            intro x hx y hy hxy
            rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
            rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
            have hab : a ≠ b := by intro h; apply hxy; cases h; rfl
            change G.Adj a.val b.val
            simpa [Go] using hS a ha b hb hab
          have hliftN_ind (S : Finset Vnbr)
              (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Gn.Adj x y) :
              ∀ x ∈ liftN S, ∀ y ∈ liftN S, x ≠ y → ¬ G.Adj x y := by
            intro x hx y hy hxy hAdj
            rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
            rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
            have hab : a ≠ b := by intro h; apply hxy; cases h; rfl
            apply hS a ha b hb hab
            change G.Adj a.val b.val at hAdj
            simpa [Gn] using hAdj
          have hliftO_ind (S : Finset Vother)
              (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Go.Adj x y) :
              ∀ x ∈ liftO S, ∀ y ∈ liftO S, x ≠ y → ¬ G.Adj x y := by
            intro x hx y hy hxy hAdj
            rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
            rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
            have hab : a ≠ b := by intro h; apply hxy; cases h; rfl
            apply hS a ha b hb hab
            change G.Adj a.val b.val at hAdj
            simpa [Go] using hAdj
          by_cases hdeg : Nat.choose (s + t - 3) (s - 2) ≤ Nbr.card
          · have hrecCard : Nat.choose ((s - 1) + t - 2) ((s - 1) - 1) ≤ Fintype.card Vnbr := by
              rw [show (s - 1) + t - 2 = s + t - 3 by omega,
                show (s - 1) - 1 = s - 2 by omega, hcardNbr]
              exact hdeg
            rcases ih ((s - 1) + t) (by omega) (s - 1) t rfl Gn (by omega) ht hrecCard with
              ⟨C, hCcard, hC⟩ | ⟨I, hIcard, hI⟩
            · let C' := liftN C
              have hC'card : C'.card = s - 1 := by simpa [C', liftN] using hCcard
              have hvnotC : v ∉ C' := by
                intro hvC
                rcases Finset.mem_map.mp hvC with ⟨a, ha, hav⟩
                have havval : a.val = v := by change a.val = v at hav; exact hav
                have : v ∈ Nbr := by rw [← havval]; exact a.property
                exact hvnotNbr this
              have hAdjv : ∀ u ∈ C', G.Adj v u := by
                intro u hu
                rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
                exact (G.mem_neighborFinset v a.val).mp a.property
              left
              refine ⟨insert v C', ?_, ?_⟩
              · rw [Finset.card_insert_of_notMem hvnotC, hC'card]
                omega
              · intro u hu w hw huw
                simp only [Finset.mem_insert] at hu hw
                rcases hu with rfl | hu
                · rcases hw with rfl | hw
                  · exact (huw rfl).elim
                  · exact hAdjv w hw
                · rcases hw with rfl | hw
                  · exact G.adj_symm (hAdjv u hu)
                  · exact hliftN_adj C hC u hu w hw huw
            · right
              exact ⟨liftN I, (hliftN_card I).trans hIcard, hliftN_ind I hI⟩
          · have hdeglt : Nbr.card < Nat.choose (s + t - 3) (s - 2) := Nat.lt_of_not_ge hdeg
            have hOtherBound : Nat.choose (s + t - 3) (s - 1) ≤ Other.card := by
              rw [hPascal] at hcard
              omega
            have hrecCard : Nat.choose (s + (t - 1) - 2) (s - 1) ≤ Fintype.card Vother := by
              rw [show s + (t - 1) - 2 = s + t - 3 by omega, hcardOther]
              exact hOtherBound
            rcases ih (s + (t - 1)) (by omega) s (t - 1) rfl Go hs (by omega) hrecCard with
              ⟨C, hCcard, hC⟩ | ⟨I, hIcard, hI⟩
            · left
              exact ⟨liftO C, (hliftO_card C).trans hCcard, hliftO_adj C hC⟩
            · let I' := liftO I
              have hI'card : I'.card = t - 1 := by simpa [I', liftO] using hIcard
              have hvnotOther : v ∉ Other := by simp [Other]
              have hvnotI : v ∉ I' := by
                intro hvI
                rcases Finset.mem_map.mp hvI with ⟨a, ha, hav⟩
                have havval : a.val = v := by change a.val = v at hav; exact hav
                have haOther : v ∈ Other := by rw [← havval]; exact a.property
                exact hvnotOther haOther
              have hNotAdjv : ∀ u ∈ I', ¬ G.Adj v u := by
                intro u hu hAdj
                rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
                have haOther : a.val ∈ Other := a.property
                have haNotNbr : a.val ∉ Nbr := (Finset.mem_sdiff.mp haOther).2
                change G.Adj v a.val at hAdj
                exact haNotNbr ((G.mem_neighborFinset v a.val).mpr hAdj)
              right
              refine ⟨insert v I', ?_, ?_⟩
              · rw [Finset.card_insert_of_notMem hvnotI, hI'card]
                omega
              · intro u hu w hw huw
                simp only [Finset.mem_insert] at hu hw
                rcases hu with rfl | hu
                · rcases hw with rfl | hw
                  · exact (huw rfl).elim
                  · exact hNotAdjv w hw
                · rcases hw with rfl | hw
                  · intro hAdj
                    exact hNotAdjv u hu (G.adj_symm hAdj)
                  · exact hliftO_ind I hI u hu w hw huw
  exact hmain (s + t) s t rfl (V := V) G hs ht hcard

end HypercubeRamsey
