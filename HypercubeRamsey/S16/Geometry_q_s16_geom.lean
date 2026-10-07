import HypercubeRamsey.PartC.Resampling

namespace HypercubeRamsey.Lane_q_s16_geom

open Classical

universe u

/-- A finite loopless symmetric graph with degree at most `d` admits a greedy
coloring with `d + 1` colors. -/
theorem exists_coloring_of_degree_bound {α : Type u} [Fintype α]
    (adj : α → α → Prop) (d : ℕ)
    (hsymm : ∀ ⦃x y⦄, adj x y → adj y x)
    (hirr : ∀ x, ¬ adj x x)
    (hdegree : ∀ x, (Finset.univ.filter (adj x)).card ≤ d) :
    ∃ c : α → Fin (d + 1), ∀ ⦃x y⦄, adj x y → c x ≠ c y := by
  classical
  let P : ∀ (β : Type u) [Fintype β], Prop := fun β =>
    ∀ (r : β → β → Prop), (∀ ⦃x y⦄, r x y → r y x) →
      (∀ x, ¬ r x x) →
      (∀ x, (Finset.univ.filter (r x)).card ≤ d) →
      ∃ c : β → Fin (d + 1), ∀ ⦃x y⦄, r x y → c x ≠ c y
  have hP : P α := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ α
    · intro β γ _ e ih r hr hs hd
      letI : Fintype β := Fintype.ofEquiv γ e.symm
      have hdegree' : ∀ x : β,
          (Finset.univ.filter (fun y => r (e x) (e y))).card ≤ d := by
        intro x
        let s : Finset β := Finset.univ.filter (fun y => r (e x) (e y))
        let t : Finset γ := Finset.univ.filter (r (e x))
        have hcard : s.card = t.card := by
          apply Finset.card_bij (fun y _ => e y)
          · intro y hy
            change y ∈ Finset.univ.filter (fun z => r (e x) (e z)) at hy
            have hy' := (Finset.mem_filter.mp hy).2
            change e y ∈ Finset.univ.filter (r (e x))
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩
          · intro y₁ hy₁ y₂ hy₂ heq
            exact e.injective heq
          · intro y hy
            refine ⟨e.symm y, ?_, by simp⟩
            change y ∈ Finset.univ.filter (r (e x)) at hy
            have hy' := (Finset.mem_filter.mp hy).2
            change e.symm y ∈ Finset.univ.filter (fun z => r (e x) (e z))
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hy'⟩
        calc
          s.card = t.card := hcard
          _ ≤ d := hd (e x)
      obtain ⟨c, hc⟩ := ih (fun x y => r (e x) (e y))
        (by intro x y h; exact hr h)
        (by intro x h; exact hs (e x) h) hdegree'
      refine ⟨fun x => c (e.symm x), ?_⟩
      intro x y h
      exact hc (by simpa using h)
    · intro r hr hs hd
      refine ⟨(fun x => x.elim), ?_⟩
      intro x y h
      exact x.elim
    · intro β _ ih r hr hs hd
      have hdegree' : ∀ x : β,
          (Finset.univ.filter (fun y => r (some x) (some y))).card ≤ d := by
        intro x
        let s : Finset β := Finset.univ.filter (fun y => r (some x) (some y))
        let t : Finset (Option β) := Finset.univ.filter (r (some x))
        have hsub : s.image some ⊆ t := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
        have hcard : s.card ≤ t.card := by
          calc
            s.card = (s.image some).card := by
              symm
              exact Finset.card_image_of_injective _ (Option.some_injective β)
            _ ≤ t.card := Finset.card_le_card hsub
        exact hcard.trans (hd (some x))
      obtain ⟨c, hc⟩ := ih (fun x y => r (some x) (some y))
        (by intro x y h; exact hr h)
        (by intro x h; exact hs (some x) h) hdegree'
      let bad : Finset (Fin (d + 1)) :=
        (Finset.univ.filter (fun x : β => r none (some x))).image c
      have hbad : bad.card ≤ d := by
        let neigh : Finset β := Finset.univ.filter (fun x => r none (some x))
        let allNeigh : Finset (Option β) := Finset.univ.filter (r none)
        have hneighSub : neigh.image some ⊆ allNeigh := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        have hneigh : neigh.card ≤ allNeigh.card := by
          calc
            neigh.card = (neigh.image some).card := by
              symm
              exact Finset.card_image_of_injective _ (Option.some_injective β)
            _ ≤ allNeigh.card := Finset.card_le_card hneighSub
        calc
          bad.card ≤ neigh.card := by
            dsimp [bad, neigh]
            exact Finset.card_image_le
          _ ≤ allNeigh.card := hneigh
          _ ≤ d := hd none
      have hlt : bad.card < (Finset.univ : Finset (Fin (d + 1))).card := by
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨z, hz, hzn⟩ := bad.exists_mem_notMem_of_card_lt_card hlt
      refine ⟨(fun x => match x with | none => z | some y => c y), ?_⟩
      intro x y h
      cases x with
      | none =>
        cases y with
        | none => exact (hs none h).elim
        | some y =>
          change z ≠ c y
          intro heq
          have hy : y ∈ Finset.univ.filter (fun z : β => r none (some z)) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact h
          have hcy : c y ∈ bad := Finset.mem_image.mpr ⟨y, hy, rfl⟩
          exact hzn (heq ▸ hcy)
      | some x =>
        cases y with
        | none =>
          change c x ≠ z
          intro heq
          have h' : r none (some x) := hr h
          have hx : x ∈ Finset.univ.filter (fun z : β => r none (some z)) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact h'
          have hcx : c x ∈ bad := Finset.mem_image.mpr ⟨x, hx, rfl⟩
          exact hzn (heq.symm ▸ hcx)
        | some y =>
          change c x ≠ c y
          exact hc h
  exact hP adj hsymm hirr hdegree

/-- A Hamming ball in a Boolean cube is bounded by the sum of the binomial
layers through its radius. -/
theorem hamming_ball_card_le {m r : ℕ} (v : CubePos m) :
    (Finset.univ.filter fun w : CubePos m => hammingDist v w ≤ r).card ≤
      ∑ j ∈ Finset.range (r + 1), Nat.choose m j := by
  classical
  let diffEquiv : CubePos m ≃ Finset (Fin m) :=
    { toFun := fun w => Finset.univ.filter fun i => v i ≠ w i
      invFun := fun s i => if i ∈ s then !v i else v i
      left_inv := by
        intro w
        funext i
        by_cases h : v i = w i
        · simp [h]
        · have h' : w i = !v i := by
            cases hv : v i <;> cases hw : w i <;> simp_all
          simp [h']
      right_inv := by
        intro s
        ext i
        by_cases h : i ∈ s <;> simp [h] }
  let B : Finset (CubePos m) := Finset.univ.filter fun w => hammingDist v w ≤ r
  let S : Type := {s : Finset (Fin m) // s.card ≤ r}
  let layers : Type := Σ j : Fin (r + 1), {s : Finset (Fin m) // s.card = j.val}
  let toS : {w : CubePos m // w ∈ B} → S := fun w =>
    ⟨diffEquiv w.1, by
      have hw := w.2
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist] at hw
      simpa [diffEquiv] using hw⟩
  have hinj : Function.Injective toS := by
    intro x y h
    apply Subtype.ext
    apply diffEquiv.injective
    exact congrArg Subtype.val h
  have hball : B.card = Fintype.card {w : CubePos m // w ∈ B} := by
    rw [Fintype.card_subtype]
    simp
  have hS : Fintype.card S ≤ Fintype.card layers := by
    apply Fintype.card_le_of_injective
      (fun s : S => ⟨⟨s.1.card, by omega⟩, ⟨s.1, rfl⟩⟩)
    intro x y h
    apply Subtype.ext
    have hs := congrArg (fun z : layers => z.2.val) h
    exact hs
  have hlayers : Fintype.card layers =
      ∑ j ∈ Finset.range (r + 1), Nat.choose m j := by
    calc
      Fintype.card layers = ∑ j : Fin (r + 1),
          Fintype.card {s : Finset (Fin m) // s.card = j.val} := by
        simp [layers, Fintype.card_sigma]
      _ = ∑ j : Fin (r + 1), Nat.choose m j.val := by
        simp [Fintype.card_finset_len]
      _ = ∑ j ∈ Finset.range (r + 1), Nat.choose m j := by
        rw [Fin.sum_univ_eq_sum_range (fun j => Nat.choose m j) (r + 1)]
  calc
    B.card = Fintype.card {w : CubePos m // w ∈ B} := hball
    _ ≤ Fintype.card S := Fintype.card_le_of_injective toS hinj
    _ ≤ Fintype.card layers := hS
    _ = ∑ j ∈ Finset.range (r + 1), Nat.choose m j := hlayers

/-- A Boolean cube whose Hamming-ball layers fit in `d` colors can be colored
so that close distinct words receive different colors. -/
theorem cube_hamming_coloring {m r d : ℕ}
    (hbound : (∑ j ∈ Finset.range (r + 1), Nat.choose m j) ≤ d) :
    ∃ c : CubePos m → Fin (d + 1),
      ∀ ⦃x y⦄, x ≠ y → hammingDist x y ≤ r → c x ≠ c y := by
  classical
  let adj : CubePos m → CubePos m → Prop :=
    fun x y => x ≠ y ∧ hammingDist x y ≤ r
  letI : DecidableRel adj := fun x y => Classical.propDecidable _
  have hsymm : ∀ ⦃x y⦄, adj x y → adj y x := by
    intro x y h
    rcases h with ⟨hxy, hdist⟩
    refine ⟨hxy.symm, ?_⟩
    simpa [hammingDist, ne_comm] using hdist
  have hirr : ∀ x, ¬ adj x x := by
    intro x h
    exact h.1 rfl
  have hdegree : ∀ x, (Finset.univ.filter (adj x)).card ≤ d := by
    intro x
    let Nbr := Finset.univ.filter (adj x)
    let Ball := Finset.univ.filter (fun y : CubePos m => hammingDist x y ≤ r)
    have hsub : Nbr ⊆ Ball := by
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.2⟩
    calc
      Nbr.card ≤ Ball.card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ Finset.range (r + 1), Nat.choose m j := hamming_ball_card_le x
      _ ≤ d := hbound
  obtain ⟨c, hc⟩ := exists_coloring_of_degree_bound adj d hsymm hirr hdegree
  refine ⟨c, ?_⟩
  intro x y hxy hdist
  exact hc ⟨hxy, hdist⟩

theorem sum_choose_mono {m n r : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ Finset.range (r + 1), Nat.choose m j) ≤
      ∑ j ∈ Finset.range (r + 1), Nat.choose n j := by
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.choose_le_choose j hmn

/-- The number of rank starts divisible by a positive batch size is at most
`m / q + 1`. -/
theorem card_rank_starts_le (m q : ℕ) :
    Fintype.card {j : Fin m // j.val % q = 0} ≤ m / q + 1 := by
  classical
  let f : {j : Fin m // j.val % q = 0} → Fin (m / q + 1) := fun j =>
    ⟨j.1.val / q, by
      have hj : j.1.val / q ≤ m / q := Nat.div_le_div_right j.1.isLt.le
      omega⟩
  calc
    Fintype.card {j : Fin m // j.val % q = 0} ≤ Fintype.card (Fin (m / q + 1)) :=
      Fintype.card_le_of_injective f (by
        intro a b hab
        apply Subtype.ext
        apply Fin.ext
        have hquot : a.1.val / q = b.1.val / q := congrArg Fin.val hab
        have ha : a.1.val = q * (a.1.val / q) := by
          calc
            a.1.val = a.1.val % q + q * (a.1.val / q) :=
              (Nat.mod_add_div a.1.val q).symm
            _ = q * (a.1.val / q) := by rw [a.2]; simp
        have hb' : b.1.val = q * (b.1.val / q) := by
          calc
            b.1.val = b.1.val % q + q * (b.1.val / q) :=
              (Nat.mod_add_div b.1.val q).symm
            _ = q * (b.1.val / q) := by rw [b.2]; simp
        rw [ha, hb', hquot])
    _ = m / q + 1 := by simp

/-- The first rank in a size-`q` batch. -/
def batchStart (rank q : ℕ) : ℕ := rank / q * q

theorem batchStart_le_rank (rank q : ℕ) : batchStart rank q ≤ rank :=
  Nat.div_mul_le_self _ _

theorem batchStart_mod (rank q : ℕ) : batchStart rank q % q = 0 := by
  simp [batchStart]

theorem rank_eq_of_same_batch {r s q : ℕ}
    (hdiv : r / q = s / q) (hmod : r % q = s % q) : r = s := by
  calc
    r = r % q + q * (r / q) := (Nat.mod_add_div r q).symm
    _ = s % q + q * (s / q) := by rw [hmod, hdiv]
    _ = s := Nat.mod_add_div s q

end HypercubeRamsey.Lane_q_s16_geom
