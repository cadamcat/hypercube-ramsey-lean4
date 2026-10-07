import Mathlib

/-!
# Section 10.1a: the reusable Hamming syndrome projection

The construction is stated for any finite elementary abelian 2-group.  This is the
coordinate group of a binary chunk; taking a product over chunks gives the residual
projection used in Section 10 and the same algebraic statement is available to Part C.
-/

namespace HypercubeRamsey.S10

open scoped BigOperators

/-- The syndrome of a binary word indexed by a finite elementary abelian 2-group. -/
def chunkSyndrome {G : Type*} [Fintype G] [AddCommGroup G] (s : G → Bool) : G :=
  ∑ g : G, if s g then g else 0

/-- Flip one indexed bit. -/
def flipChunkBit {G : Type*} [DecidableEq G] (s : G → Bool) (g : G) : G → Bool :=
  fun i => if i = g then !s i else s i

/-- Correct a word by flipping the bit named by its syndrome. -/
def chunkProject {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (s : G → Bool) : G → Bool :=
  flipChunkBit s (chunkSyndrome s)

/-- Hamming distance between two words on one chunk. -/
def chunkHammingDistance {G : Type*} [Fintype G] [DecidableEq G]
    (s t : G → Bool) : ℕ :=
  (Finset.univ.filter fun g => s g ≠ t g).card

/-- P10.1a's generic one-chunk theorem. -/
def P10_1aProjectionStatement : Prop :=
  ∀ {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (h₂ : ∀ g : G, g + g = 0),
    (∀ s : G → Bool, chunkSyndrome (chunkProject s) = 0 ∧
      chunkHammingDistance s (chunkProject s) = 1) ∧
    (∀ t : G → Bool, chunkSyndrome t = 0 →
      (Finset.univ.filter fun s : G → Bool => chunkProject s = t).card = Fintype.card G)

/-- P10.1a (10:30–41): syndrome correction lands in the zero-syndrome class, flips
exactly one coordinate, and every zero-syndrome word has exactly one preimage per
coordinate. The statement is uniform in the finite binary coordinate group. -/
theorem p10_1a_hamming_projection : P10_1aProjectionStatement := by
  intro G hF hD hA h₂
  classical
  have flip_involutive (s : G → Bool) (g : G) :
      flipChunkBit (flipChunkBit s g) g = s := by
    funext i
    by_cases hi : i = g <;> simp [flipChunkBit, hi]
  have syndrome_flip (s : G → Bool) (g : G) :
      chunkSyndrome (flipChunkBit s g) = chunkSyndrome s + g := by
    unfold chunkSyndrome
    calc
      (∑ x : G, if flipChunkBit s g x then x else 0) =
          ∑ x : G, ((if s x then x else 0) + (if x = g then g else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxg : x = g
        · subst x
          by_cases hs : s g
          · simp [flipChunkBit, hs, h₂ g]
          · simp [flipChunkBit, hs]
        · simp [flipChunkBit, hxg]
      _ = _ := by simp [Finset.sum_add_distrib]
  have project_syndrome (s : G → Bool) :
      chunkSyndrome (chunkProject s) = 0 := by
    rw [chunkProject, syndrome_flip]
    exact h₂ (chunkSyndrome s)
  have project_distance (s : G → Bool) :
      chunkHammingDistance s (chunkProject s) = 1 := by
    have hset :
        Finset.univ.filter (fun g : G => s g ≠ chunkProject s g) =
          {chunkSyndrome s} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      by_cases hg : g = chunkSyndrome s
      · subst g
        simp [chunkProject, flipChunkBit]
      · simp [chunkProject, flipChunkBit, hg]
    simp [chunkHammingDistance, hset]
  constructor
  · intro s
    exact ⟨project_syndrome s, project_distance s⟩
  · intro t ht
    have hcard :
        (Finset.univ.filter fun s : G → Bool => chunkProject s = t).card =
          Fintype.card G := by
      calc
        (Finset.univ.filter fun s : G → Bool => chunkProject s = t).card =
            (Finset.univ : Finset G).card := by
          apply Finset.card_bij (fun s _ => chunkSyndrome s)
          · intro s hs
            simp
          · intro s₁ hs₁ s₂ hs₂ heq
            have hs₁proj : chunkProject s₁ = t :=
              (Finset.mem_filter.mp hs₁).2
            have hs₂proj : chunkProject s₂ = t :=
              (Finset.mem_filter.mp hs₂).2
            have recover (s : G → Bool) (hsp : chunkProject s = t) :
                s = flipChunkBit t (chunkSyndrome s) := by
              calc
                s = flipChunkBit (flipChunkBit s (chunkSyndrome s))
                    (chunkSyndrome s) := (flip_involutive s _).symm
                _ = flipChunkBit t (chunkSyndrome s) := by
                    rw [← chunkProject, hsp]
            rw [recover s₁ hs₁proj, recover s₂ hs₂proj, heq]
          · intro g hg
            refine ⟨flipChunkBit t g, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              constructor
              · simp
              · have hsynd :
                    chunkSyndrome (flipChunkBit t g) = g := by
                  rw [syndrome_flip, ht]
                  simp
                rw [chunkProject, hsynd]
                exact flip_involutive t g
            · rw [syndrome_flip, ht]
              simp
        _ = Fintype.card G := by simp
    exact hcard

/-- Project the ordinary neighbor obtained by flipping coordinate `l`. -/
def projectedNeighbor {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (s : G → Bool) (l : G) : G → Bool :=
  chunkProject (flipChunkBit s l)

/-- Coordinates whose ordinary neighbors project to the same site. -/
noncomputable def projectedNeighborFiber {G : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] (s t : G → Bool) : Finset G := by
  classical
  exact Finset.univ.filter fun l => projectedNeighbor s l = t

/-- Number of ordinary incidences in a projected-neighbor group. -/
noncomputable def projectedNeighborMultiplicity {G : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] (s t : G → Bool) : ℕ :=
  (projectedNeighborFiber s t).card

/-- P10.1a neighbor multiplicities: if the center syndrome is zero, all ordinary
neighbors project to one group; otherwise every nonempty group has multiplicity two. -/
theorem p10_1a_neighbour_multiplicities {G : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] (h₂ : ∀ g : G, g + g = 0) (s t : G → Bool) :
    projectedNeighborMultiplicity s t = 0 ∨
      (chunkSyndrome s = 0 ∧ projectedNeighborMultiplicity s t = Fintype.card G) ∨
      (chunkSyndrome s ≠ 0 ∧ projectedNeighborMultiplicity s t = 2) := by
  classical
  let σ := chunkSyndrome s
  have flip_involutive (u : G → Bool) (g : G) :
      flipChunkBit (flipChunkBit u g) g = u := by
    funext i
    by_cases hi : i = g <;> simp [flipChunkBit, hi]
  have syndrome_flip (u : G → Bool) (g : G) :
      chunkSyndrome (flipChunkBit u g) = chunkSyndrome u + g := by
    unfold chunkSyndrome
    calc
      (∑ x : G, if flipChunkBit u g x then x else 0) =
          ∑ x : G, ((if u x then x else 0) + (if x = g then g else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxg : x = g
        · subst x
          by_cases hu : u g
          · simp [flipChunkBit, hu, h₂ g]
          · simp [flipChunkBit, hu]
        · simp [flipChunkBit, hxg]
      _ = _ := by simp [Finset.sum_add_distrib]
  have nformula (l : G) :
      projectedNeighbor s l =
        flipChunkBit (flipChunkBit s l) (σ + l) := by
    unfold projectedNeighbor chunkProject
    rw [syndrome_flip]
  have flip_commute (u : G → Bool) (a b : G) :
      flipChunkBit (flipChunkBit u a) b =
        flipChunkBit (flipChunkBit u b) a := by
    funext x
    by_cases hxa : x = a
    · subst x
      by_cases hab : a = b
      · subst b
        simp [flipChunkBit]
      · simp [flipChunkBit, hab]
    · by_cases hxb : x = b
      ·
        have hba : b ≠ a := by
          intro h
          exact hxa (hxb.trans h)
        simp [flipChunkBit, hxb, hba]
      · simp [flipChunkBit, hxa, hxb]
  have add_involutive (x : G) : σ + (σ + x) = x := by
    calc
      σ + (σ + x) = (σ + σ) + x := (add_assoc σ σ x).symm
      _ = 0 + x := by rw [h₂ σ]
      _ = x := zero_add x
  have neighbor_pair (l : G) :
      projectedNeighbor s (σ + l) = projectedNeighbor s l := by
    rw [nformula (σ + l), nformula l, add_involutive]
    exact flip_commute s (σ + l) l
  have zero_neighbor (hσ : σ = 0) (l : G) :
      projectedNeighbor s l = s := by
    rw [nformula l, hσ, zero_add]
    exact flip_involutive s l
  by_cases hσ : σ = 0
  · by_cases hst : s = t
    · have hfiber : projectedNeighborFiber s t = Finset.univ := by
        ext l
        simp only [projectedNeighborFiber, Finset.mem_filter, Finset.mem_univ,
          true_and]
        rw [zero_neighbor hσ l]
        simpa using hst
      right
      left
      refine ⟨hσ, ?_⟩
      change (projectedNeighborFiber s t).card = Fintype.card G
      rw [hfiber]
      simp
    · have hfiber : projectedNeighborFiber s t = ∅ := by
        ext l
        simp only [projectedNeighborFiber, Finset.mem_filter, Finset.mem_univ,
          true_and]
        rw [zero_neighbor hσ l]
        simp [hst]
      left
      change (projectedNeighborFiber s t).card = 0
      rw [hfiber]
      simp
  · by_cases hzero : projectedNeighborMultiplicity s t = 0
    · exact Or.inl hzero
    · right
      right
      refine ⟨hσ, ?_⟩
      have coord_neq (l : G) : l ≠ σ + l := by
        intro heq
        apply hσ
        apply add_right_cancel
        calc
          σ + l = l := heq.symm
          _ = 0 + l := by simp
      have neighbor_eq_cases (m l : G)
          (heq : projectedNeighbor s m = projectedNeighbor s l) :
          m = l ∨ m = σ + l := by
        have hnot : projectedNeighbor s l l ≠ s l := by
          rw [nformula l]
          simp [flipChunkBit, coord_neq l]
        have hbad : projectedNeighbor s m l ≠ s l := by
          rw [heq]
          exact hnot
        by_cases hml : l = m
        · exact Or.inl hml.symm
        · by_cases hsm : l = σ + m
          · right
            calc
              m = σ + (σ + m) := (add_involutive m).symm
              _ = σ + l := by rw [hsm]
          · exfalso
            have hval : projectedNeighbor s m l = s l := by
              rw [nformula m]
              simp [flipChunkBit, hml, hsm]
            exact hbad hval
      have hpos : 0 < (projectedNeighborFiber s t).card := by
        unfold projectedNeighborMultiplicity at hzero
        exact Nat.pos_of_ne_zero hzero
      obtain ⟨l₀, hl₀⟩ := Finset.card_pos.mp hpos
      have hl₀out : projectedNeighbor s l₀ = t := by
        change l₀ ∈ Finset.univ.filter (fun l => projectedNeighbor s l = t) at hl₀
        exact (Finset.mem_filter.mp hl₀).2
      have hfiber : projectedNeighborFiber s t = {l₀, σ + l₀} := by
        ext m
        simp only [projectedNeighborFiber, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hm
          apply neighbor_eq_cases m l₀
          exact hm.trans hl₀out.symm
        · intro hm
          rcases hm with hm | hm
          · simpa [hm] using hl₀out
          · subst m
            exact (neighbor_pair l₀).trans hl₀out
      change (projectedNeighborFiber s t).card = 2
      rw [hfiber]
      simp [coord_neq l₀]

/-- A single chunk fiber has diameter at most two: each source differs from its
projected word in one coordinate. -/
theorem p10_1a_chunk_fiber_diameter {G : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] (h₂ : ∀ g : G, g + g = 0) (s t : G → Bool)
    (hproj : chunkProject s = chunkProject t) :
    chunkHammingDistance s t ≤ 2 := by
  classical
  have triangle (a b c : G → Bool) :
      chunkHammingDistance a c ≤
        chunkHammingDistance a b + chunkHammingDistance b c := by
    have hsub :
        (Finset.univ.filter fun x : G => a x ≠ c x) ⊆
          (Finset.univ.filter fun x => a x ≠ b x) ∪
            (Finset.univ.filter fun x => b x ≠ c x) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hab : a x = b x
      · right
        intro hbc
        exact hx (hab.trans hbc)
      · exact Or.inl hab
    unfold chunkHammingDistance
    calc
      _ ≤ ((Finset.univ.filter fun x : G => a x ≠ b x) ∪
          (Finset.univ.filter fun x => b x ≠ c x)).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter fun x : G => a x ≠ b x).card +
          (Finset.univ.filter fun x => b x ≠ c x).card := Finset.card_union_le _ _
  have distance_one (u : G → Bool) :
      chunkHammingDistance u (chunkProject u) = 1 := by
    have hset :
        Finset.univ.filter (fun g : G => u g ≠ chunkProject u g) =
          {chunkSyndrome u} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      by_cases hg : g = chunkSyndrome u
      · subst g
        simp [chunkProject, flipChunkBit]
      · simp [chunkProject, flipChunkBit, hg]
    simp [chunkHammingDistance, hset]
  have hs : chunkHammingDistance s (chunkProject s) = 1 := distance_one s
  have ht : chunkHammingDistance t (chunkProject s) = 1 := by
    calc
      chunkHammingDistance t (chunkProject s) =
          chunkHammingDistance t (chunkProject t) := by rw [hproj]
      _ = 1 := distance_one t
  have hbound := triangle s (chunkProject s) t
  have ht' : chunkHammingDistance (chunkProject s) t = 1 := by
    simpa [chunkHammingDistance, ne_comm] using ht
  omega

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {G : C → Type*} [∀ c, Fintype (G c)] [∀ c, DecidableEq (G c)]
  [∀ c, AddCommGroup (G c)]

/-- Apply the one-chunk projection independently in every chunk. -/
def productProject (s : ∀ c, G c → Bool) : ∀ c, G c → Bool :=
  fun c => chunkProject (s c)

/-- Total number of set bits across a chunked word. -/
def productTrueCount (s : ∀ c, G c → Bool) : ℕ :=
  ∑ c : C, (Finset.univ.filter fun g : G c => s c g).card

/-- Total Hamming distance across a chunked word. -/
def productHammingDistance (s t : ∀ c, G c → Bool) : ℕ :=
  ∑ c : C, chunkHammingDistance (s c) (t c)

/-- P10.1a, product parity clause: one bit is corrected in each chunk, so parity
changes exactly when the number of chunks is odd. -/
theorem p10_1a_product_parity
    (h₂ : ∀ c (g : G c), g + g = 0) (s : ∀ c, G c → Bool) :
    (Even (Fintype.card C) →
      (Even (productTrueCount s) ↔ Even (productTrueCount (productProject s)))) ∧
    (Odd (Fintype.card C) →
      (Even (productTrueCount s) ↔ ¬ Even (productTrueCount (productProject s)))) := by
  classical
  have count_flip (c : C) (u : G c → Bool) (g : G c) :
      Even ((Finset.univ.filter fun x : G c => u x).card) ↔
        ¬ Even ((Finset.univ.filter fun x : G c => flipChunkBit u g x).card) := by
    let A : Finset (G c) := Finset.univ.filter fun x => u x
    let B : Finset (G c) := Finset.univ.filter fun x => flipChunkBit u g x
    have even_succ (n : ℕ) : Even (n + 1) ↔ ¬ Even n := by
      exact Nat.even_add_one
    by_cases hg : u g
    · have hgA : g ∈ A := by simp [A, hg]
      have hset : B = A.erase g := by
        ext x
        by_cases hx : x = g
        · subst x
          simp [A, B, hg, flipChunkBit]
        · simp [A, B, hx, flipChunkBit]
      have hcard : B.card + 1 = A.card := by
        rw [hset]
        exact Finset.card_erase_add_one hgA
      rw [← hcard, even_succ]
    · have hnotA : g ∉ A := by simp [A, hg]
      have hset : B = insert g A := by
        ext x
        by_cases hx : x = g
        · subst x
          simp [A, B, hg, flipChunkBit]
        · simp [A, B, hx, flipChunkBit]
      have hcard : B.card = A.card + 1 := by
        rw [hset]
        exact Finset.card_insert_of_notMem hnotA
      rw [hcard, even_succ]
      simpa [A]
  let a : C → ℕ := fun c => (Finset.univ.filter fun g : G c => s c g).card
  let b : C → ℕ := fun c =>
    (Finset.univ.filter fun g : G c => chunkProject (s c) g).card
  have local_parity (c : C) : Even (a c) ↔ ¬ Even (b c) := by
    change Even ((Finset.univ.filter fun g : G c => s c g).card) ↔
      ¬ Even ((Finset.univ.filter fun g : G c => chunkProject (s c) g).card)
    rw [chunkProject]
    exact count_flip c (s c) (chunkSyndrome (s c))
  have sum_parity (S : Finset C) :
      Even (∑ c ∈ S, a c) ↔
        (Even (∑ c ∈ S, b c) ↔ Even S.card) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert c S hc ih =>
      rw [Finset.sum_insert hc, Finset.sum_insert hc,
        Finset.card_insert_of_notMem hc]
      rw [Nat.even_add, Nat.even_add, Nat.even_add_one]
      rw [local_parity c, ih]
      tauto
  have hrel :
      Even (productTrueCount s) ↔
        (Even (productTrueCount (productProject s)) ↔ Even (Fintype.card C)) := by
    change Even (∑ c : C, a c) ↔
      (Even (∑ c : C, b c) ↔ Even (Fintype.card C))
    simpa using (sum_parity (Finset.univ : Finset C))
  constructor
  · intro hEven
    simpa [hEven] using hrel
  · intro hOdd
    have hNotEven : ¬ Even (Fintype.card C) :=
      Nat.not_even_iff_odd.mpr hOdd
    simpa [hNotEven] using hrel

/-- The product projection flips exactly one bit per chunk. This cardinality form
is useful when a later argument only needs the total Hamming displacement. -/
theorem p10_1a_product_distance
    (h₂ : ∀ c (g : G c), g + g = 0) (s : ∀ c, G c → Bool) :
    productHammingDistance s (productProject s) = Fintype.card C := by
  classical
  have each (c : C) :
      chunkHammingDistance (s c) (chunkProject (s c)) = 1 := by
    have hset :
        Finset.univ.filter (fun g : G c => s c g ≠ chunkProject (s c) g) =
          {chunkSyndrome (s c)} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      by_cases hg : g = chunkSyndrome (s c)
      · subst g
        simp [chunkProject, flipChunkBit]
      · simp [chunkProject, flipChunkBit, hg]
    simp [chunkHammingDistance, hset]
  unfold productHammingDistance productProject
  calc
    (∑ c : C, chunkHammingDistance (s c) (chunkProject (s c))) =
        ∑ _c : C, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact each c
    _ = Fintype.card C := by simp

/-- Product fibers have diameter at most two coordinates per chunk. -/
theorem p10_1a_product_fiber_diameter
    (h₂ : ∀ c (g : G c), g + g = 0) (s t : ∀ c, G c → Bool)
    (hproj : productProject s = productProject t) :
    productHammingDistance s t ≤ 2 * Fintype.card C := by
  classical
  unfold productHammingDistance
  calc
    (∑ c : C, chunkHammingDistance (s c) (t c)) ≤
        ∑ _c : C, (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro c hc
      apply p10_1a_chunk_fiber_diameter (h₂ c) (s c) (t c)
      exact congrFun hproj c
    _ = 2 * Fintype.card C := by simp [Nat.mul_comm]

end HypercubeRamsey.S10
