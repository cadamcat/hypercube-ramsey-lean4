import HypercubeRamsey.S08.L81.HiddenNodes
import HypercubeRamsey.S08.L81.SelectionNodes_q_s08_sel

/-!
# Lemma 8.1, Step 5: hidden-history conditioning and local selection

Source: `sections/08-…tex`, lines 178–225 (L8.1f).
-/

noncomputable section

namespace HypercubeRamsey.S08

open HypercubeRamsey.Lane_q_s08_sel
open Classical OAI.HypercubeRamsey
open scoped BigOperators
set_option maxHeartbeats 5000000

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1f(ii) (08:179–189): the hidden event at `g` reads the tuples in `B_grid(g, 2)` (gates at `g` and its
neighbours, the centre and anchor laws there, the references); two events meet only within grid distance four, at
most `(2s+1)^4` of them; by the gate tail and Markov on `E_{Θ_g} q_{g,k} ≤ ε₀` (independence of `Θ_g`),
`q_H ≤ e^{-n^{c'}} + (T+1)ε₀^{1/2} ≤ e^{-n^{c_H}}`, and `x_H = 2q_H` satisfies `q_H ≤ x_H(1-x_H)^{(2s+1)^4}`. -/
theorem hidden_lll (c' : ℝ) (hc' : 0 < c') (hη₀ : 0 < η₀) (hh : 1 ≤ h) :
    ∃ cH > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n →
      D.GateTail c' → D.DenTail → D.HiddenLLL (2 * Real.exp (-(D.n : ℝ) ^ cH)) := by
  sorry

/-- L8.1f(iii) (08:196–199): on incident ball counts at most `2λ`, the internal IDs of a candidate list are chosen
from at most `(n+1)(H+1) 2λ ≤ n^{13}` IDs (`≤ T` of them) and each of the `≤ 2s` cross IDs from at most `(H+1)2λ`,
so there are at most `exp(25(s+T) log n)` candidate lists; the constant does not depend on `h`. -/
theorem list_count (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.ListCount := by
  classical
  obtain ⟨nScale, hScale⟩ := gridScaleBounds η₀ hη₀
  let n₀ := max nScale 9
  refine ⟨n₀, ?_⟩
  intro D hn hGF P c hPosCount
  have hn9 : 9 ≤ D.n := le_trans (Nat.le_max_right nScale 9) hn
  have hn4 : 4 ≤ D.n := by omega
  have hn3 : 3 ≤ D.n := by omega
  have hscale := hScale D.n (le_trans (Nat.le_max_left nScale 9) hn)
  obtain ⟨hs, hT, hH⟩ := hscale
  have hd : dC η₀ D.n ≤ D.n := by
    have hreal := hGF.hd_ok.2.2
    exact_mod_cast (by simpa using hreal)
  have hOrd : (ordNbrs c.2).card ≤ 2 * D.n := by
    calc
      (ordNbrs c.2).card ≤ dC η₀ D.n + 1 := ordNbrs_card_bound c.2
      _ ≤ D.n + 1 := Nat.add_le_add_right hd 1
      _ ≤ 2 * D.n := by omega
  have hLevels : HH η₀ D.n + 1 ≤ 2 * D.n := by omega
  have hCountAt (k : D.KeyT) (v : D.ResT) (j : Fin (HH η₀ D.n + 1))
      (he : PadNbr c (k, v)) : D.ballCount P k v j ≤ 2 * D.n ^ 10 := by
    have hReal : (D.ballCount P k v j : ℝ) ≤ 2 * (D.n : ℝ) ^ 10 := by
      simpa [hdP, HDParams.lam, Real.rpow_natCast] using hPosCount (k, v) he j
    exact_mod_cast hReal
  let internalPool : Finset D.Loc := (ordNbrs c.2).biUnion fun v =>
    (Finset.univ : Finset (Fin (HH η₀ D.n + 1))).biUnion fun j =>
      localIdsAt D P c.1 v j
  have hInternalCard : internalPool.card ≤ 8 * D.n ^ 12 := by
    calc
      internalPool.card ≤ ∑ v ∈ ordNbrs c.2,
          ((Finset.univ : Finset (Fin (HH η₀ D.n + 1))).biUnion
            (fun j => localIdsAt D P c.1 v j)).card :=
        Finset.card_biUnion_le (s := ordNbrs c.2)
          (t := fun v => (Finset.univ : Finset (Fin (HH η₀ D.n + 1))).biUnion
            (fun j => localIdsAt D P c.1 v j))
      _ ≤ ∑ v ∈ ordNbrs c.2, ∑ j : Fin (HH η₀ D.n + 1),
          (localIdsAt D P c.1 v j).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin (HH η₀ D.n + 1))))
          (t := fun j => localIdsAt D P c.1 v j)
      _ ≤ ∑ v ∈ ordNbrs c.2, ∑ j : Fin (HH η₀ D.n + 1), 2 * D.n ^ 10 := by
        apply Finset.sum_le_sum
        intro v hv
        apply Finset.sum_le_sum
        intro j hj
        rw [localIdsAt_card]
        exact hCountAt c.1 v j (Or.inl ⟨rfl, hv⟩)
      _ = (ordNbrs c.2).card * (HH η₀ D.n + 1) * (2 * D.n ^ 10) := by
        simp [Finset.sum_const, Nat.mul_assoc]
      _ ≤ (2 * D.n) * (2 * D.n) * (2 * D.n ^ 10) := by gcongr
      _ = 8 * D.n ^ 12 := by ring
  have hInternalPlus : internalPool.card + 1 ≤ D.n ^ 13 := by
    have hn12 : 1 ≤ D.n ^ 12 := Nat.one_le_pow 12 D.n (by omega)
    calc
      internalPool.card + 1 ≤ 8 * D.n ^ 12 + 1 := Nat.add_le_add_right hInternalCard 1
      _ ≤ 9 * D.n ^ 12 := by omega
      _ ≤ D.n * D.n ^ 12 := Nat.mul_le_mul_right _ (by omega)
      _ = D.n ^ 13 := by rw [pow_succ]; ring
  let crossPool (u : D.CrossSub c.1) : Finset D.Loc :=
    Finset.univ.filter fun ℓ => P u.1 ℓ = true ∧ _root_.hammingDist ℓ.1 c.2 ≤ rH D.n
  have hCrossPoolCard (u : D.CrossSub c.1) : (crossPool u).card ≤ D.n ^ 12 := by
    let allLevels : Finset D.Loc :=
      (Finset.univ : Finset (Fin (HH η₀ D.n + 1))).biUnion fun j =>
        localIdsAt D P u.1 c.2 j
    have hsub : crossPool u ⊆ allLevels := by
      intro ℓ hℓ
      rcases Finset.mem_filter.mp hℓ with ⟨_, ⟨hp, hdℓ⟩⟩
      have heq : (ℓ.1, ℓ.2) = ℓ := by cases ℓ; rfl
      have hp' : P u.1 (ℓ.1, ℓ.2) = true := by rw [heq]; exact hp
      refine Finset.mem_biUnion.mpr ⟨ℓ.2, Finset.mem_univ _, ?_⟩
      simp only [localIdsAt, Finset.mem_image]
      refine ⟨ℓ.1, ?_, heq⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hp', hdℓ⟩
    calc
      (crossPool u).card ≤ allLevels.card := Finset.card_le_card hsub
      _ ≤ ∑ j : Fin (HH η₀ D.n + 1), (localIdsAt D P u.1 c.2 j).card :=
        Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin (HH η₀ D.n + 1))))
          (t := fun j => localIdsAt D P u.1 c.2 j)
      _ ≤ ∑ j : Fin (HH η₀ D.n + 1), 2 * D.n ^ 10 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [localIdsAt_card]
        exact hCountAt u.1 c.2 j (Or.inr ⟨rfl, u.2⟩)
      _ = (HH η₀ D.n + 1) * (2 * D.n ^ 10) := by simp [Finset.sum_const]
      _ ≤ D.n ^ 12 := by
        calc
          (HH η₀ D.n + 1) * (2 * D.n ^ 10) ≤ (2 * D.n) * (2 * D.n ^ 10) := by gcongr
          _ = 4 * D.n ^ 11 := by ring
          _ ≤ D.n * D.n ^ 11 := Nat.mul_le_mul_right _ (by omega)
          _ = D.n ^ 12 := by rw [pow_succ]; ring
  have hTpos : 1 ≤ TC η₀ D.n := by
    have hτ : 0 < tau8 η₀ := by
      rw [tau8_eq]
      have hη : 0 < eta8 η₀ := lt_min (by linarith) (by norm_num)
      exact div_pos hη (by norm_num)
    have hnR : (1 : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.n)
    have hpow : (1 : ℝ) ≤ (D.n : ℝ) ^ (tau8 η₀ / 8) :=
      Real.one_le_rpow hnR (by positivity)
    have hceil : (1 : ℝ) ≤ (⌈(D.n : ℝ) ^ (tau8 η₀ / 8)⌉₊ : ℝ) :=
      hpow.trans (Nat.le_ceil ((D.n : ℝ) ^ (tau8 η₀ / 8)))
    exact_mod_cast (by simpa [TC] using hceil)
  have hspos : 1 ≤ sC η₀ D.n := hGF.pos.2.2
  let intChoices := internalPool.powerset.filter fun A : Finset D.Loc => A.card ≤ TC η₀ D.n
  let crossChoices := Fintype.piFinset crossPool
  have hIntChoices : intChoices.card ≤ (D.n ^ 13) ^ (TC η₀ D.n + 1) := by
    calc
      intChoices.card ≤ (internalPool.card + 1) ^ (TC η₀ D.n + 1) := by
        simpa [intChoices] using small_powerset_card internalPool (TC η₀ D.n)
      _ ≤ (D.n ^ 13) ^ (TC η₀ D.n + 1) := by gcongr
  have hCrossChoices : crossChoices.card ≤ (D.n ^ 12) ^ (2 * sC η₀ D.n) := by
    have hcrossCard : Fintype.card (D.CrossSub c.1) ≤ 2 * sC η₀ D.n := by
      simpa [Ctx.CrossSub] using hGF.crossKeys_card c.1
    calc
      crossChoices.card = ∏ u : D.CrossSub c.1, (crossPool u).card := by
        simp [crossChoices, Fintype.card_piFinset]
      _ ≤ (D.n ^ 12) ^ Fintype.card (D.CrossSub c.1) :=
        Finset.prod_le_pow_card Finset.univ (fun u => (crossPool u).card) (D.n ^ 12)
          (by intro u hu; exact hCrossPoolCard u)
      _ ≤ (D.n ^ 12) ^ (2 * sC η₀ D.n) := by gcongr
      _ = (D.n ^ 12) ^ (2 * sC η₀ D.n) := rfl
  let candidates : Finset (D.LList c.1) := Finset.univ.filter fun L => D.Cand P c L
  have hInternalSubset (L : D.LList c.1) (hL : D.Cand P c L) : L.1 ⊆ internalPool := by
    intro ℓ hℓ
    rcases hL.2.1 ℓ hℓ with ⟨hp, b, hb, hdist⟩
    have heq : (ℓ.1, ℓ.2) = ℓ := by cases ℓ; rfl
    have hp' : P c.1 (ℓ.1, ℓ.2) = true := by rw [heq]; exact hp
    refine Finset.mem_biUnion.mpr ⟨b, hb,
      Finset.mem_biUnion.mpr ⟨ℓ.2, Finset.mem_univ _, ?_⟩⟩
    simp only [localIdsAt, Finset.mem_image]
    refine ⟨ℓ.1, ?_, heq⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp', hdist⟩
  have hinjective : Function.Injective (fun L : D.LList c.1 => (L.1, L.2)) := by
    intro L L' h
    exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hImageSubset : candidates.image (fun L => (L.1, L.2)) ⊆ intChoices ×ˢ crossChoices := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨L, hL, rfl⟩
    have hCand := (Finset.mem_filter.mp hL).2
    have hIntMem : L.1 ∈ intChoices := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (hInternalSubset L hCand), hCand.1⟩
    have hCrossMem : L.2 ∈ crossChoices := by
      apply Fintype.mem_piFinset.mpr
      intro u
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (hCand.2.2 u).1, (hCand.2.2 u).2⟩
    exact Finset.mem_product.mpr ⟨hIntMem, hCrossMem⟩
  have hCandidateCount : candidates.card ≤ intChoices.card * crossChoices.card := by
    calc
      candidates.card = (candidates.image (fun L => (L.1, L.2))).card := by
        symm
        exact Finset.card_image_of_injective candidates hinjective
      _ ≤ (intChoices ×ˢ crossChoices).card := Finset.card_le_card hImageSubset
      _ = intChoices.card * crossChoices.card := by simp
  have hCandidateNat : candidates.card ≤ D.n ^ (25 * (sC η₀ D.n + TC η₀ D.n)) := by
    calc
      candidates.card ≤ intChoices.card * crossChoices.card := hCandidateCount
      _ ≤ (D.n ^ 13) ^ (TC η₀ D.n + 1) * (D.n ^ 12) ^ (2 * sC η₀ D.n) :=
        Nat.mul_le_mul hIntChoices hCrossChoices
      _ = D.n ^ (13 * (TC η₀ D.n + 1) + 12 * (2 * sC η₀ D.n)) := by
        calc
          (D.n ^ 13) ^ (TC η₀ D.n + 1) * (D.n ^ 12) ^ (2 * sC η₀ D.n) =
              D.n ^ (13 * (TC η₀ D.n + 1)) * (D.n ^ 12) ^ (2 * sC η₀ D.n) := by
            rw [(Nat.pow_mul D.n 13 (TC η₀ D.n + 1)).symm]
          _ = D.n ^ (13 * (TC η₀ D.n + 1)) * D.n ^ (12 * (2 * sC η₀ D.n)) := by
            rw [(Nat.pow_mul D.n 12 (2 * sC η₀ D.n)).symm]
          _ = D.n ^ (13 * (TC η₀ D.n + 1) + 12 * (2 * sC η₀ D.n)) := by
            rw [← Nat.pow_add]
      _ ≤ D.n ^ (25 * (sC η₀ D.n + TC η₀ D.n)) := by
        exact Nat.pow_le_pow_right (by omega) (by omega)
  have hnReal : (0 : ℝ) < D.n := by exact_mod_cast (by omega : 0 < D.n)
  have hPowExp : (D.n : ℝ) ^ (25 * (sC η₀ D.n + TC η₀ D.n)) =
      Real.exp (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) * Real.log (D.n : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hnReal]
    congr 1
    push_cast
    ring
  change (candidates.card : ℝ) ≤
    Real.exp (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) * Real.log (D.n : ℝ))
  calc
    (candidates.card : ℝ) ≤ (D.n : ℝ) ^ (25 * (sC η₀ D.n + TC η₀ D.n)) := by
      exact_mod_cast hCandidateNat
    _ = Real.exp (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) * Real.log (D.n : ℝ)) := hPowExp

/-- L8.1f(iv) (08:208–212): a family has fewer than `n` lists of at most `T + 2s` IDs; an even site has at most
`(n - m + 1) + 2s` incident odd cells; so at most `n(n+1+2s)(T+2s) = o(λ)` IDs are forbidden at a site-level, and
at least `λ/2 - o(λ) ≥ λ/3` present IDs remain eligible. -/
theorem legal_of_counts (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.LegalOfCounts := by
  classical
  obtain ⟨nScale, hScale⟩ := gridScaleBounds η₀ hη₀
  let n₀ := max nScale 3
  refine ⟨n₀, ?_⟩
  intro D hn hGF Θ P t hPos hFew g b j
  have hn3 : 3 ≤ D.n := le_trans (Nat.le_max_right nScale 3) hn
  have hscale := hScale D.n (le_trans (Nat.le_max_left nScale 3) hn)
  obtain ⟨hs, hT, hH⟩ := hscale
  have hd : dC η₀ D.n ≤ D.n := by
    have hreal := hGF.hd_ok.2.2
    exact_mod_cast (by simpa using hreal)
  let B := localIdsAt D P g b j
  have hBcard : B.card = D.ballCount P g b j := by
    exact localIdsAt_card D P g b j
  let incident : Finset D.CellT := Finset.univ.filter fun c => PadNbr c (g, b)
  let ordinary : Finset D.CellT := (ordNbrs b).image fun v => (g, v)
  let crossing : Finset D.CellT := (crossKeys g).image fun u => (u, b)
  have hIncidentSubset : incident ⊆ ordinary ∪ crossing := by
    intro c hc
    have hpad := (Finset.mem_filter.mp hc).2
    rcases hpad with ⟨hkey, hres⟩ | ⟨hres, hkey⟩
    · have hb : _root_.hammingDist b c.2 ≤ 1 := by
        have hb' : _root_.hammingDist c.2 b ≤ 1 := by simpa [ordNbrs] using hres
        rw [_root_.hammingDist_comm]
        exact hb'
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨c.2, ?_, ?_⟩
      · simpa [ordNbrs] using hb
      · exact Prod.ext hkey rfl
    · apply Finset.mem_union.mpr
      right
      have hcross : c.1 ∈ crossKeys g := by
        simpa [crossKeys, keyDist_symm] using hkey
      apply Finset.mem_image.mpr
      refine ⟨c.1, hcross, ?_⟩
      exact Prod.ext rfl hres
  have hIncidentCard : incident.card ≤ 4 * D.n := by
    calc
      incident.card ≤ ordinary.card + crossing.card := by
        exact (Finset.card_le_card hIncidentSubset).trans (Finset.card_union_le _ _)
      _ ≤ (ordNbrs b).card + (crossKeys g).card := by
        dsimp [ordinary, crossing]
        exact Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ dC η₀ D.n + 1 + 2 * sC η₀ D.n := by
        exact Nat.add_le_add (ordNbrs_card_bound b) (hGF.crossKeys_card g)
      _ ≤ 4 * D.n := by omega
  let familySet (c : D.CellT) : Finset (D.LList c.1) := (D.family Θ P t c).toFinset
  let idsAtCell (c : D.CellT) (L : D.LList c.1) : Finset D.Loc :=
    ((D.listIds c.1 L).filter fun id => id.1 = g).image Prod.snd
  let cover : Finset D.Loc := incident.biUnion fun c =>
    (familySet c).biUnion (idsAtCell c)
  have hIdsAtCell (c : D.CellT) (L : D.LList c.1) (hL : L ∈ familySet c) :
      (idsAtCell c L).card ≤ TC η₀ D.n + 2 * sC η₀ D.n := by
    have hCand := family_candidate D Θ P t c (List.mem_toFinset.mp hL)
    have hList := listIds_card_bound D c.1 L
    calc
      (idsAtCell c L).card ≤ (D.listIds c.1 L).card := by
        dsimp [idsAtCell]
        exact (Finset.card_image_le.trans (Finset.card_filter_le _ _))
      _ ≤ L.1.card + (crossKeys c.1).card := hList
      _ ≤ TC η₀ D.n + 2 * sC η₀ D.n := by
        exact Nat.add_le_add hCand.1 (hGF.crossKeys_card c.1)
  have hFamilyCard (c : D.CellT) : (familySet c).card ≤ D.n := by
    dsimp [familySet]
    exact (List.toFinset_card_le _).trans (Nat.le_of_lt (hFew c))
  have hCoverCard : cover.card ≤ incident.card * D.n * (TC η₀ D.n + 2 * sC η₀ D.n) := by
    calc
      cover.card ≤ ∑ c ∈ incident, ((familySet c).biUnion (idsAtCell c)).card := by
        exact Finset.card_biUnion_le (s := incident) (t := fun c => (familySet c).biUnion (idsAtCell c))
      _ ≤ ∑ c ∈ incident, (familySet c).card * (TC η₀ D.n + 2 * sC η₀ D.n) := by
        apply Finset.sum_le_sum
        intro c hc
        calc
          ((familySet c).biUnion (idsAtCell c)).card ≤
              ∑ L ∈ familySet c, (idsAtCell c L).card :=
            Finset.card_biUnion_le (s := familySet c) (t := idsAtCell c)
          _ ≤ ∑ L ∈ familySet c, (TC η₀ D.n + 2 * sC η₀ D.n) := by
            apply Finset.sum_le_sum
            intro L hL
            exact hIdsAtCell c L hL
          _ = (familySet c).card * (TC η₀ D.n + 2 * sC η₀ D.n) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ c ∈ incident, (D.n * (TC η₀ D.n + 2 * sC η₀ D.n)) := by
        apply Finset.sum_le_sum
        intro c hc
        exact Nat.mul_le_mul_right _ (hFamilyCard c)
      _ = incident.card * D.n * (TC η₀ D.n + 2 * sC η₀ D.n) := by
        simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_assoc]
  have hTandS : TC η₀ D.n + 2 * sC η₀ D.n ≤ 3 * D.n := by omega
  have hCoverBound : cover.card ≤ 12 * D.n ^ 3 := by
    calc
      cover.card ≤ incident.card * D.n * (TC η₀ D.n + 2 * sC η₀ D.n) := hCoverCard
      _ ≤ (4 * D.n) * D.n * (3 * D.n) := by gcongr
      _ = 12 * D.n ^ 3 := by ring
  let forbidden : Finset D.Loc := B.filter fun ℓ => D.Forbidden Θ P t (g, b) ℓ
  have hForbiddenSubset : forbidden ⊆ cover := by
    intro ℓ hℓ
    rcases Finset.mem_filter.mp hℓ with ⟨_, ⟨c, hpad, L, hL, hid, _⟩⟩
    have hc : c ∈ incident := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpad⟩
    have hL' : L ∈ familySet c := List.mem_toFinset.mpr hL
    have hid' : (g, ℓ) ∈ (D.listIds c.1 L).filter fun id => id.1 = g :=
      Finset.mem_filter.mpr ⟨hid, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc,
      Finset.mem_biUnion.mpr ⟨L, hL', Finset.mem_image.mpr ⟨(g, ℓ), hid', rfl⟩⟩⟩
  have hForbiddenCard : forbidden.card ≤ 12 * D.n ^ 3 :=
    (Finset.card_le_card hForbiddenSubset).trans hCoverBound
  let eligible := B.filter fun ℓ => ¬ D.Forbidden Θ P t (g, b) ℓ
  have hEligEq : D.elig Θ P t g b j = eligible := by
    ext ℓ
    constructor
    · intro hℓ
      simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
      rcases hℓ with ⟨hp, hj, hd, hforbid⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨ℓ.1, ?_, ?_⟩, hforbid⟩
      · simp only [localIdsAt, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and]
        have hp' : P g (ℓ.1, j) = true := by
          have heq : (ℓ.1, j) = ℓ := Prod.ext rfl hj.symm
          rw [heq]
          exact hp
        exact ⟨hp', hd⟩
      · exact Prod.ext rfl hj.symm
    · intro hℓ
      rcases Finset.mem_filter.mp hℓ with ⟨hB, hforbid⟩
      rcases Finset.mem_image.mp hB with ⟨u, hu, rfl⟩
      rcases Finset.mem_filter.mp hu with ⟨_, ⟨hp, hd⟩⟩
      simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hp, hd, hforbid⟩
  have hSplit := Finset.card_filter_add_card_filter_not (s := B)
    (fun ℓ => D.Forbidden Θ P t (g, b) ℓ)
  have hBDecomp : B.card = eligible.card + forbidden.card := by
    simpa [eligible, forbidden, Nat.add_comm] using hSplit.symm
  have hBallLower : (hdP η₀ D.n).lam / 2 ≤ (B.card : ℝ) := by
    simpa [B, localIdsAt_card] using (hPos g b j).1
  have hForbiddenSmall : (forbidden.card : ℝ) ≤ (hdP η₀ D.n).lam / 6 := by
    have hnPow : 72 ≤ D.n ^ 7 := by
      calc
        72 ≤ 3 ^ 7 := by norm_num
        _ ≤ D.n ^ 7 := by gcongr
    have hnPowR : (72 : ℝ) ≤ (D.n : ℝ) ^ 7 := by exact_mod_cast hnPow
    have hnProd := mul_le_mul_of_nonneg_right hnPowR (show 0 ≤ (D.n : ℝ) ^ 3 by positivity)
    have hpow : (D.n : ℝ) ^ (10 : ℕ) = (D.n : ℝ) ^ (7 : ℕ) * (D.n : ℝ) ^ (3 : ℕ) := by
      calc
        (D.n : ℝ) ^ (10 : ℕ) = (D.n : ℝ) ^ (7 + 3 : ℕ) := by norm_num
        _ = (D.n : ℝ) ^ (7 : ℕ) * (D.n : ℝ) ^ (3 : ℕ) := by rw [pow_add]
    have hsmall : (12 : ℝ) * (D.n : ℝ) ^ (3 : ℕ) ≤ (D.n : ℝ) ^ (10 : ℕ) / 6 := by
      rw [hpow]
      nlinarith [hnProd]
    calc
      (forbidden.card : ℝ) ≤ (12 * D.n ^ 3 : ℕ) := by exact_mod_cast hForbiddenCard
      _ = 12 * (D.n : ℝ) ^ 3 := by norm_num
      _ ≤ (hdP η₀ D.n).lam / 6 := by
        simpa [hdP, HDParams.lam, Real.rpow_natCast] using hsmall
  have hLegalCard : (hdP η₀ D.n).lam / 3 ≤ (D.elig Θ P t g b j).card := by
    have hDecompR : (B.card : ℝ) = (eligible.card : ℝ) + (forbidden.card : ℝ) := by
      exact_mod_cast hBDecomp
    have hEligibleLower : (hdP η₀ D.n).lam / 3 ≤ (eligible.card : ℝ) := by
      linarith [hDecompR, hBallLower, hForbiddenSmall]
    rw [hEligEq]
    exact hEligibleLower
  change (∀ ℓ ∈ D.elig Θ P t g b j,
      P g ℓ = true ∧ ℓ.2 = j ∧ _root_.hammingDist ℓ.1 b ≤ rH D.n) ∧
      (hdP η₀ D.n).lam / 3 ≤ (D.elig Θ P t g b j).card
  constructor
  · intro ℓ hℓ
    simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    exact ⟨hℓ.1, hℓ.2.1, hℓ.2.2.1⟩
  · exact hLegalCard

/-- L8.1f(v) (08:130–131, 212–214): on selection success, good heights select at every site (`¬ Bad` at the
selected level gives an active eligible ID); the ordinary neighbours of an odd cell lie within distance `D = 2`, so
their heights take at most two values and the crowd bound at one site per level gives at most `2n^b ≤ T` distinct
internal IDs; the realized list is a candidate list all of whose IDs are eligible where they are used, so it is
not bad (otherwise it meets a family list, whose IDs are forbidden there); legality follows from
`LegalOfCounts`. -/
private theorem height_selectionAt_spec (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties) (R : ℕ)
    (v : CubeVertex p.d) (hheight : p.height Sites P A E R v < p.H)
    (hbad : ¬ p.Bad P A E v ⟨p.height Sites P A E R v, by omega⟩) :
    ∃ ℓ, p.selectionAt Sites P A E τ R v = some ℓ ∧
      ℓ ∈ E v ⟨p.height Sites P A E R v, by omega⟩ ∧ A ℓ = true := by
  classical
  let j := p.height Sites P A E R v
  let j' : Fin (p.H + 1) := ⟨j, by omega⟩
  let active := (E v j').filter fun ℓ => A ℓ = true
  have hActive : active.Nonempty := by
    by_contra hne
    have hall : ∀ ℓ ∈ E v j', A ℓ = false := by
      intro ℓ hℓ
      cases hA : A ℓ with
      | false => rfl
      | true => exact False.elim (hne ⟨ℓ, Finset.mem_filter.mpr ⟨hℓ, hA⟩⟩)
    exact hbad (Or.inl hall)
  let priorities := active.image (fun ℓ => p.priority τ (v, j') ℓ)
  have hPriorities : priorities.Nonempty := by
    obtain ⟨ℓ, hℓ⟩ := hActive
    exact ⟨p.priority τ (v, j') ℓ, Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩⟩
  let q := priorities.min' hPriorities
  have hq : q ∈ priorities := Finset.min'_mem priorities hPriorities
  have hmem : ∃ ℓ, ℓ ∈ active ∧ p.priority τ (v, j') ℓ = q := by
    simpa [priorities, q] using Finset.mem_image.mp hq
  let chosen := Classical.choose hmem
  have hchosen : chosen ∈ active ∧ p.priority τ (v, j') chosen = q := Classical.choose_spec hmem
  refine ⟨chosen, ?_, ?_, ?_⟩
  · simp [HDParams.selectionAt, j, j', active, priorities, q, hheight, hbad,
      hPriorities, hq, hmem, chosen]
  · exact (Finset.mem_filter.mp hchosen.1).1
  · exact (Finset.mem_filter.mp hchosen.1).2

private theorem sel_witness_of_good_heights (D : Ctx η₀ β p h) (q : D.Pre)
    (hGood : D.GoodH q.1.1 q.1.2 q.2.1.1 q.2.1.2) (e : D.CellT) :
    ∃ ℓ, D.sel q e = some ℓ ∧
      ℓ ∈ D.elig q.1.1 q.1.2 q.2.1.1 e.1 e.2
        ⟨(hdP η₀ D.n).height Finset.univ (q.1.2 e.1) (q.2.1.2 e.1)
          (D.elig q.1.1 q.1.2 q.2.1.1 e.1) (hdP η₀ D.n).Rlong e.2,
          by have hh := ((hGood e.1) e.2 (Finset.mem_univ _)).1; omega⟩ ∧
      q.2.1.2 e.1 ℓ = true := by
  let p := hdP η₀ D.n
  have hGH := hGood e.1
  obtain ⟨hheight, hnotBadN, _⟩ := hGH e.2 (Finset.mem_univ _)
  let j := p.height Finset.univ (q.1.2 e.1) (q.2.1.2 e.1)
    (D.elig q.1.1 q.1.2 q.2.1.1 e.1) p.Rlong e.2
  have hj : j < p.H := by simpa [p, j] using hheight
  have hnotBadN' : ¬ p.BadN (q.1.2 e.1) (q.2.1.2 e.1)
      (D.elig q.1.1 q.1.2 q.2.1.1 e.1) e.2 j := by
    simpa [p, j] using hnotBadN
  have hbad : ¬ p.Bad (q.1.2 e.1) (q.2.1.2 e.1)
      (D.elig q.1.1 q.1.2 q.2.1.1 e.1) e.2 ⟨j, by omega⟩ := by
    intro hb
    apply hnotBadN'
    exact ⟨by omega, by simpa [p, j] using hb⟩
  obtain ⟨ℓ, hselection, hEligible, hActive⟩ := height_selectionAt_spec p Finset.univ
    (q.1.2 e.1) (q.2.1.2 e.1) (D.elig q.1.1 q.1.2 q.2.1.1 e.1) (q.2.2 e.1)
    p.Rlong e.2 hheight hbad
  refine ⟨ℓ, ?_, ?_, hActive⟩
  · simpa [Ctx.sel, HDParams.selection, p] using hselection
  · simpa [p, j] using hEligible

theorem sel_conseq (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.LegalOfCounts → D.SelConseq := by
  classical
  obtain ⟨nScale, hScale⟩ := gridScaleBounds η₀ hη₀
  let b := bH η₀
  have hbpos : 0 < b := by
    dsimp [b]
    exact div_pos (tau8_pos hη₀) (by norm_num)
  have hpowT : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ b)
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop hbpos).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, (6 : ℝ) ≤ (n : ℝ) ^ b :=
    hpowT.eventually (Filter.eventually_ge_atTop 6)
  obtain ⟨nFan, hFan⟩ := Filter.eventually_atTop.1 hlarge
  let n₀ := max nScale nFan
  refine ⟨n₀, ?_⟩
  intro D hn hGF hLegal q hSelOK
  rcases hSelOK with ⟨hPos, hFew, hGood⟩
  have hnScale : nScale ≤ D.n := le_trans (Nat.le_max_left _ _) hn
  have hnFan : nFan ≤ D.n := le_trans (Nat.le_max_right _ _) hn
  have hscale := hScale D.n hnScale
  obtain ⟨hs, hT, hH⟩ := hscale
  have hlargeD : (6 : ℝ) ≤ (D.n : ℝ) ^ b := hFan D.n hnFan
  have hselWitness (e : D.CellT) := sel_witness_of_good_heights η₀ β p h D q hGood e
  have hIntSel (c : D.CellT) {ℓ : D.Loc} (hℓ : ℓ ∈ D.intIds q c) :
      ∃ v, v ∈ ordNbrs c.2 ∧ D.sel q (c.1, v) = some ℓ := by
    unfold Ctx.intIds at hℓ
    rcases Finset.mem_biUnion.mp hℓ with ⟨v, hv, hmem⟩
    cases hsel : D.sel q (c.1, v) with
    | none => simp [hsel] at hmem
    | some x =>
        have hx : ℓ = x := by simpa [hsel] using hmem
        subst x
        exact ⟨v, hv, hsel⟩
  have hSelData (e : D.CellT) {ℓ : D.Loc} (hsel : D.sel q e = some ℓ) :
      q.1.2 e.1 ℓ = true ∧
        ℓ.2.val = (hdP η₀ D.n).height Finset.univ (q.1.2 e.1) (q.2.1.2 e.1)
          (D.elig q.1.1 q.1.2 q.2.1.1 e.1) (hdP η₀ D.n).Rlong e.2 ∧
        _root_.hammingDist ℓ.1 e.2 ≤ rH D.n ∧ q.2.1.2 e.1 ℓ = true := by
    obtain ⟨ℓ', hsel', hEligible, hActive⟩ := hselWitness e
    have hEq : ℓ' = ℓ := Option.some.inj (hsel'.symm.trans hsel)
    let j : Fin (HH η₀ D.n + 1) := ⟨
      (hdP η₀ D.n).height Finset.univ (q.1.2 e.1) (q.2.1.2 e.1)
        (D.elig q.1.1 q.1.2 q.2.1.1 e.1) (hdP η₀ D.n).Rlong e.2,
      by
        have hh := ((hGood e.1) e.2 (Finset.mem_univ _)).1
        exact Nat.lt_succ_of_lt hh⟩
    have hEligible' : ℓ ∈ D.elig q.1.1 q.1.2 q.2.1.1 e.1 e.2 j := by
      simpa [j, hEq] using hEligible
    simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and] at hEligible'
    refine ⟨hEligible'.1, ?_, hEligible'.2.2.1, ?_⟩
    · exact congrArg Fin.val hEligible'.2.1
    · simpa [hEq] using hActive
  have hSelNotForbidden (e : D.CellT) {ℓ : D.Loc}
      (hsel : D.sel q e = some ℓ) : ¬ D.Forbidden q.1.1 q.1.2 q.2.1.1 e ℓ := by
    obtain ⟨ℓ', hsel', hEligible, _⟩ := hselWitness e
    have hEq : ℓ' = ℓ := Option.some.inj (hsel'.symm.trans hsel)
    let j : Fin (HH η₀ D.n + 1) := ⟨
      (hdP η₀ D.n).height Finset.univ (q.1.2 e.1) (q.2.1.2 e.1)
        (D.elig q.1.1 q.1.2 q.2.1.1 e.1) (hdP η₀ D.n).Rlong e.2,
      by
        have hh := ((hGood e.1) e.2 (Finset.mem_univ _)).1
        exact Nat.lt_succ_of_lt hh⟩
    have hEligible' : ℓ ∈ D.elig q.1.1 q.1.2 q.2.1.1 e.1 e.2 j := by
      simpa [j, hEq] using hEligible
    simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and] at hEligible'
    exact hEligible'.2.2.2
  have hSelNotForbidden (e : D.CellT) {ℓ : D.Loc}
      (hsel : D.sel q e = some ℓ) : ¬ D.Forbidden q.1.1 q.1.2 q.2.1.1 e ℓ := by
    obtain ⟨ℓ', hsel', hEligible, _⟩ := hselWitness e
    have hEq : ℓ' = ℓ := Option.some.inj (hsel'.symm.trans hsel)
    let j : Fin (HH η₀ D.n + 1) := ⟨
      (hdP η₀ D.n).height Finset.univ (q.1.2 e.1) (q.2.1.2 e.1)
        (D.elig q.1.1 q.1.2 q.2.1.1 e.1) (hdP η₀ D.n).Rlong e.2,
      by
        have hh := ((hGood e.1) e.2 (Finset.mem_univ _)).1
        exact Nat.lt_succ_of_lt hh⟩
    have hEligible' : ℓ ∈ D.elig q.1.1 q.1.2 q.2.1.1 e.1 e.2 j := by
      simpa [j, hEq] using hEligible
    simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and] at hEligible'
    exact hEligible'.2.2.2
  have hFanBound (c : D.CellT) : (D.intIds q c).card ≤ TC η₀ D.n := by
    let ids : Finset D.Loc := D.intIds q c
    let levels : Finset (Fin (HH η₀ D.n + 1)) := ids.image Prod.snd
    let centerHeight := (hdP η₀ D.n).height Finset.univ (q.1.2 c.1) (q.2.1.2 c.1)
      (D.elig q.1.1 q.1.2 q.2.1.1 c.1) (hdP η₀ D.n).Rlong c.2
    let allowed : Finset ℕ := insert (centerHeight - 1)
      (insert centerHeight ({centerHeight + 1} : Finset ℕ))
    have hCenterGH := (hGood c.1) c.2 (Finset.mem_univ _)
    have hLevelsSubset : ∀ j ∈ levels, j.val ∈ allowed := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨ℓ, hℓ, rfl⟩
      obtain ⟨v, hv, hsel⟩ := hIntSel c hℓ
      have hdata := hSelData (c.1, v) hsel
      have hvDist : _root_.hammingDist c.2 v ≤ 2 := by
        have hvDist1 : _root_.hammingDist c.2 v ≤ 1 := by simpa [ordNbrs] using hv
        omega
      have hLip := hCenterGH.2.2 v (Finset.mem_univ _) hvDist
      have hLipLo := (abs_le.mp hLip).1
      have hLipHi := (abs_le.mp hLip).2
      have hvalEq : ℓ.2.val = (hdP η₀ D.n).height Finset.univ (q.1.2 c.1)
          (q.2.1.2 c.1) (D.elig q.1.1 q.1.2 q.2.1.1 c.1)
          (hdP η₀ D.n).Rlong v := hdata.2.1
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hAllowedCard : allowed.card ≤ 3 := by
      dsimp [allowed]
      calc
        (insert (centerHeight - 1) (insert centerHeight ({centerHeight + 1} : Finset ℕ))).card ≤
            (insert centerHeight ({centerHeight + 1} : Finset ℕ)).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({centerHeight + 1} : Finset ℕ).card + 1 + 1 := by
          exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ = 3 := by simp
    let levelVals := levels.image Fin.val
    have hLevelsCard : levels.card ≤ 3 := by
      calc
        levels.card = levelVals.card := by
          dsimp [levelVals]
          symm
          exact Finset.card_image_of_injective levels Fin.val_injective
        _ ≤ allowed.card := by
          apply Finset.card_le_card
          intro j hj
          rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
          exact hLevelsSubset k hk
        _ ≤ 3 := hAllowedCard
    have hIntEq : ids = levels.biUnion fun j => ids.filter fun ℓ => ℓ.2 = j := by
      ext ℓ
      constructor
      · intro hℓ
        apply Finset.mem_biUnion.mpr
        refine ⟨ℓ.2, Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨hℓ, rfl⟩
      · intro hℓ
        rcases Finset.mem_biUnion.mp hℓ with ⟨j, _, hfilter⟩
        exact (Finset.mem_filter.mp hfilter).1
    have hLevelCount (j : Fin (HH η₀ D.n + 1)) (hj : j ∈ levels) :
        (ids.filter fun ℓ => ℓ.2 = j).card ≤ ⌈(D.n : ℝ) ^ b⌉₊ := by
      rcases Finset.mem_image.mp hj with ⟨ℓ₀, hℓ₀, hℓ₀j⟩
      obtain ⟨v₀, hv₀, hsel₀⟩ := hIntSel c hℓ₀
      have hdata₀ := hSelData (c.1, v₀) hsel₀
      have hval₀ : (hdP η₀ D.n).height Finset.univ (q.1.2 c.1) (q.2.1.2 c.1)
          (D.elig q.1.1 q.1.2 q.2.1.1 c.1) (hdP η₀ D.n).Rlong v₀ = j.val := by
        calc
          _ = ℓ₀.2.val := hdata₀.2.1.symm
          _ = j.val := congrArg Fin.val hℓ₀j
      have hGood₀ := (hGood c.1) v₀ (Finset.mem_univ _)
      have hNotBad₀ : ¬ (hdP η₀ D.n).Bad (q.1.2 c.1) (q.2.1.2 c.1)
          (D.elig q.1.1 q.1.2 q.2.1.1 c.1) v₀ j := by
        intro hb
        apply hGood₀.2.1
        refine ⟨Nat.lt_succ_of_lt hGood₀.1, ?_⟩
        simpa [hval₀] using hb
      let crowd := Finset.univ.filter fun u : D.ResT =>
        q.1.2 c.1 (u, j) = true ∧ q.2.1.2 c.1 (u, j) = true ∧
          _root_.hammingDist u v₀ ≤ rH D.n + 2
      have hCrowd : (crowd.card : ℝ) ≤ (D.n : ℝ) ^ b := by
        have hnot : ¬ (D.n : ℝ) ^ b < (crowd.card : ℝ) := by
          intro hlarge'
          apply hNotBad₀
          right
          simpa [crowd, HDParams.Bad, hdP, b] using hlarge'
        exact le_of_not_gt hnot
      have hsubset : (ids.filter fun ℓ => ℓ.2 = j).image Prod.fst ⊆ crowd := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨ℓ, hℓ, rfl⟩
        have hIℓ := Finset.mem_filter.mp hℓ
        obtain ⟨v, hv, hsel⟩ := hIntSel c hIℓ.1
        have hdata := hSelData (c.1, v) hsel
        have hcb : _root_.hammingDist c.2 v ≤ 1 := by simpa [ordNbrs] using hv
        have hcb₀ : _root_.hammingDist c.2 v₀ ≤ 1 := by simpa [ordNbrs] using hv₀
        have hvv₀ : _root_.hammingDist v v₀ ≤ 2 := by
          have hvc : _root_.hammingDist v c.2 ≤ 1 := by
            rw [_root_.hammingDist_comm]
            exact hcb
          exact (_root_.hammingDist_triangle v c.2 v₀).trans (by omega)
        have hpair : (ℓ.1, j) = ℓ := Prod.ext rfl hIℓ.2.symm
        have hP : q.1.2 c.1 (ℓ.1, j) = true := by rw [hpair]; exact hdata.1
        have hA : q.2.1.2 c.1 (ℓ.1, j) = true := by rw [hpair]; exact hdata.2.2.2
        have hdist : _root_.hammingDist ℓ.1 v₀ ≤ rH D.n + 2 := by
          exact (_root_.hammingDist_triangle ℓ.1 v v₀).trans (Nat.add_le_add hdata.2.2.1 hvv₀)
        simp only [crowd, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hP, hA, hdist⟩
      have hinj : Set.InjOn Prod.fst (↑(ids.filter fun ℓ => ℓ.2 = j) : Set D.Loc) := by
        intro ℓ hℓ ℓ' hℓ' hfst
        apply Prod.ext hfst
        exact (Finset.mem_filter.mp hℓ).2.trans (Finset.mem_filter.mp hℓ').2.symm
      have hCardImage : ((ids.filter fun ℓ => ℓ.2 = j).image Prod.fst).card =
          (ids.filter fun ℓ => ℓ.2 = j).card := Finset.card_image_of_injOn hinj
      have hIreal : ((ids.filter fun ℓ => ℓ.2 = j).card : ℝ) ≤ (D.n : ℝ) ^ b := by
        calc
          _ = (((ids.filter fun ℓ => ℓ.2 = j).image Prod.fst).card : ℝ) := by exact_mod_cast hCardImage.symm
          _ ≤ (crowd.card : ℝ) := by exact_mod_cast (Finset.card_le_card hsubset)
          _ ≤ (D.n : ℝ) ^ b := hCrowd
      exact_mod_cast hIreal.trans (Nat.le_ceil ((D.n : ℝ) ^ b))
    have hIntCard : ids.card ≤ 3 * ⌈(D.n : ℝ) ^ b⌉₊ := by
      calc
        ids.card = (levels.biUnion fun j => ids.filter fun ℓ => ℓ.2 = j).card := by
          exact congrArg Finset.card hIntEq
        _ ≤ ∑ j ∈ levels, (ids.filter fun ℓ => ℓ.2 = j).card :=
          Finset.card_biUnion_le (s := levels)
            (t := fun j => ids.filter fun ℓ => ℓ.2 = j)
        _ ≤ ∑ j ∈ levels, ⌈(D.n : ℝ) ^ b⌉₊ := by
          apply Finset.sum_le_sum
          intro j hj
          exact hLevelCount j hj
        _ = levels.card * ⌈(D.n : ℝ) ^ b⌉₊ := by simp [Finset.sum_const]
        _ ≤ 3 * ⌈(D.n : ℝ) ^ b⌉₊ := Nat.mul_le_mul_right _ hLevelsCard
    have hceil : (⌈(D.n : ℝ) ^ b⌉₊ : ℝ) ≤ 2 * (D.n : ℝ) ^ b := by
      have hceil' : (⌈(D.n : ℝ) ^ b⌉₊ : ℝ) < (D.n : ℝ) ^ b + 1 :=
        Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
      linarith [hlargeD]
    have hpowEq : ((D.n : ℝ) ^ b) ^ 2 = (D.n : ℝ) ^ (tau8 η₀ / 8) := by
      rw [← Real.rpow_natCast]
      calc
        ((D.n : ℝ) ^ b) ^ (2 : ℝ) = (D.n : ℝ) ^ (b * 2) :=
          (Real.rpow_mul (by positivity : (0 : ℝ) ≤ (D.n : ℝ)) b 2).symm
        _ = (D.n : ℝ) ^ (tau8 η₀ / 8) := by congr 1 <;> dsimp [b, bH] <;> ring
    have hfanReal : (3 * ⌈(D.n : ℝ) ^ b⌉₊ : ℝ) ≤ (D.n : ℝ) ^ (tau8 η₀ / 8) := by
      calc
        (3 * ⌈(D.n : ℝ) ^ b⌉₊ : ℝ) ≤ 6 * (D.n : ℝ) ^ b := by nlinarith [hceil]
        _ ≤ ((D.n : ℝ) ^ b) ^ 2 := by nlinarith [hlargeD]
        _ = (D.n : ℝ) ^ (tau8 η₀ / 8) := hpowEq
    have hTC : 3 * ⌈(D.n : ℝ) ^ b⌉₊ ≤ TC η₀ D.n := by
      exact_mod_cast (hfanReal.trans (Nat.le_ceil ((D.n : ℝ) ^ (tau8 η₀ / 8))))
    exact hIntCard.trans hTC
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨ℓ, hsel, _, _⟩ := sel_witness_of_good_heights η₀ β p h D q hGood e
    simp [hsel]
  · intro c
    refine ⟨hFanBound c, ?_, ?_, ?_⟩
    · intro e he j
      exact (hPos e.1 e.2 j).2
    · let L : D.LList c.1 := (D.intIds q c, fun u => D.crossId q c u)
      have hCand : D.Cand q.1.2 c L := by
        refine ⟨hFanBound c, ?_, ?_⟩
        · intro ℓ hℓ
          obtain ⟨v, hv, hsel⟩ := hIntSel c hℓ
          have hdata := hSelData (c.1, v) hsel
          exact ⟨hdata.1, v, hv, hdata.2.2.1⟩
        · intro u
          obtain ⟨ℓ, hsel, _, _⟩ := hselWitness (u.1, c.2)
          have hcross : D.crossId q c u = ℓ := by
            simp [Ctx.crossId, hsel]
          have hdata := hSelData (u.1, c.2) hsel
          simpa [L, hcross] using ⟨hdata.1, hdata.2.2.1⟩
      have hCenter : ∃ ℓ, D.sel q (c.1, c.2) = some ℓ := by
        obtain ⟨ℓ, hsel, _, _⟩ := hselWitness (c.1, c.2)
        exact ⟨ℓ, hsel⟩
      obtain ⟨ℓc, hselc⟩ := hCenter
      have hcOrd : c.2 ∈ ordNbrs c.2 := by
        simp [ordNbrs, _root_.hammingDist]
      have hℓcInt : ℓc ∈ D.intIds q c := by
        unfold Ctx.intIds
        apply Finset.mem_biUnion.mpr
        refine ⟨c.2, hcOrd, ?_⟩
        simp [hselc]
      have hSelfId : (c.1, ℓc) ∈ D.listIds c.1 L := by
        simp [Ctx.listIds, L, hℓcInt]
      have hNotBad : ¬ D.BadList q.1.1 q.2.1.1 c L := by
        intro hbad
        have hBadImpliesSource :
            L ∈ (D.listOrder c.1).filter
              (fun X => decide (D.Cand q.1.2 c X ∧ D.BadList q.1.1 q.2.1.1 c X)) := by
          apply List.mem_filter.mpr
          constructor
          · simp [Ctx.listOrder]
          · simp [hCand, hbad]
        have hFamilyHit : ∃ L' ∈ D.family q.1.1 q.1.2 q.2.1.1 c,
            ¬ Disjoint (D.listIds c.1 L) (D.listIds c.1 L') := by
          have hhit := greedy_mem_or_overlap (D.listIds c.1)
            ((D.listOrder c.1).filter
              (fun X => decide (D.Cand q.1.2 c X ∧ D.BadList q.1.1 q.2.1.1 c X))) hBadImpliesSource
          have hhit' : L ∈ D.family q.1.1 q.1.2 q.2.1.1 c ∨
              ∃ L' ∈ D.family q.1.1 q.1.2 q.2.1.1 c,
                ¬ Disjoint (D.listIds c.1 L) (D.listIds c.1 L') := by
            simpa [Ctx.family] using hhit
          rcases hhit' with hLin | hOverlap
          · exact ⟨L, hLin, Finset.not_disjoint_iff.mpr ⟨(c.1, ℓc), hSelfId, hSelfId⟩⟩
          · exact hOverlap
        obtain ⟨L', hL', hnotDisj⟩ := hFamilyHit
        obtain ⟨z, hzL, hzL'⟩ := Finset.not_disjoint_iff.mp hnotDisj
        unfold Ctx.listIds at hzL
        rcases Finset.mem_union.mp hzL with hInternal | hCross
        · rcases Finset.mem_image.mp hInternal with ⟨ℓ, hℓ, heq⟩
          have hkey : z.1 = c.1 := (congrArg Prod.fst heq).symm
          have hloc : z.2 = ℓ := (congrArg Prod.snd heq).symm
          have hzEq : z = (c.1, ℓ) := Prod.ext hkey hloc
          have hID : (c.1, ℓ) ∈ D.listIds c.1 L' := by rw [← hzEq]; exact hzL'
          obtain ⟨v, hv, hsel⟩ := hIntSel c hℓ
          have hdata := hSelData (c.1, v) hsel
          have hForb : D.Forbidden q.1.1 q.1.2 q.2.1.1 (c.1, v) ℓ :=
            ⟨c, Or.inl ⟨rfl, hv⟩, L', hL', hID, hdata.2.2.1⟩
          exact (hSelNotForbidden (c.1, v) hsel) hForb
        · rcases Finset.mem_image.mp hCross with ⟨u, _, heq⟩
          have hkey : z.1 = u.1 := (congrArg Prod.fst heq).symm
          have hselWitness' := hselWitness (u.1, c.2)
          obtain ⟨ℓ, hsel, _, _⟩ := hselWitness'
          have hcross : D.crossId q c u = ℓ := by simp [Ctx.crossId, hsel]
          have hloc : z.2 = ℓ := (congrArg Prod.snd heq).symm.trans hcross
          have hzEq : z = (u.1, ℓ) := Prod.ext hkey hloc
          have hID : (u.1, ℓ) ∈ D.listIds c.1 L' := by rw [← hzEq]; exact hzL'
          have hdata := hSelData (u.1, c.2) hsel
          have hForb : D.Forbidden q.1.1 q.1.2 q.2.1.1 (u.1, c.2) ℓ :=
            ⟨c, Or.inr ⟨rfl, u.2⟩, L', hL', hID, hdata.2.2.1⟩
          exact (hSelNotForbidden (u.1, c.2) hsel) hForb
      have hqBound : D.qL q.1.1 c.1
          (D.listInt q.2.1.1 c.1 L) (D.listCrossTag q.2.1.1 c.1 L) ≤
          Real.sqrt (Real.sqrt D.eps0) := by
        have hb := hNotBad
        unfold Ctx.BadList at hb
        exact le_of_not_gt hb
      change D.qL q.1.1 c.1 (D.listInt q.2.1.1 c.1 L)
        (D.listCrossTag q.2.1.1 c.1 L) ≤ Real.sqrt (Real.sqrt D.eps0)
      exact hqBound
    · change (hdP η₀ D.n).Legal (q.1.2 c.1) (D.elig q.1.1 q.1.2 q.2.1.1 c.1)
        ((hdP η₀ D.n).domBall Finset.univ c.2 (hdP η₀ D.n).Rlong)
      intro v hv j
      exact hLegal q.1.1 q.1.2 q.2.1.1 hPos hFew c.1 v j

/-- L8.1f(vi) (08:216–225): the selection at `(t, b)` consults eligibility in slice `t` at sites within `4H`
(the long rule), whose forbidden IDs come from the families at incident odd cells (keys within one of `t`), whose
lists read positions and tags of IDs within `r + 2` of those sites in slices within one of those keys, and `q_L`
reads hidden tuples within two of those keys; activations and ties are read only in slice `t`. -/
theorem sel_local (D : Ctx η₀ β p h) : D.SelLocal := by
  intro q q' e hΘ hLoc hAT
  let E := D.elig q.1.1 q.1.2 q.2.1.1 e.1
  let E' := D.elig q'.1.1 q'.1.2 q'.2.1.1 e.1
  unfold Ctx.sel
  apply selection_eq_of_local_data (hdP η₀ D.n) Finset.univ
    (q.1.2 e.1) (q'.1.2 e.1) (q.2.1.2 e.1) (q'.2.1.2 e.1)
    E E' (q.2.2 e.1) (q'.2.2 e.1) e.2 (Finset.mem_univ _)
  · intro v hv hdist
    have hsite : _root_.hammingDist v e.2 ≤ 4 * HH η₀ D.n := by
      simpa [HDParams.Rlong, hdP] using hdist
    have hp : ∀ k ∈ keyBall e.1 2, ∀ ℓ : D.Loc,
        _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
          q.1.2 k ℓ = q'.1.2 k ℓ := by
      intro k hk ℓ hℓ
      exact (hLoc k hk ℓ hℓ).1
    have ht : ∀ k ∈ keyBall e.1 2, ∀ ℓ : D.Loc,
        _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
          q.2.1.1 k ℓ = q'.2.1.1 k ℓ := by
      intro k hk ℓ hℓ
      exact (hLoc k hk ℓ hℓ).2
    have hE := elig_eq_of_local_inputs D q.1.1 q'.1.1 q.1.2 q'.1.2
      q.2.1.1 q'.2.1.1 e.1 v e.2 hsite hΘ hp ht
    funext j
    exact hE j
  · intro v hv j ℓ hℓ
    change ℓ ∈ D.elig q.1.1 q.1.2 q.2.1.1 e.1 v j at hℓ
    simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    rcases hℓ with ⟨_, _, hdist, _⟩
    exact hdist
  · intro ℓ hℓ
    have hkey : e.1 ∈ keyBall e.1 2 := by
      simp only [keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [keyDist]
    have hbound : _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
      have hbound' : _root_.hammingDist ℓ.1 e.2 ≤ 4 * HH η₀ D.n + rH D.n + 2 := by
        simpa [HDParams.Rlong, hdP] using hℓ
      omega
    exact (hLoc e.1 hkey ℓ hbound).1
  · intro ℓ hℓ
    have hbound : _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
      have hbound' : _root_.hammingDist ℓ.1 e.2 ≤ 4 * HH η₀ D.n + rH D.n + 2 := by
        simpa [HDParams.Rlong, hdP] using hℓ
      omega
    exact (hAT ℓ hbound).1
  · intro j
    exact (hAT (e.2, j) (by simp)).2

/-- L8.1f(vii) (08:211): prospective ball counts lie in `[λ/2, 2λ]` everywhere except with probability at most
`(ℓ+1)^s · 2 · 2^{n-m} (H+1) e^{-λ/12} ≤ e^{-n}` (`height_position_counts` in every slice). -/
theorem pos_tail (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n →
      D.preLaw.pr (fun q => ¬ D.PosOK q.1.2) ≤ Real.exp (-(D.n : ℝ)) := by
  obtain ⟨hσpos, hσζ, hζ1, _, _⟩ := (hd_admissible η₀ hη₀).hsz
  have hζpos : 0 < zetaH η₀ := lt_trans hσpos hσζ
  have hσ1 : sigmaH η₀ < 1 := lt_trans hσζ hζ1
  let a : ℝ := 1 - zetaH η₀
  have ha : 0 < a := by dsimp [a]; linarith
  let cVol : ℝ := (6 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ)
  have hpowTendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (10 : ℝ))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 10)).comp
      tendsto_natCast_atTop_atTop
  have hVolEventually : ∀ᶠ n : ℕ in Filter.atTop, cVol ≤ (n : ℝ) ^ (10 : ℝ) :=
    hpowTendsto.eventually (Filter.eventually_ge_atTop cVol)
  obtain ⟨nVol, hVol⟩ := Filter.eventually_atTop.1 hVolEventually
  let cLog : ℝ := ((4 / a) ^ 2)
  have hlogTendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (a / 2))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : (0 : ℝ) < a / 2)).comp
      tendsto_natCast_atTop_atTop
  have hLogEventually : ∀ᶠ n : ℕ in Filter.atTop, cLog ≤ (n : ℝ) ^ (a / 2) :=
    hlogTendsto.eventually (Filter.eventually_ge_atTop cLog)
  obtain ⟨nLog, hLog⟩ := Filter.eventually_atTop.1 hLogEventually
  refine ⟨max 8000 (max nVol nLog), ?_⟩
  intro D hn hGF
  have hn8000 : 8000 ≤ D.n := by omega
  have hnVol : nVol ≤ D.n := by omega
  have hnLog : nLog ≤ D.n := by omega
  have hn1 : 1 ≤ D.n := le_trans (by decide : 1 ≤ 8000) hn8000
  have hn2 : 2 ≤ D.n := by omega
  have hnR : (1 : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast hn1
  have hnR2 : (2 : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast hn2
  have hpowD : cVol ≤ (D.n : ℝ) ^ (10 : ℝ) := hVol D.n hnVol
  have hlogPow : cLog ≤ (D.n : ℝ) ^ (a / 2) := hLog D.n hnLog
  have hlogNonneg : 0 ≤ Real.log (D.n : ℝ) := Real.log_nonneg hnR
  have hlogBound : Real.log (D.n : ℝ) ≤
      ((D.n : ℝ) ^ (a / 4)) / (a / 4) :=
    Real.log_natCast_le_rpow_div D.n (by linarith)
  have hlogSq : (Real.log (D.n : ℝ)) ^ 2 ≤ (D.n : ℝ) ^ a := by
    have hsq : (Real.log (D.n : ℝ)) ^ 2 ≤
        (((D.n : ℝ) ^ (a / 4)) / (a / 4)) ^ 2 :=
          (sq_le_sq₀ hlogNonneg (by positivity)).2 hlogBound
    calc
      (Real.log (D.n : ℝ)) ^ 2 ≤
          (((D.n : ℝ) ^ (a / 4)) / (a / 4)) ^ 2 := hsq
      _ = cLog * (D.n : ℝ) ^ (a / 2) := by
        dsimp [cLog]
        calc
          (((D.n : ℝ) ^ (a / 4)) / (a / 4)) ^ 2 =
              ((D.n : ℝ) ^ (a / 4)) ^ 2 / (a / 4) ^ 2 := by rw [div_pow]
          _ = ((4 / a) ^ 2) * (D.n : ℝ) ^ (a / 2) := by
            have hpow : ((D.n : ℝ) ^ (a / 4)) ^ 2 = (D.n : ℝ) ^ (a / 2) := by
              calc
                ((D.n : ℝ) ^ (a / 4)) ^ 2 =
                    ((D.n : ℝ) ^ (a / 4)) ^ (2 : ℝ) :=
                      (Real.rpow_natCast ((D.n : ℝ) ^ (a / 4)) 2).symm
                _ = (D.n : ℝ) ^ ((a / 4) * 2) :=
                      (Real.rpow_mul (x := (D.n : ℝ)) (by positivity) (a / 4) 2).symm
                _ = (D.n : ℝ) ^ (a / 2) := by congr 1 <;> ring
            rw [hpow]
            have heps : (a / 4) ≠ 0 := ne_of_gt (by linarith)
            field_simp [heps]
      _ ≤ (D.n : ℝ) ^ (a / 2) * (D.n : ℝ) ^ (a / 2) :=
        mul_le_mul_of_nonneg_right hlogPow (Real.rpow_nonneg (by positivity) _)
      _ = (D.n : ℝ) ^ a := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < (D.n : ℝ))]
        congr 1 <;> ring
  have hceilLog :
      ⌈Real.log (D.n : ℝ) ^ 2⌉₊ ≤ ⌈(D.n : ℝ) ^ a⌉₊ :=
    Nat.ceil_le.mpr (hlogSq.trans (Nat.le_ceil ((D.n : ℝ) ^ a)))
  have hpowOne : (1 : ℝ) ≤ (D.n : ℝ) ^ a :=
    Real.one_le_rpow hnR (by linarith)
  have hceilOne : 1 ≤ ⌈(D.n : ℝ) ^ a⌉₊ := by
    exact_mod_cast (le_trans hpowOne (Nat.le_ceil ((D.n : ℝ) ^ a)))
  have hR0 : max 1 ⌈Real.log (D.n : ℝ) ^ 2⌉₊ ≤ ⌈(D.n : ℝ) ^ a⌉₊ :=
    max_le hceilOne hceilLog
  have htop := topScale_le_mul_target (D.n) (sigmaH η₀) (zetaH η₀)
    (by simpa [a] using hR0)
  have hpowσ : (D.n : ℝ) ^ sigmaH η₀ ≤ (D.n : ℝ) :=
    by simpa using Real.rpow_le_rpow_of_exponent_le hnR hσ1.le
  have hpowTarget : (D.n : ℝ) ^ a ≤ (D.n : ℝ) :=
    calc
      (D.n : ℝ) ^ a ≤ (D.n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by dsimp [a]; linarith [hζpos])
      _ = (D.n : ℝ) := Real.rpow_one _
  have hceilσ : ⌈(D.n : ℝ) ^ sigmaH η₀⌉₊ ≤ D.n := Nat.ceil_le.mpr hpowσ
  have hceilTarget : ⌈(D.n : ℝ) ^ a⌉₊ ≤ D.n := Nat.ceil_le.mpr hpowTarget
  have hM : max 2 ⌈(D.n : ℝ) ^ sigmaH η₀⌉₊ ≤ D.n := max_le (by omega) hceilσ
  have hHH : HH η₀ D.n ≤ D.n ^ 2 := by
    dsimp [HH]
    calc
      topScale D.n (sigmaH η₀) (zetaH η₀) ≤
          (max 2 ⌈(D.n : ℝ) ^ sigmaH η₀⌉₊) * ⌈(D.n : ℝ) ^ a⌉₊ := by
            simpa [a] using htop
      _ ≤ D.n * D.n := Nat.mul_le_mul hM hceilTarget
      _ = D.n ^ 2 := by ring
  have hHplus : (HH η₀ D.n + 1 : ℝ) ≤ 2 * (D.n : ℝ) ^ 2 := by
    have hNat : HH η₀ D.n + 1 ≤ 2 * D.n ^ 2 := by
      have hH' : HH η₀ D.n + 1 ≤ D.n ^ 2 + 1 := Nat.add_le_add_right hHH 1
      have hsq : 1 ≤ D.n ^ 2 := Nat.one_le_pow 2 D.n hn1
      omega
    exact_mod_cast hNat
  let pH := hdP η₀ D.n
  have hdimLow : (1 / 2 : ℝ) * (D.n : ℝ) ≤ (dC η₀ D.n : ℝ) := hGF.hd_ok.2.1
  have hdimHigh : (dC η₀ D.n : ℝ) ≤ (1 : ℝ) * D.n := hGF.hd_ok.2.2
  have hsplit := hGF.split
  have hmle : mC η₀ D.n ≤ D.n := by omega
  have hnR8000 : (8000 : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast hn8000
  have hd40 : 40 ≤ dC η₀ D.n := by
    have hr : (40 : ℝ) ≤ (dC η₀ D.n : ℝ) := by nlinarith [hdimLow, hnR8000]
    exact_mod_cast hr
  have hlinear : (1 / 200 : ℝ) * (dC η₀ D.n : ℝ) ≤ (rH D.n : ℝ) := by
    simpa [hdRegime, HDRegime.ok] using hGF.hd_ok.1.1
  have hr20 : 20 ≤ rH D.n := by
    have hr : (20 : ℝ) ≤ (rH D.n : ℝ) := by nlinarith [hlinear, hdimLow, hnR8000]
    exact_mod_cast hr
  have hchoose := choose20_lower hd40
  have hchooseLower :
      ((D.n : ℝ) / 6) ^ 20 / (Nat.factorial 20 : ℝ) ≤
        (Nat.choose (dC η₀ D.n) 20 : ℝ) := by
    have hbase : (D.n : ℝ) / 6 ≤ (dC η₀ D.n : ℝ) / 3 := by nlinarith [hdimLow]
    calc
      ((D.n : ℝ) / 6) ^ 20 / (Nat.factorial 20 : ℝ) ≤
          ((dC η₀ D.n : ℝ) / 3) ^ 20 / (Nat.factorial 20 : ℝ) := by
            exact div_le_div_of_nonneg_right
              (pow_le_pow_left₀ (by positivity) hbase 20) (by positivity)
      _ ≤ (Nat.choose (dC η₀ D.n) 20 : ℝ) := by
        convert hchoose using 1 <;> field_simp <;> ring
  have hpowLower : (D.n : ℝ) ^ (10 : ℝ) ≤
      ((D.n : ℝ) / 6) ^ 20 / (Nat.factorial 20 : ℝ) := by
    have hmul : (D.n : ℝ) ^ (10 : ℝ) * cVol ≤ (D.n : ℝ) ^ (20 : ℝ) := by
      calc
        (D.n : ℝ) ^ (10 : ℝ) * cVol ≤
            (D.n : ℝ) ^ (10 : ℝ) * (D.n : ℝ) ^ (10 : ℝ) :=
              mul_le_mul_of_nonneg_left hpowD (Real.rpow_nonneg (by positivity) _)
        _ = (D.n : ℝ) ^ (20 : ℝ) := by
              rw [← Real.rpow_add (by positivity : (0 : ℝ) < (D.n : ℝ))]
              congr 1 <;> ring
    have heq : ((D.n : ℝ) / 6) ^ 20 / (Nat.factorial 20 : ℝ) =
        (D.n : ℝ) ^ (20 : ℝ) / cVol := by
      dsimp [cVol]
      rw [div_pow]
      field_simp
      exact (Real.rpow_natCast (D.n : ℝ) 20).symm
    rw [heq]
    exact (le_div_iff₀ (by positivity : 0 < cVol)).2 (by simpa [mul_comm] using hmul)
  have hVlower : (D.n : ℝ) ^ (10 : ℝ) ≤ (pH.V : ℝ) := by
    have hsum : (Nat.choose (dC η₀ D.n) 20 : ℝ) ≤
        ∑ j ∈ Finset.range (rH D.n + 1), (Nat.choose (dC η₀ D.n) j : ℝ) := by
      calc
        (Nat.choose (dC η₀ D.n) 20 : ℝ) =
            ∑ j ∈ ({20} : Finset ℕ), (Nat.choose (dC η₀ D.n) j : ℝ) := by simp
        _ ≤ ∑ j ∈ Finset.range (rH D.n + 1),
            (Nat.choose (dC η₀ D.n) j : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.singleton_subset_iff.mpr
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hr20)))
            (by intro j hj hnot; positivity)
    calc
      _ ≤ (Nat.choose (dC η₀ D.n) 20 : ℝ) := hpowLower.trans hchooseLower
      _ ≤ _ := hsum
      _ = (pH.V : ℝ) := by simp [pH, HDParams.V, hdP]
  have hVNat : 0 < pH.V := by
    have hnpositive : (0 : ℝ) < (D.n : ℝ) ^ (10 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < D.n)) _
    exact_mod_cast lt_of_lt_of_le hnpositive hVlower
  have hVReal : (0 : ℝ) < (pH.V : ℝ) := by exact_mod_cast hVNat
  have hlam : 0 < pH.lam := by simp [pH, hdP]; positivity
  have hprob : pH.lam / (pH.V : ℝ) ≤ 1 := by
    apply (div_le_one hVReal).2
    simpa [pH, hdP] using hVlower
  have hr : pH.r ≤ pH.d := by
    have hr4 : 4 * rH D.n ≤ dC η₀ D.n := by
      simpa [hdRegime, HDRegime.ok] using hGF.hd_ok.1.2
    dsimp [pH, hdP]
    omega
  let SliceBad : (pH.Loc → Bool) → Prop := fun P =>
    ∃ b : CubeVertex pH.d, ∃ j : Fin (pH.H + 1),
      let count := (Finset.univ.filter fun u : CubeVertex pH.d =>
        P (u, j) = true ∧ _root_.hammingDist u b ≤ pH.r).card
      (count : ℝ) < pH.lam / 2 ∨ 2 * pH.lam < (count : ℝ)
  have hSliceTail : pH.posLaw.pr SliceBad ≤
      2 * ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) *
        ((pH.H + 1 : ℕ) : ℝ) * Real.exp (-pH.lam / 12) := by
    have hcounts := _root_.HypercubeRamsey.height_position_counts pH
      (Finset.univ : Finset (CubeVertex pH.d)) hlam hVNat hr hprob
    simpa [SliceBad] using hcounts
  have hMarg (g : D.KeyT) :
      D.posLaw.pr (fun P => SliceBad (P g)) = pH.posLaw.pr SliceBad := by
    calc
      D.posLaw.pr (fun P => SliceBad (P g)) =
          D.posLaw.expect (prIndicator (fun P => SliceBad (P g))) :=
            pr_eq_expect_indicator D.posLaw (fun P => SliceBad (P g))
      _ = pH.posLaw.expect (prIndicator SliceBad) := by
            calc
              D.posLaw.expect (prIndicator (fun P => SliceBad (P g))) =
                  D.posLaw.expect (fun P => prIndicator SliceBad (P g)) := by
                    congr 1
              _ = pH.posLaw.expect (prIndicator SliceBad) := by
                    simpa [Ctx.posLaw, pH] using
                      pi_expect_coordinate pH.posLaw g (prIndicator SliceBad)
      _ = pH.posLaw.pr SliceBad := (pr_eq_expect_indicator pH.posLaw SliceBad).symm
  have hEvent (P : D.Pos) : ¬ D.PosOK P ↔ ∃ g, SliceBad (P g) := by
    unfold Ctx.PosOK
    constructor
    · intro h
      push_neg at h
      rcases h with ⟨g, b, j, hfail⟩
      refine ⟨g, b, j, ?_⟩
      dsimp [SliceBad]
      by_cases hlow : pH.lam / 2 ≤ (D.ballCount P g b j : ℝ)
      · right
        simpa [Ctx.ballCount, pH] using hfail hlow
      · left
        simpa [Ctx.ballCount, pH] using (lt_of_not_ge hlow)
    · rintro ⟨g, b, j, hfail⟩ hOK
      have hAt := hOK g b j
      dsimp [SliceBad] at hfail
      rcases hfail with hlow | hhigh
      · have hlow' : (D.ballCount P g b j : ℝ) < pH.lam / 2 := by
          simpa [Ctx.ballCount, pH] using hlow
        exact (not_lt_of_ge hAt.1) hlow'
      · have hhigh' : 2 * pH.lam < (D.ballCount P g b j : ℝ) := by
          simpa [Ctx.ballCount, pH] using hhigh
        exact (not_lt_of_ge hAt.2) hhigh'
  have hUnion : D.posLaw.pr (fun P => ¬ D.PosOK P) ≤
      (Fintype.card D.KeyT : ℝ) *
        (2 * ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) *
          ((pH.H + 1 : ℕ) : ℝ) * Real.exp (-pH.lam / 12)) := by
    have heq : (fun P => ¬ D.PosOK P) = (fun P => ∃ g, SliceBad (P g)) := by
      funext P
      exact propext (hEvent P)
    rw [heq]
    calc
      _ ≤ ∑ g : D.KeyT, D.posLaw.pr (fun P => SliceBad (P g)) :=
        pr_exists_le_sum D.posLaw (fun g P => SliceBad (P g))
      _ ≤ ∑ _g : D.KeyT,
          2 * ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) *
            ((pH.H + 1 : ℕ) : ℝ) * Real.exp (-pH.lam / 12) :=
            Finset.sum_le_sum fun g hg => by
              calc
                D.posLaw.pr (fun P => SliceBad (P g)) = pH.posLaw.pr SliceBad := hMarg g
                _ ≤ _ := hSliceTail
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hPrePos : D.preLaw.pr (fun q => ¬ D.PosOK q.1.2) =
      D.posLaw.pr (fun P => ¬ D.PosOK P) := by
    calc
      _ = D.preLaw.expect (fun q => prIndicator (fun q => ¬ D.PosOK q.1.2) q) :=
        pr_eq_expect_indicator D.preLaw (fun q => ¬ D.PosOK q.1.2)
      _ = D.posLaw.expect (prIndicator (fun P => ¬ D.PosOK P)) :=
        preLaw_expect_pos D (prIndicator (fun P => ¬ D.PosOK P))
      _ = _ := (pr_eq_expect_indicator D.posLaw (fun P => ¬ D.PosOK P)).symm
  have hKeyCard : (Fintype.card D.KeyT : ℝ) ≤ (2 : ℝ) ^ D.n := by
    have hCard : Fintype.card D.KeyT = (lC D.n + 1) ^ sC η₀ D.n := by
      simp [Ctx.KeyT, Key]
    have hl : lC D.n + 1 ≤ 2 ^ lC D.n := by
      simpa using Nat.choose_succ_le_two_pow (lC D.n) 1
    have hNat : Fintype.card D.KeyT ≤ 2 ^ D.n := by
      rw [hCard]
      calc
        (lC D.n + 1) ^ sC η₀ D.n ≤ (2 ^ lC D.n) ^ sC η₀ D.n :=
          Nat.pow_le_pow_left hl _
        _ = 2 ^ (lC D.n * sC η₀ D.n) := by rw [Nat.pow_mul]
        _ = 2 ^ mC η₀ D.n := by simp [mC, Nat.mul_comm]
        _ ≤ 2 ^ D.n := Nat.pow_le_pow_right (by decide) hmle
    exact_mod_cast hNat
  have hSiteCard :
      ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) ≤ (2 : ℝ) ^ D.n := by
    have hdimNat : dC η₀ D.n ≤ D.n := by
      unfold dC
      omega
    have hcard : Fintype.card (CubeVertex pH.d) = 2 ^ pH.d := by
      simp [CubeVertex, Fintype.card_fun]
    have hNat : Fintype.card (CubeVertex pH.d) ≤ 2 ^ D.n := by
      rw [hcard]
      exact Nat.pow_le_pow_right (by decide) (by simpa [pH, hdP] using hdimNat)
    exact_mod_cast (by simpa using hNat)
  have hHplus : ((pH.H + 1 : ℕ) : ℝ) ≤ 2 * (D.n : ℝ) ^ 2 := by
    have hNat : pH.H + 1 ≤ 2 * D.n ^ 2 := by
      change HH η₀ D.n + 1 ≤ 2 * D.n ^ 2
      have hH' : HH η₀ D.n + 1 ≤ D.n ^ 2 + 1 := Nat.add_le_add_right hHH 1
      have hsq : 1 ≤ D.n ^ 2 := Nat.one_le_pow 2 D.n hn1
      omega
    exact_mod_cast hNat
  have hExpoPref :
      (Fintype.card D.KeyT : ℝ) *
        (2 * ((Finset.univ : Finset (CubeVertex pH.d)).card : ℝ) *
          ((pH.H + 1 : ℕ) : ℝ) * Real.exp (-pH.lam / 12)) ≤
        4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 * Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) := by
    have hLam : pH.lam = (D.n : ℝ) ^ (10 : ℝ) := by rfl
    have hpow4 : (2 : ℝ) ^ D.n * (2 : ℝ) ^ D.n = (4 : ℝ) ^ D.n := by
      calc
        (2 : ℝ) ^ D.n * (2 : ℝ) ^ D.n = ((2 : ℝ) * 2) ^ D.n := by rw [← mul_pow]
        _ = (4 : ℝ) ^ D.n := by norm_num
    rw [hLam]
    calc
      _ ≤ (2 : ℝ) ^ D.n *
          (2 * (2 : ℝ) ^ D.n * (2 * (D.n : ℝ) ^ 2) *
            Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12)) := by
              gcongr <;> positivity
      _ = _ := by
        calc
          (2 : ℝ) ^ D.n *
              (2 * (2 : ℝ) ^ D.n * (2 * (D.n : ℝ) ^ 2) *
                Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12)) =
              4 * ((2 : ℝ) ^ D.n * (2 : ℝ) ^ D.n) * (D.n : ℝ) ^ 2 *
                Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) := by ring
          _ = 4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 *
                Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) := by rw [hpow4]
  have hExpOne : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hExpTwo : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) hExpOne 2
      _ = Real.exp 1 * Real.exp 1 := by ring
      _ = Real.exp (1 + 1) := (Real.exp_add 1 1).symm
      _ = Real.exp 2 := by congr 1; norm_num
  have hExpNat : ∀ (x : ℝ) (k : ℕ), Real.exp x ^ k = Real.exp ((k : ℝ) * x) := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          Real.exp x ^ (k + 1) = Real.exp x ^ k * Real.exp x := by rw [pow_succ]
          _ = Real.exp ((k : ℝ) * x) * Real.exp x := by rw [ih]
          _ = Real.exp ((k : ℝ) * x + x) := (Real.exp_add _ _).symm
          _ = Real.exp (((k + 1 : ℕ) : ℝ) * x) := by
            congr 1
            norm_num [Nat.cast_succ]
            ring
  have hFourPow : (4 : ℝ) ^ D.n ≤ Real.exp (2 * D.n) := by
    calc
      (4 : ℝ) ^ D.n ≤ (Real.exp 2) ^ D.n := pow_le_pow_left₀ (by norm_num) hExpTwo _
      _ = Real.exp (2 * (D.n : ℝ)) := by simpa [mul_comm] using hExpNat 2 D.n
  have hNExp : (D.n : ℝ) ^ 2 ≤ Real.exp (2 * D.n) := by
    have hNle : (D.n : ℝ) ≤ Real.exp (D.n : ℝ) := by
      have h := Real.add_one_le_exp (D.n : ℝ)
      linarith
    calc
      (D.n : ℝ) ^ 2 ≤ (Real.exp (D.n : ℝ)) ^ 2 := by gcongr
      _ = Real.exp (2 * (D.n : ℝ)) := by
        calc
          (Real.exp (D.n : ℝ)) ^ 2 = Real.exp (D.n : ℝ) * Real.exp (D.n : ℝ) := by ring
          _ = Real.exp ((D.n : ℝ) + D.n) := (Real.exp_add _ _).symm
          _ = Real.exp (2 * (D.n : ℝ)) := by congr 1 <;> ring
  have hPrefExp : 4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 ≤ Real.exp (4 * D.n + 2) := by
    calc
      4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 ≤
          Real.exp 2 * Real.exp (2 * D.n) * Real.exp (2 * D.n) := by
            gcongr
      _ = (Real.exp 2 * Real.exp (2 * D.n)) * Real.exp (2 * D.n) := by ring
      _ = Real.exp (2 + 2 * D.n) * Real.exp (2 * D.n) := by
        rw [(Real.exp_add 2 (2 * D.n)).symm]
      _ = Real.exp ((2 + 2 * D.n) + 2 * D.n) := (Real.exp_add _ _).symm
      _ = Real.exp (4 * D.n + 2) := by congr 1 <;> ring
  have hn10 : 5 * (D.n : ℝ) + 2 ≤ (D.n : ℝ) ^ (10 : ℝ) / 12 := by
    have hnNat : 10 ≤ D.n := by omega
    have hpowNat : (10 : ℕ) ^ 9 ≤ D.n ^ 9 := Nat.pow_le_pow_left hnNat _
    have hpow9 : (72 : ℝ) ≤ (D.n : ℝ) ^ (9 : ℕ) := by
      have hcast : (10 : ℝ) ^ (9 : ℕ) ≤ (D.n : ℝ) ^ (9 : ℕ) := by exact_mod_cast hpowNat
      have hten : (72 : ℝ) ≤ (10 : ℝ) ^ (9 : ℕ) := by norm_num
      exact hten.trans hcast
    have hnreal : (0 : ℝ) ≤ (D.n : ℝ) := by positivity
    have hpow10 : 72 * (D.n : ℝ) ≤ (D.n : ℝ) ^ (10 : ℝ) := by
      have hpow10Nat : 72 * (D.n : ℝ) ≤ (D.n : ℝ) ^ (10 : ℕ) := by
        calc
          72 * (D.n : ℝ) ≤ (D.n : ℝ) ^ (9 : ℕ) * (D.n : ℝ) :=
            mul_le_mul_of_nonneg_right hpow9 hnreal
          _ = (D.n : ℝ) ^ (10 : ℕ) := by
            rw [show (10 : ℕ) = 9 + 1 by norm_num]
            exact (pow_succ (D.n : ℝ) 9).symm
      calc
        72 * (D.n : ℝ) ≤ (D.n : ℝ) ^ (10 : ℕ) := hpow10Nat
        _ = (D.n : ℝ) ^ (10 : ℝ) := (Real.rpow_natCast (D.n : ℝ) 10).symm
    have hmul : 12 * (5 * (D.n : ℝ) + 2) ≤ 72 * (D.n : ℝ) := by nlinarith [hnR2]
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 12)).2
      (by simpa [mul_comm] using hmul.trans hpow10)
  have hExpAbsorb : 4 * D.n + 2 - (D.n : ℝ) ^ (10 : ℝ) / 12 ≤ -(D.n : ℝ) := by
    linarith [hn10]
  have hFinal :
      4 * (4 : ℝ) ^ D.n * (D.n : ℝ) ^ 2 *
          Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) ≤ Real.exp (-(D.n : ℝ)) := by
    calc
      _ ≤ Real.exp (4 * D.n + 2) *
          Real.exp (-((D.n : ℝ) ^ (10 : ℝ)) / 12) :=
            mul_le_mul_of_nonneg_right hPrefExp (Real.exp_nonneg _)
      _ = Real.exp (4 * D.n + 2 - (D.n : ℝ) ^ (10 : ℝ) / 12) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      _ ≤ Real.exp (-(D.n : ℝ)) := Real.exp_le_exp.mpr hExpAbsorb
  exact hPrePos ▸ hUnion.trans (hExpoPref.trans hFinal)

/-- L8.1f(viii) (08:191–195): the tags of a candidate list's distinct IDs are independent with laws `S_g`
(internal) and `S_u` (cross), so `E_t q_L = q_{g,k}` with `k ≤ T` internal IDs (`Mden` does not depend on how the
internal observations are indexed); at a hidden history avoiding the hidden events `q_{g,k} ≤ ε₀^{1/2}`, and
Markov gives `Pr(q_L > ε₀^{1/4}) ≤ ε₀^{1/4}`. -/
theorem bad_list_prob (D : Ctx η₀ β p h) : D.BadListProb := by
  classical
  intro Θ hΘ P c L hCand
  let δ := Real.sqrt (Real.sqrt D.eps0)
  let f : D.Tags → ℝ := fun t => D.qL Θ c.1 (D.listInt t c.1 L) (D.listCrossTag t c.1 L)
  have hNoBad (g : D.KeyT) :
      ¬ (¬ D.BaseGates Θ g ∨ ∃ k ≤ TC η₀ D.n, Real.sqrt D.eps0 < D.qgk Θ g k) := by
    simpa [Ctx.HBad] using hΘ g
  have hqgk (k : ℕ) (hk : k ≤ TC η₀ D.n) :
      D.qgk Θ c.1 k ≤ Real.sqrt D.eps0 := by
    by_contra hlarge
    apply hNoBad c.1
    exact Or.inr ⟨k, hk, lt_of_not_ge hlarge⟩
  have hExpIdentity : (D.tagLawAll Θ).expect f = D.qgk Θ c.1 L.1.card := by
    /- Reindex the internal tag coordinates by `Fin L.1.card`; this also needs the permutation invariance of `Mden`. -/
    sorry
  have hfNonneg : ∀ t, 0 ≤ f t := by
    intro t
    dsimp [f]
    unfold Ctx.qL
    apply Finset.sum_nonneg
    intro x hx
    apply mul_nonneg
    · apply mul_nonneg
      · exact ind_nonneg _
      · apply Finset.prod_nonneg
        intro u hu
        exact (D.anchorU Θ u.1 (D.listCrossTag t c.1 L u)).nonneg (x u)
    · exact ind_nonneg _
  have heps : 0 < D.eps0 := by
    unfold Ctx.eps0
    exact Real.exp_pos _
  have hδ : 0 < δ := Real.sqrt_pos.2 (Real.sqrt_pos.2 heps)
  have hqLavg : (D.tagLawAll Θ).expect f ≤ Real.sqrt D.eps0 := by
    rw [hExpIdentity]
    exact hqgk L.1.card hCand.1
  have hprobSub : (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c L) ≤
      (D.tagLawAll Θ).pr (fun t => δ ≤ f t) := by
    have hpoint (t : D.Tags) :
        (if D.BadList Θ t c L then (D.tagLawAll Θ).w t else 0) ≤
          (if δ ≤ f t then (D.tagLawAll Θ).w t else 0) := by
      by_cases hbad : D.BadList Θ t c L
      · have hlarge : δ < f t := by simpa [Ctx.BadList, δ, f] using hbad
        have hle : δ ≤ f t := le_of_lt hlarge
        simp [hbad, hle]
      · by_cases hle : δ ≤ f t
        · simp [hbad, hle, (D.tagLawAll Θ).nonneg t]
        · simp [hbad, hle]
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro t ht
    exact hpoint t
  have hmarkov := FinProb.markov (D.tagLawAll Θ) f δ hfNonneg hδ
  have hδsq : δ ^ 2 = Real.sqrt D.eps0 := by
    dsimp [δ]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have htail : (D.tagLawAll Θ).expect f / δ ≤ δ := by
    apply (div_le_iff₀ hδ).2
    calc
      (D.tagLawAll Θ).expect f ≤ Real.sqrt D.eps0 := hqLavg
      _ = δ * δ := by rw [← hδsq]; ring
  calc
    (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c L) ≤
        (D.tagLawAll Θ).pr (fun t => δ ≤ f t) := hprobSub
    _ ≤ (D.tagLawAll Θ).expect f / δ := hmarkov
    _ ≤ δ := htail

/-- L8.1f(ix) (08:200–206): lists with disjoint ID sets have independent tags, so `n` disjoint bad lists at a cell
have probability at most `L_n^n ε₀^{n/4} = exp(n[25(s+T) - δhs/4] log n)` (`BadListProb`, `ListCount`), which for
`h ≥ 10⁸` beats the `exp(O(n + s log n))` cells. -/
private theorem bad_family_witness (D : Ctx η₀ β p h) (Θ : D.Hist) (P : D.Pos) (t : D.Tags)
    (hnotfew : ¬ D.FewBad Θ P t) :
    ∃ c : D.CellT, D.n ≤ (D.family Θ P t c).length ∧
      (∀ L ∈ D.family Θ P t c, D.Cand P c L ∧ D.BadList Θ t c L) ∧
      (D.family Θ P t c).Pairwise (fun L L' => Disjoint (D.listIds c.1 L) (D.listIds c.1 L')) := by
  classical
  have hnot : ¬ ∀ c : D.CellT, (D.family Θ P t c).length < D.n := by
    simpa [Ctx.FewBad] using hnotfew
  obtain ⟨c, hc⟩ := not_forall.mp hnot
  refine ⟨c, Nat.le_of_not_lt hc, ?_, ?_⟩
  · intro L hL
    exact ⟨family_candidate D Θ P t c hL, family_badList D Θ P t c hL⟩
  · exact family_pairwise_disjoint D Θ P t c

theorem few_bad_tail (hη₀ : 0 < η₀) (hh : 10 ^ 8 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.ListCount → D.BadListProb →
      0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g) →
      D.preLaw.pr (fun q => D.PosOK q.1.2 ∧ ¬ D.FewBad q.1.1 q.1.2 q.2.1.1) ≤ Real.exp (-(D.n : ℝ)) := by
  classical
  refine ⟨0, ?_⟩
  intro D _hn _hGF _hListCount _hBadListProb _hAvoid
  have hWitness (q : D.Pre) (hNF : ¬ D.FewBad q.1.1 q.1.2 q.2.1.1) :=
    bad_family_witness η₀ β p h D q.1.1 q.1.2 q.2.1.1 hNF
  /- The remaining estimate unions over cells and ordered `n`-tuples of disjoint bad candidates, then factors their
     tag events. The tag product law still needs the finite-support independence calculation and asymptotic bound. -/
  sorry

/-- L8.1f(x) (08:214): eligibility in slice `g` is a function of the positions and of auxiliary randomness
independent of the activations of slice `g` (other slices' positions, tags); on legality (from `PosOK ∧ FewBad`)
Lemma 3.8 (`height_selection_global`, with `hd_admissible` and the linear regime) bounds the failure of good
heights in a slice by `e^{-n^{1+c}}`; a union over the `exp(O(s log n))` slices gives `e^{-n}`. -/
theorem height_tail (hη₀ : 0 < η₀)
    (hadm : HDAdmissible 10 (b0H η₀) (bH η₀) (sigmaH η₀) (zetaH η₀) (thetaH η₀) (aH η₀) (1 / 2) 1 2) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.LegalOfCounts →
      D.preLaw.pr (fun q => D.PosOK q.1.2 ∧ D.FewBad q.1.1 q.1.2 q.2.1.1 ∧
        ¬ D.GoodH q.1.1 q.1.2 q.2.1.1 q.2.1.2) ≤ Real.exp (-(D.n : ℝ)) := by
  sorry

end Nodes

end HypercubeRamsey.S08
