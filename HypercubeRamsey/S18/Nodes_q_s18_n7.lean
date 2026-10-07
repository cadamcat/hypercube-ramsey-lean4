import HypercubeRamsey.S18.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace HypercubeRamsey.S18.Lane_q_s18_n7

open Classical Filter
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem paletteScale_sum (D : LateData hPT) :
    (∑ p : PaletteIndex D, D.paletteScale p) =
      ∑ i : Fin PT.tiling.m, (PT.tiling.P i).M := by
  classical
  rw [Fintype.sum_sigma]
  simp only [LateData.paletteScale, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hχ : (D.chi i : ℝ) ≠ 0 := by
    exact ne_of_gt (Nat.cast_pos.mpr (D.chi_pos i))
  calc
    (∑ _y : Fin (D.chi i), (PT.tiling.P i).M / (D.chi i : ℝ)) =
        (D.chi i : ℝ) * ((PT.tiling.P i).M / (D.chi i : ℝ)) := by simp
    _ = (PT.tiling.P i).M := by field_simp [hχ]

theorem paletteScale_sum_le_host (D : LateData hPT) :
    (∑ p : PaletteIndex D, D.paletteScale p) ≤ (T.S.N k : ℝ) := by
  classical
  rw [paletteScale_sum]
  have hdisj : (Set.univ : Set (Fin PT.tiling.m)).PairwiseDisjoint
      (fun i => (PT.tiling.P i).X) := by
    intro i hi j hj hij
    exact hPT.tiling_valid.patch_X_disjoint i j hij
  have hdisj' : ((Finset.univ : Finset (Fin PT.tiling.m)) : Set (Fin PT.tiling.m)).PairwiseDisjoint
      (fun i => (PT.tiling.P i).X) := by simpa using hdisj
  let U := (Finset.univ : Finset (Fin PT.tiling.m)).biUnion
    (fun i => (PT.tiling.P i).X)
  have hcard : U.card = ∑ i : Fin PT.tiling.m, ((PT.tiling.P i).X.card) := by
    dsimp [U]
    simpa using (Finset.card_biUnion (s := Finset.univ) hdisj')
  have hsub : U ⊆ (Finset.univ : Finset (Fin (T.S.N k))) := by
    intro x hx
    simp
  have hnat : (∑ i : Fin PT.tiling.m, ((PT.tiling.P i).M)) ≤ T.S.N k := by
    calc
      ∑ i : Fin PT.tiling.m, (PT.tiling.P i).M = U.card := by
        rw [hcard]
        apply Finset.sum_congr rfl
        intro i hi
        exact (PT.tiling.P i).cardX.symm
      _ ≤ Fintype.card (Fin (T.S.N k)) := Finset.card_le_card hsub
      _ = T.S.N k := Fintype.card_fin _
  exact_mod_cast hnat

private theorem paletteRows_disjoint (D : LateData hPT) :
    (Set.univ : Set (PaletteIndex D)).PairwiseDisjoint (D.paletteRows) := by
  intro p hp q hq hpq
  refine Finset.disjoint_left.2 ?_
  intro v hvp hvq
  simp only [LateData.paletteRows, Finset.mem_filter, Finset.mem_univ, true_and] at hvp hvq
  exact hpq (hvp.2.symm.trans hvq.2)

theorem paletteRows_card_sum_le_cube (D : LateData hPT) :
    (∑ p : PaletteIndex D, ((D.paletteRows p).card : ℝ)) ≤
      (2 : ℝ) ^ (T.S.n k : ℝ) := by
  classical
  let U := (Finset.univ : Finset (PaletteIndex D)).biUnion D.paletteRows
  have hcard : U.card = ∑ p : PaletteIndex D, (D.paletteRows p).card := by
    dsimp [U]
    have hdisj : ((Finset.univ : Finset (PaletteIndex D)) : Set (PaletteIndex D)).PairwiseDisjoint
        (D.paletteRows) := by simpa using paletteRows_disjoint D
    simpa using (Finset.card_biUnion (s := Finset.univ) hdisj)
  have hsub : U ⊆ (Finset.univ : Finset (Pos T k)) := by
    intro v hv
    simp
  have hnat : (∑ p : PaletteIndex D, (D.paletteRows p).card) ≤ Fintype.card (Pos T k) := by
    calc
      _ = U.card := hcard.symm
      _ ≤ Fintype.card (Pos T k) := Finset.card_le_card hsub
  have hposcard : Fintype.card (Pos T k) = 2 ^ (T.S.n k) := by
    simp [Pos, CubePos]
  have hreal : (∑ p : PaletteIndex D, ((D.paletteRows p).card : ℝ)) ≤
      ((Fintype.card (Pos T k) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [hposcard] at hreal
  simpa [Real.rpow_natCast] using hreal

theorem paletteScale_inv_sum_le {D : LateData hPT} {δ Kpair : ℝ}
    (hKpair : 0 < Kpair) (hPair : PairInitialFacts D δ Kpair)
    (hDensity : 1 ≤ densityScale T k) :
    (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) ≤
      Kpair * (2 : ℝ) ^ (T.S.n k : ℝ) /
        (densityScale T k * ((2 : ℝ) ^ ((T.S.n k : ℝ) - Real.sqrt (T.S.n k))) ^ 2) := by
  classical
  let n : ℝ := T.S.n k
  let L : ℝ := (2 : ℝ) ^ (n - Real.sqrt n)
  have hn : 0 ≤ n := by positivity
  have hL : 0 < L := Real.rpow_pos_of_pos (by norm_num) _
  have hrowsLower (p : PaletteIndex D) :
      L ≤ ((D.paletteRows p).card : ℝ) := by
    simpa [L, n] using hPair.2.1 p
  have hcount :
      (Fintype.card (PaletteIndex D) : ℝ) * L ≤ (2 : ℝ) ^ n := by
    calc
      (Fintype.card (PaletteIndex D) : ℝ) * L = ∑ p : PaletteIndex D, L := by simp
      _ ≤ ∑ p : PaletteIndex D, ((D.paletteRows p).card : ℝ) :=
        Finset.sum_le_sum fun p _ => hrowsLower p
      _ ≤ (2 : ℝ) ^ n := by simpa [n] using paletteRows_card_sum_le_cube D
  have hscaleInv (p : PaletteIndex D) :
      (D.paletteScale p)⁻¹ ≤ Kpair / (densityScale T k * L) := by
    have hrowsPos : 0 < ((D.paletteRows p).card : ℝ) := lt_of_lt_of_le hL (hrowsLower p)
    have hdens : 0 < densityScale T k := lt_of_lt_of_le (by norm_num) hDensity
    have hup := hPair.1 p
    have hmul : densityScale T k * L ≤ Kpair * D.paletteScale p := by
      have h' := (le_div_iff₀ hdens).mp (le_trans (hrowsLower p) hup)
      nlinarith
    have hscale : 0 < D.paletteScale p := by
      by_contra hnscale
      have hnonpos : D.paletteScale p ≤ 0 := le_of_not_gt hnscale
      have hright : Kpair * D.paletteScale p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hKpair.le hnonpos
      have hleft : 0 < densityScale T k * L := mul_pos hdens hL
      linarith
    have hdiv : (1 : ℝ) / D.paletteScale p ≤ Kpair / (densityScale T k * L) := by
      rw [div_le_div_iff₀ hscale (mul_pos hdens hL)]
      nlinarith [hmul]
    simpa [one_div] using hdiv
  have hsum :
      (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) ≤
        (Fintype.card (PaletteIndex D) : ℝ) * (Kpair / (densityScale T k * L)) := by
    calc
      _ ≤ ∑ p : PaletteIndex D, Kpair / (densityScale T k * L) :=
        Finset.sum_le_sum fun p _ => hscaleInv p
      _ = (Fintype.card (PaletteIndex D) : ℝ) * (Kpair / (densityScale T k * L)) := by simp
  have hdens : 0 < densityScale T k := lt_of_lt_of_le (by norm_num) hDensity
  have hconst : 0 ≤ Kpair / (densityScale T k * L ^ 2) := by positivity
  have hfinal :
      (Fintype.card (PaletteIndex D) : ℝ) * (Kpair / (densityScale T k * L)) ≤
        (2 : ℝ) ^ n * (Kpair / (densityScale T k * L ^ 2)) := by
    have := mul_le_mul_of_nonneg_right hcount hconst
    convert this using 1 <;> field_simp <;> ring
  calc
    (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) ≤
        (Fintype.card (PaletteIndex D) : ℝ) * (Kpair / (densityScale T k * L)) := hsum
    _ ≤ (2 : ℝ) ^ n * (Kpair / (densityScale T k * L ^ 2)) := hfinal
    _ = Kpair * (2 : ℝ) ^ n / (densityScale T k * L ^ 2) := by ring
    _ = Kpair * (2 : ℝ) ^ (T.S.n k : ℝ) /
          (densityScale T k * ((2 : ℝ) ^ ((T.S.n k : ℝ) - Real.sqrt (T.S.n k))) ^ 2) := by
      simp [L, n]

private theorem walk_cross_boundary {α : Type*} {G : SimpleGraph α} {u v : α}
    (p : G.Walk u v) {S : Set α} (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  induction p with
  | nil => simp_all
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ S
      · exact ih hb hv
      · exact ⟨a, hu, b, hb, hab⟩

private theorem connected_boundary {α : Type*} {G : SimpleGraph α} (hG : G.Connected)
    {S : Set α} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨y, hy⟩ := hSc
  obtain ⟨p, hp⟩ := hG.exists_isPath x y
  exact walk_cross_boundary p hx hy

private theorem exists_connected_finset_card {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (hG : G.Connected) :
    ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card α →
      ∃ S : Finset α, S.card = n ∧ (G.induce (S : Set α)).Connected := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
      intro hm hcard
      by_cases hm0 : m = 0
      · subst m
        let v : α := Classical.choice hG.nonempty
        refine ⟨{v}, by simp, ?_⟩
        haveI : Nonempty (↑({v} : Finset α)) := ⟨⟨v, Finset.mem_singleton_self v⟩⟩
        haveI : Subsingleton (↑({v} : Finset α)) := by
          refine ⟨fun x y => ?_⟩
          apply Subtype.ext
          have hx : x.1 ∈ ({v} : Finset α) := by
            change x.1 ∈ (↑({v} : Finset α))
            exact x.2
          have hy : y.1 ∈ ({v} : Finset α) := by
            change y.1 ∈ (↑({v} : Finset α))
            exact y.2
          exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
        exact SimpleGraph.Connected.of_subsingleton
      · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        obtain ⟨S, hScard, hSconn⟩ := ih hmpos (by omega)
        have hScardlt : S.card < Fintype.card α := by omega
        obtain ⟨v, hvuniv, hvnot⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := Finset.univ) hScardlt
        obtain ⟨u0, hu0⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
        obtain ⟨u, hu, w, hw, huw⟩ :=
          connected_boundary hG (by exact ⟨u0, hu0⟩) (by exact ⟨v, hvnot⟩)
        have hpair : (G.induce ({u, w} : Set α)).Connected :=
          G.induce_pair_connected_of_adj huw
        have hunion : (G.induce ((S : Set α) ∪ ({u, w} : Set α))).Connected :=
          G.induce_union_connected hSconn.preconnected hpair.preconnected ⟨u, hu, by simp⟩
        have hset : ((insert w S : Finset α) : Set α) =
            (S : Set α) ∪ ({u, w} : Set α) := by
          ext x
          simp [hu, or_assoc, or_left_comm, or_comm]
        have hnewconn : (G.induce ((insert w S : Finset α) : Set α)).Connected := by
          rw [hset]
          exact hunion
        refine ⟨insert w S, ?_, hnewconn⟩
        have hw' : w ∉ S := by simpa using hw
        rw [Finset.card_insert_of_notMem hw', hScard]

private theorem connected_image_subtype_finset {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (Q : Finset α) (S : Finset {x // x ∈ (Q : Set α)})
    (hS : ((G.induce (Q : Set α)).induce (S : Set {x // x ∈ (Q : Set α)})).Connected) :
    (G.induce ((S.image (fun x => x.1) : Finset α) : Set α)).Connected := by
  classical
  let f : {x // x ∈ S} → {x // x ∈ (S.image (fun x => x.1) : Finset α)} := fun x =>
    ⟨x.1.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hα : x.1.1 = y.1.1 := congrArg (fun z : {a // a ∈ (S.image (fun x => x.1) : Finset α)} => z.1) hxy
      have hrow : x.1 = y.1 := Subtype.ext hα
      exact Subtype.ext hrow
    · intro y
      rcases Finset.mem_image.mp y.2 with ⟨x, hx, hval⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hval
  let e : {x // x ∈ S} ≃ {x // x ∈ (S.image (fun x => x.1) : Finset α)} :=
    Equiv.ofBijective f hf
  let eG : (G.induce (Q : Set α)).induce (S : Set {x // x ∈ (Q : Set α)}) ≃g
      G.induce ((S.image (fun x => x.1) : Finset α) : Set α) :=
    { toEquiv := e
      map_rel_iff' := by intro x y; rfl }
  exact eG.connected_iff.mp hS

theorem hall_condition_of_no_connected_obstruction
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : SimpleGraph α) (R : Finset α) (f : α → Finset β) (t₀ : ℕ) (ht₀ : 3 ≤ t₀)
    (hAdj : ∀ x y, G.Adj x y ↔ x ≠ y ∧ (f x ∩ f y).Nonempty)
    (hTwo : ∀ x ∈ R, 2 ≤ (f x).card)
    (hLarge : ∀ S : Finset α, S ⊆ R → S.card = t₀ →
      (G.induce (S : Set α)).Connected → False)
    (hSmall : ∀ S : Finset α, S ⊆ R → 3 ≤ S.card → S.card < t₀ →
      (G.induce (S : Set α)).Connected → ¬ (S.biUnion f).card < S.card) :
    ∀ S : Finset α, S ⊆ R → S.card ≤ (S.biUnion f).card := by
  classical
  intro S hSR
  by_contra hnot
  have hdef : (S.biUnion f).card < S.card := Nat.lt_of_not_ge hnot
  let bads : Finset (Finset α) :=
    Finset.univ.filter fun Q => Q ⊆ R ∧ (Q.biUnion f).card < Q.card
  have hBads : bads.Nonempty := by
    refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSR, hdef⟩⟩
  let cards := bads.image Finset.card
  have hCards : cards.Nonempty := hBads.image Finset.card
  let minCard := cards.min' hCards
  have hMinCardMem : minCard ∈ cards := Finset.min'_mem _ _
  obtain ⟨Q, hQ, hQcard⟩ := Finset.mem_image.mp hMinCardMem
  have hQsub : Q ⊆ R := (Finset.mem_filter.mp hQ).2.1
  have hQdef : (Q.biUnion f).card < Q.card := (Finset.mem_filter.mp hQ).2.2
  have hmin : ∀ Q' ∈ bads, Q.card ≤ Q'.card := by
    intro Q' hQ'
    calc
      Q.card = minCard := hQcard
      _ ≤ Q'.card := Finset.min'_le cards _ (Finset.mem_image.mpr ⟨Q', hQ', rfl⟩)
  have hQpos : 0 < Q.card := by omega
  have hQthree : 3 ≤ Q.card := by
    by_contra hn
    have hlt : Q.card < 3 := Nat.lt_of_not_ge hn
    by_cases h1 : Q.card = 1
    · obtain ⟨x, hxQ⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
      have hcard : 2 ≤ (Q.biUnion f).card :=
        (hTwo x (hQsub hxQ)).trans
          (Finset.card_le_card (Finset.subset_biUnion_of_mem f hxQ))
      omega
    · by_cases h2 : Q.card = 2
      · obtain ⟨x, hxQ⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
        have hcard : 2 ≤ (Q.biUnion f).card :=
          (hTwo x (hQsub hxQ)).trans
            (Finset.card_le_card (Finset.subset_biUnion_of_mem f hxQ))
        omega
      · omega
  have hQconn : (G.induce (Q : Set α)).Connected := by
    by_contra hNotConn
    let GQ := G.induce (Q : Set α)
    letI : Fintype {x // x ∈ (Q : Set α)} := inferInstance
    letI : DecidableEq {x // x ∈ (Q : Set α)} := inferInstance
    obtain ⟨root, hroot⟩ := Finset.card_pos.mp hQpos
    let r : {x // x ∈ (Q : Set α)} := ⟨root, by simpa using hroot⟩
    have hUnreach : ∃ y, ¬ GQ.Reachable r y := by
      by_contra hall
      apply hNotConn
      apply (GQ.connected_iff_exists_forall_reachable).2
      refine ⟨r, ?_⟩
      intro y
      by_contra hny
      exact hall ⟨y, hny⟩
    obtain ⟨y, hyUnreach⟩ := hUnreach
    let U : Finset {x // x ∈ (Q : Set α)} :=
      Finset.univ.filter fun x => GQ.Reachable r x
    let V : Finset {x // x ∈ (Q : Set α)} := Finset.univ \ U
    have hrU : r ∈ U := by simp [U]
    have hyV : y ∈ V := by simp [V, U, hyUnreach]
    let Uα : Finset α := U.image (fun x => x.1)
    let Vα : Finset α := V.image (fun x => x.1)
    have hpart : Uα ∪ Vα = Q := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
          exact z.2
        · rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
          exact z.2
      · intro hxQ
        let z : {x // x ∈ (Q : Set α)} := ⟨x, by simpa using hxQ⟩
        by_cases hzu : z ∈ U
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨z, hzu, rfl⟩))
        · have hzv : z ∈ V := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzu⟩
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨z, hzv, rfl⟩))
    have hUsub : Uα ⊆ Q := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
      exact z.2
    have hVsub : Vα ⊆ Q := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
      exact z.2
    have hUcard : Uα.card = U.card := by
      change (U.image (fun x => x.1)).card = U.card
      exact Finset.card_image_iff.mpr (by
        intro x hx z hz heq
        exact Subtype.ext heq)
    have hVcard : Vα.card = V.card := by
      change (V.image (fun x => x.1)).card = V.card
      exact Finset.card_image_iff.mpr (by
        intro x hx z hz heq
        exact Subtype.ext heq)
    have hUpos : Uα.Nonempty := by
      exact ⟨root, Finset.mem_image.mpr ⟨r, hrU, rfl⟩⟩
    have hVpos : Vα.Nonempty := by
      exact ⟨y.1, Finset.mem_image.mpr ⟨y, hyV, rfl⟩⟩
    have hNoCross : ∀ x ∈ U, ∀ z ∈ V, ¬ G.Adj x.1 z.1 := by
      intro x hx z hz hadj
      have hxReach : GQ.Reachable r x := (Finset.mem_filter.mp hx).2
      have hadjQ : GQ.Adj x z := by simpa [GQ] using hadj
      have hzReach : GQ.Reachable r z := hxReach.trans hadjQ.reachable
      have hzInU : z ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzReach⟩
      exact (Finset.mem_sdiff.mp hz).2 hzInU
    have hendDisj : Disjoint (Uα.biUnion f) (Vα.biUnion f) := by
      refine Finset.disjoint_left.mpr ?_
      intro b hbU hbV
      rcases Finset.mem_biUnion.mp hbU with ⟨x, hxU, hbx⟩
      rcases Finset.mem_biUnion.mp hbV with ⟨z, hzV, hbz⟩
      rcases Finset.mem_image.mp hxU with ⟨x', hxU', rfl⟩
      rcases Finset.mem_image.mp hzV with ⟨z', hzV', rfl⟩
      have hxz : x'.1 ≠ z'.1 := by
        intro heq
        have : x' = z' := Subtype.ext heq
        have hzU : z' ∈ U := this ▸ hxU'
        exact (Finset.mem_sdiff.mp hzV').2 hzU
      have hinter : (f x'.1 ∩ f z'.1).Nonempty :=
        ⟨b, Finset.mem_inter.mpr ⟨hbx, hbz⟩⟩
      exact hNoCross x' hxU' z' hzV' ((hAdj x'.1 z'.1).2 ⟨hxz, hinter⟩)
    have hEndpointSplit : Q.biUnion f = Uα.biUnion f ∪ Vα.biUnion f := by
      rw [← hpart]
      ext b
      constructor
      · intro hb
        rcases Finset.mem_biUnion.mp hb with ⟨x, hx, hbx⟩
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨x, hx, hbx⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨x, hx, hbx⟩))
      · intro hb
        rcases Finset.mem_union.mp hb with hb | hb
        · rcases Finset.mem_biUnion.mp hb with ⟨x, hx, hbx⟩
          exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_union.mpr (Or.inl hx), hbx⟩
        · rcases Finset.mem_biUnion.mp hb with ⟨x, hx, hbx⟩
          exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_union.mpr (Or.inr hx), hbx⟩
    have hRowsDisjoint : Disjoint Uα Vα := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxU hxV
      rcases Finset.mem_image.mp hxU with ⟨x', hxU', rfl⟩
      rcases Finset.mem_image.mp hxV with ⟨z', hzV', heq⟩
      have hsame : x' = z' := Subtype.ext heq.symm
      have hzU : z' ∈ U := hsame ▸ hxU'
      exact (Finset.mem_sdiff.mp hzV').2 hzU
    have hRowsCard : Q.card = Uα.card + Vα.card := by
      rw [← hpart, Finset.card_union_of_disjoint hRowsDisjoint]
    have hEndCard : (Q.biUnion f).card =
        (Uα.biUnion f).card + (Vα.biUnion f).card := by
      rw [hEndpointSplit, Finset.card_union_of_disjoint hendDisj]
    have hdefSplit : (Uα.biUnion f).card < Uα.card ∨ (Vα.biUnion f).card < Vα.card := by
      have hUcardpos : 0 < Uα.card := Finset.card_pos.mpr hUpos
      have hVcardpos : 0 < Vα.card := Finset.card_pos.mpr hVpos
      omega
    rcases hdefSplit with hUdef | hVdef
    · have hUmem : Uα ∈ bads := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Finset.Subset.trans hUsub hQsub, hUdef⟩
      have hminU := hmin Uα hUmem
      have hUlt : Uα.card < Q.card := by
        rw [hRowsCard]
        have hVcardpos : 0 < Vα.card := Finset.card_pos.mpr hVpos
        omega
      omega
    · have hVmem : Vα ∈ bads := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Finset.Subset.trans hVsub hQsub, hVdef⟩
      have hminV := hmin Vα hVmem
      have hVlt : Vα.card < Q.card := by
        rw [hRowsCard]
        have hUcardpos : 0 < Uα.card := Finset.card_pos.mpr hUpos
        omega
      omega
  by_cases hQge : Q.card ≥ t₀
  · obtain ⟨S, hScard, hSconn⟩ :=
      exists_connected_finset_card (G.induce (Q : Set α)) hQconn t₀ (by omega)
        (by simpa using hQge)
    let Sα : Finset α := S.image (fun x => x.1)
    have hSαcard : Sα.card = t₀ := by
      dsimp [Sα]
      rw [Finset.card_image_of_injective S (fun x y heq => Subtype.ext heq)]
      exact hScard
    have hSαsub : Sα ⊆ R := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
      exact hQsub z.2
    have hSαconn := connected_image_subtype_finset G Q S hSconn
    exact hLarge Sα hSαsub hSαcard hSαconn
  · have hQlt : Q.card < t₀ := Nat.lt_of_not_ge hQge
    exact hSmall Q hQsub hQthree hQlt hQconn hQdef

theorem finLaw_pr_bind_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (A : α → Prop) :
    (FinLaw.bind P K).pr (fun ab => A ab.1) = P.pr A := by
  classical
  unfold FinLaw.pr FinLaw.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hA : A a
  · simp only [hA, if_true]
    calc
      ∑ x, P.w a * (K a).w x = P.w a * ∑ x, (K a).w x := by rw [Finset.mul_sum]
      _ = P.w a := by rw [(K a).sum_one, mul_one]
  · simp [hA]

theorem finLaw_pr_split {α : Type*} [Fintype α] (P : FinLaw α)
    (A B : α → Prop) :
    P.pr A = P.pr (fun x => A x ∧ B x) + P.pr (fun x => A x ∧ ¬ B x) := by
  classical
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hA : A x <;> by_cases hB : B x <;> simp [hA, hB]

theorem exists_weight_pos_of_pr_pos {α : Type*} [Fintype α]
    (P : FinLaw α) (A : α → Prop) (hA : 0 < P.pr A) :
    ∃ x, A x ∧ 0 < P.w x := by
  classical
  by_contra h
  push_neg at h
  have hzero : ∀ x, (if A x then P.w x else 0) = 0 := by
    intro x
    by_cases hx : A x
    · have hxle : P.w x ≤ 0 := h x hx
      simp [hx, le_antisymm hxle (P.nonneg x)]
    · simp [hx]
  have hsum : (∑ x, if A x then P.w x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact hzero x
  unfold FinLaw.pr at hA
  linarith

theorem depFun_app_eq {ι : Sort*} {R : ι → Sort*} {β : Sort*}
    (F : ∀ i, R i → β) {i j : ι} (h : i = j) (x : R i) :
    F i x = F j (Eq.mp (congrArg R h) x) := by
  cases h
  rfl

end HypercubeRamsey.S18.Lane_q_s18_n7
