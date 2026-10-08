import HypercubeRamsey.S05.Centres_sol_s05_k1_local
import HypercubeRamsey.S05.Centres_sol_s05_k1_cap

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 800000

/-- `Finset.mem_of_mem_filter` for any decidability instance of the filter predicate; the
instance is read off the hypothesis instead of being synthesized. -/
theorem mem_of_mem_filter_any {α : Type*} {p : α → Prop} {inst : DecidablePred p} {s : Finset α}
    {x : α} (h : x ∈ @Finset.filter α p inst s) : x ∈ s :=
  @Finset.mem_of_mem_filter α p inst s x h

section Tables
variable {Target Data Ω : Type*} [Fintype Target] [Fintype Data] [Fintype Ω]
variable (T U : PresentationTable (Target := Target) (Data := Data) (Ω := Ω))

theorem adjustedRow_mass (d : Data) (x : Target) :
    T.experiment.adjustedRow d x =
      T.prior.w x * presentationMass T.raw T.present x d / T.experiment.selectedMass d := by
  unfold SelectionExperiment5.adjustedRow
  by_cases hm : T.experiment.selectedMass d = 0
  · simp only [hm, ite_true, div_zero]
  · rw [if_neg hm]
    change T.prior.w x * T.likelihood x d * T.selection x d / _ = _
    rw [mul_assoc, T.likelihood_mul_selection]

theorem completedProxy_congr (ε : ℝ) (source source' : Data → Target → ℝ)
    (d : Data) (x : Target) (hp : T.prior = U.prior)
    (hl : ∀ y, T.likelihood y d = U.likelihood y d)
    (hm : ∀ y, presentationMass T.raw T.present y d = presentationMass U.raw U.present y d)
    (hs : source d x = source' d x) : T.completedProxy ε source d x = U.completedProxy ε source' d x := by
  have hb : T.experiment.baseMass d = U.experiment.baseMass d := by
    unfold SelectionExperiment5.baseMass
    change (∑ y, T.prior.w y * T.likelihood y d) = ∑ y, U.prior.w y * U.likelihood y d
    simp_rw [hp, hl]
  have hm' : T.experiment.selectedMass d = U.experiment.selectedMass d := by
    rw [T.experiment_selectedMass, U.experiment_selectedMass]
    simp_rw [hp, hm]
  have hbase : T.experiment.baseRow d x = U.experiment.baseRow d x := by
    rw [T.experiment_baseRow, U.experiment_baseRow, hp, hl x]
    simp_rw [hl]
  have hadj : T.experiment.adjustedRow d x = U.experiment.adjustedRow d x := by
    rw [adjustedRow_mass T d x, adjustedRow_mass U d x, hp, hm x, hm']
  unfold PresentationTable.completedProxy
  rw [hb, hs]
  split_ifs
  · rfl
  · unfold SelectionExperiment5.proxyRow
    rw [hb, hm', hadj, hbase]

theorem expect_completed_external (ε c : ℝ) (source : Data → Target → ℝ)
    (P : FinProb Ω) (rows : Ω → Target → ℝ) (y x : Target)
    (hr : T.raw y = P) (ho : ∀ ω x, rows ω x = T.completedRow ε source (T.present y ω) x) :
    P.expect (fun ω => c * rows ω x) =
      c * ∑ d, presentationMass T.raw T.present y d * T.completedProxy ε source d x := by
  rw [← T.expect_completedRow ε source y x, hr]
  unfold FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  change P.w ω * (c * rows ω x) = c * (P.w ω * T.completedRow ε source (T.present y ω) x)
  rw [ho ω x]
  ring

end Tables

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) {Id : Type} [DecidableEq Id]

theorem withCol_joinHidden (b : X.Base) (hi : X.HighHid) (lo : X.LowHid)
    (k : X.LowIdx) (θ : Fin 1 → Fin N) :
    X.withCol (b, X.joinHidden hi lo) (.inl k) θ =
      (b, X.joinHidden hi (Function.update lo k θ)) := by
  apply Prod.ext
  · rfl
  funext ℓ
  cases ℓ with
  | inl k' =>
    by_cases he : k' = k
    · subst k'
      change Function.update (X.joinHidden hi lo) (.inl k) θ (.inl k) = Function.update lo k θ k
      exact (Function.update_self (.inl k) θ (X.joinHidden hi lo)).trans (Function.update_self k θ lo).symm
    · change Function.update (X.joinHidden hi lo) (.inl k) θ (.inl k') = Function.update lo k θ k'
      exact (Function.update_of_ne (Sum.inl_injective.ne he) θ (X.joinHidden hi lo)).trans
        (Function.update_of_ne he θ lo).symm
  | inr i =>
    change Function.update (X.joinHidden hi lo) (.inl k) θ (.inr i) = hi i
    exact Function.update_of_ne (show (Sum.inr i : X.Key) ≠ .inl k by simp) θ (X.joinHidden hi lo)

theorem low_column_const (ℓ : X.Key) (hl : ℓ.isLeft)
    (f : Fin (colLen5 (X.p.s n) ℓ) → Fin N) :
    ∃ x : Fin N, f = fun _ => x := by
  cases ℓ with
  | inl k =>
    refine ⟨f (0 : Fin 1), ?_⟩
    funext h
    have hh : (h : Fin 1) = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance h (0 : Fin 1)
    exact congrArg (fun h : Fin 1 => f h) hh
  | inr k => simp at hl

theorem withCol_current (H : X.KeyHist) (ℓ : X.Key) : X.withCol H ℓ (H.2 ℓ) = H := by
  apply Prod.ext
  · rfl
  funext k
  by_cases hk : k = ℓ
  · subst k; simp only [Setup5.withCol, Function.update_self]
  · simp only [Setup5.withCol, Function.update_of_ne hk]

theorem observation_history_congr (H H' : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hb : H.1 = H'.1) (hc : ∀ c ∈ r.2.1, ∀ ℓ ∈ c.2.2.1, H.2 ℓ = H'.2 ℓ) :
    observationReferenceMass X H r a = observationReferenceMass X H' r a ∧
      ∀ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
        X.candGateOn H r a θ = X.candGateOn H' r a θ ∧
          X.obsLikOn H r a θ none = X.obsLikOn H' r a θ none ∧
            X.step3PostOn H r a none θ = X.step3PostOn H' r a none θ := by
  have hcols (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (c : Id × X.Ty) (hc' : c ∈ r.2.1) :
      ∀ ℓ ∈ c.2.2.1, (X.withCol H r.1 θ).2 ℓ = (X.withCol H' r.1 θ).2 ℓ := by
    intro ℓ hℓ
    by_cases he : ℓ = r.1
    · subst ℓ; simp only [Setup5.withCol, Function.update_self]
    · simp only [Setup5.withCol, Function.update_of_ne he, hc c hc' ℓ hℓ]
  have hd (c : Id × X.Ty) (hc' : c ∈ r.2.1) : X.blockLawDel H c.2 r.1 = X.blockLawDel H' c.2 r.1 :=
    Lane_sol_s05_h5l.blockLawOn_ext X H H' c.2 (c.2.2.1.erase r.1) hb
      (fun ℓ hℓ => hc c hc' ℓ (Finset.mem_of_mem_erase hℓ))
  have ho (c : Id × X.Ty) (hc' : c ∈ r.2.1) : X.blockLaw H c.2 = X.blockLaw H' c.2 :=
    Lane_sol_s05_h5l.blockLawOn_ext X H H' c.2 c.2.2.1 hb (hc c hc')
  have hw (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (c : Id × X.Ty) (hc' : c ∈ r.2.1) :
      X.blockLaw (X.withCol H r.1 θ) c.2 = X.blockLaw (X.withCol H' r.1 θ) c.2 :=
    Lane_sol_s05_h5l.blockLawOn_ext X _ _ c.2 c.2.2.1 hb (hcols θ c hc')
  have hg (θ) : X.candGateOn H r a θ = X.candGateOn H' r a θ := by
    apply propext
    unfold Setup5.candGateOn
    have he (c : Id × X.Ty) (hc' : c ∈ r.2.1) :
        X.blockMass H c.2 (c.2.2.1.erase r.1) = X.blockMass H' c.2 (c.2.2.1.erase r.1) :=
      X.blockMass_ext5 H H' c.2 _ hb (fun ℓ hℓ => hc c hc' ℓ (Finset.mem_of_mem_erase hℓ))
    have hf (c : Id × X.Ty) (hc' : c ∈ r.2.1) :
        X.blockMass (X.withCol H r.1 θ) c.2 c.2.2.1 = X.blockMass (X.withCol H' r.1 θ) c.2 c.2.2.1 :=
      X.blockMass_ext5 _ _ c.2 _ hb (hcols θ c hc')
    constructor <;> intro hh
    · refine ⟨?_, hh.2⟩
      intro c hc' ht
      simpa only [he c hc', hf c hc'] using hh.1 c hc' ht
    · refine ⟨?_, hh.2⟩
      intro c hc' ht
      simpa only [he c hc', hf c hc'] using hh.1 c hc' ht
  have hl (θ) : X.obsLikOn H r a θ none = X.obsLikOn H' r a θ none := by
    unfold Setup5.obsLikOn
    apply Finset.prod_congr rfl
    intro c hc'
    have hc'' := mem_of_mem_filter_any hc'
    rw [hw θ c hc'', hd c hc'']
  have hm : X.step3MassOn H r a none = X.step3MassOn H' r a none := by
    unfold Setup5.step3MassOn
    rw [hb]
    simp_rw [hg, hl]
  refine ⟨?_, ?_⟩
  · unfold observationReferenceMass
    apply Finset.prod_congr rfl
    intro c hc'
    rw [hd c hc', ho c hc']
  · intro θ
    refine ⟨hg θ, hl θ, ?_⟩
    unfold Setup5.step3PostOn
    rw [hb, hg θ, hl θ, hm]

theorem update_sign_distance {m : ℕ} (t : CubeVertex m) (i : Fin m) (b : Bool) :
    _root_.hammingDist (Function.update t i b) t ≤ 1 := by
  unfold _root_.hammingDist
  have hsub : (Finset.univ.filter (fun j : Fin m => Function.update t i b j ≠ t j)) ⊆ {i} := by
    intro j hj
    by_contra hn
    have hji : j ≠ i := by simpa only [Finset.mem_singleton] using hn
    have he := (Finset.mem_filter.mp hj).2
    simp only [Function.update_of_ne hji, ne_eq, not_true_eq_false] at he
  simpa only [Finset.card_singleton] using Finset.card_le_card hsub

theorem adjacent_sign_distance {m : ℕ} (g : ChunkGeometry5 n m) (x y : CubeVertex n)
    (hxy : (cube n).Adj x y) : _root_.hammingDist (g.sign y) (g.sign x) ≤ 1 := by
  have hs := Lane_sol_s05_h5l.adjacent_sign_mem g x y hxy
  simp only [Lane_sol_s05_h5l.neighborSigns, Finset.mem_insert, Finset.mem_image] at hs
  rcases hs with he | ⟨i, hi, he⟩
  · rw [he]; simp
  · rw [← he]
    exact update_sign_distance _ _ _

theorem keyAt_low_sign {m J : ℕ} (i : CoarseKey5 n) (t : CubeVertex m) (j : ℕ)
    (k : CoarseKey5 n × CubeVertex m × Fin (J + 1))
    (hk : keyAt5 J i t j = .inl k) : k.2.1 = t := by
  unfold keyAt5 at hk
  split_ifs at hk with hj
  · have he := Sum.inl.inj hk
    exact (congrArg (fun k : CoarseKey5 n × CubeVertex m × Fin (J + 1) => k.2.1) he).symm

theorem type_low_key_distance (x : CubeVertex n) (k : X.LowIdx)
    (hk : Sum.inl k ∈ X.g.typeKeys (X.p.J n) x) :
    _root_.hammingDist k.2.1 (X.g.sign x) ≤ 1 := by
  have hx : X.g.severity x ≤ X.p.J n := low_type_of_listed X x (.inl k) (by simp) hk
  simp only [ChunkGeometry5.typeKeys, if_pos hx, Finset.mem_union, Finset.mem_image] at hk
  rcases hk with (⟨i, hi, he⟩ | ⟨j, hj, he⟩) | ⟨j, hj, he⟩
  · rw [keyAt_low_sign i (X.g.sign x) _ k he]
    simp
  · rw [keyAt_low_sign (X.g.key x) (Function.update (X.g.sign x) j (!X.g.sign x j)) _ k he]
    exact update_sign_distance _ _ _
  · rw [keyAt_low_sign (X.g.key x) (X.g.sign x) j k he]
    simp

theorem record_low_key_distance (r : X.RecordOn Id) (y : OddRole5 n) (μ : X.St.Site → Id)
    (hr : X.RecordFrom r y μ) (c : Id × X.Ty) (hc : c ∈ r.2.1) (k : X.LowIdx)
    (hk : Sum.inl k ∈ c.2.2.1) : _root_.hammingDist k.2.1 (X.g.sign y.1) ≤ 2 := by
  letI : DecidableEq (Id × X.Ty) := Classical.decEq _
  have hc' := (Finset.ext_iff.mp hr.2.1 c).mp hc
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hc'
  have hK : c.2 = X.g.evenType (X.p.J n) a.1 := (congrArg Prod.snd he).symm
  have hmem : Sum.inl k ∈ X.g.typeKeys (X.p.J n) a.1 := by simpa only [hK, ChunkGeometry5.evenType] using hk
  have h1 := type_low_key_distance X a.1 k hmem
  have hh := adjacent_sign_distance X.g a.1 y.1 (Finset.mem_filter.mp ha).2
  have h2 : _root_.hammingDist (X.g.sign a.1) (X.g.sign y.1) ≤ 1 := by
    simpa only [_root_.hammingDist_comm] using hh
  have ht := _root_.hammingDist_triangle k.2.1 (X.g.sign a.1) (X.g.sign y.1)
  omega

end
end HypercubeRamsey.Lane_sol_s05_k1
