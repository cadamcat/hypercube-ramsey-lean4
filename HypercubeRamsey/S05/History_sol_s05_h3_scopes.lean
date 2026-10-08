import HypercubeRamsey.S05.History_sol_s05_h3_high_records
import HypercubeRamsey.S05.History_sol_s05_h3_budgets
import HypercubeRamsey.S05.History_sol_s05_h5l_local

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical OAI.HypercubeRamsey Lane_q_s05_h23
open Lane_sol_s05_hist1b Lane_sol_s05_h5l
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

 def highGroupScope {n : ℕ} (q : CoarseKey5 n) : Finset (CoarseKey5 n) := coarseBall 2 q

 theorem highGroup_neighbors_card {n : ℕ} (q : CoarseKey5 n) :
    (Finset.univ.filter (LocalAdj5 highGroupScope q)).card ≤ coarseCountBound 4 := by
  classical
  have hsub : Finset.univ.filter (LocalAdj5 highGroupScope q) ⊆ coarseBall 4 q := by
    intro q' hq'
    have hh := (Finset.mem_filter.mp hq').2.2
    rw [Finset.disjoint_left] at hh
    push_neg at hh
    obtain ⟨k, hk, hk'⟩ := hh
    have hn : coarseNear 4 q q' :=
      coarseNear_trans (Finset.mem_filter.mp hk).2 (coarseNear_symm (Finset.mem_filter.mp hk').2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
  exact (Finset.card_le_card hsub).trans (coarseBall_card_bound 4 q)

 theorem type_key_coarse_mem {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)
    (x : CubeVertex n) (ℓ : HiddenKey5 n m J) (hℓ : ℓ ∈ (g.evenType J x).2.1) :
    ℓ.coarse ∈ g.coarseRange x := by
  classical
  have hself : g.key x ∈ g.coarseRange x := by simp [ChunkGeometry5.coarseRange]
  change ℓ ∈ g.typeKeys J x at hℓ
  unfold ChunkGeometry5.typeKeys at hℓ
  by_cases hx : g.severity x ≤ J
  · rw [if_pos hx] at hℓ
    rcases Finset.mem_union.mp hℓ with hAB | hC
    · rcases Finset.mem_union.mp hAB with hA | hB
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
        simpa only [keyAt5_coarse] using hi
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
        simpa only [keyAt5_coarse] using hself
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hC
      simpa only [keyAt5_coarse] using hself
  · rw [if_neg hx] at hℓ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
    exact hi

 theorem optional_key_coarse {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)
    (x : CubeVertex n) (ℓ : HiddenKey5 n m J) (hℓ : ℓ ∈ (g.optionalKey J x).toFinset) :
    ℓ.coarse = g.key x := by
  unfold ChunkGeometry5.optionalKey at hℓ
  split_ifs at hℓ with h
  · simp only [Option.toFinset_some, Finset.mem_singleton] at hℓ
    subst ℓ
    rfl
  · simp at hℓ

 theorem record_keys_coarse_near (X : Setup5 γ K' χ n N E G)
    (y : OddRole5 n) (μ : X.St.Site → Fin (X.p.T n)) (r : X.AbsRecord)
    (hr : X.RecordFrom r y μ) :
    ∀ ℓ ∈ recordKeys X r, coarseNear 2 (X.g.key y.1) ℓ.coarse := by
  classical
  letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
  have hocc : X.RecOccurs r := ⟨y, μ, hr⟩
  intro ℓ hℓ
  simp only [recordKeys, Finset.mem_insert, Finset.mem_union] at hℓ
  rcases hℓ with ht | ha | ho
  · subst ℓ
    rw [← hr.1, Lane_sol_s05_hist1b.roleKey_coarse]
    exact coarseNear_refl 2 _
  · rw [occurring_record_arrays X r hocc] at ha
    obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp ha
    have hc' := Eq.mp (congrArg (fun S => c ∈ S) hr.2.1) hc
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hc'
    subst c
    have hdata := neighbor_coarse_data X.g y.1 a.1 ((Finset.mem_filter.mp ha).2.symm)
    exact (Finset.mem_filter.mp (hdata.2 (type_key_coarse_mem X.g (X.p.J n) a.1 ℓ hkc))).2
  · obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp ho
    have hc' := Eq.mp (congrArg (fun S => c ∈ S) hr.2.2.1) hc
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hc'
    subst c
    have hopt := optional_key_coarse X.g (X.p.J n) a.1 ℓ hkc
    rw [hopt]
    have hnear := (Finset.mem_filter.mp
      (neighbor_coarse_data X.g y.1 a.1 ((Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2.symm)).1).2
    intro i
    exact (hnear i).trans (by norm_num : 1 ≤ 2)

 theorem recordArrays_high_signShift (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (hmask : r.2.2.2 = none) :
    recordArrays X (shiftHighRecord X t r) = (recordArrays X r).image (obsSignMap X t) := by
  unfold recordArrays shiftHighRecord
  simp only [hmask, Option.toFinset_none, Finset.image_empty, Finset.union_empty,
    Finset.image_union, Finset.image_image]
  rfl

 theorem record_keys_shift_coarse (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (q : CoarseKey5 n)
    (hmask : r.2.2.2 = none)
    (hlocal : ∀ ℓ ∈ recordKeys X r, coarseNear 2 q ℓ.coarse) :
    ∀ ℓ ∈ recordKeys X (shiftHighRecord X t r), coarseNear 2 q ℓ.coarse := by
  classical
  intro ℓ hℓ
  simp only [recordKeys, Finset.mem_insert, Finset.mem_union, shiftHighRecord_key] at hℓ
  rcases hℓ with ht | ha | ho
  · subst ℓ
    exact hlocal r.1 (by simp [recordKeys])
  · obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp ha
    rw [recordArrays_high_signShift X t r hmask] at hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    change ℓ ∈ d.2.2.1.image (signShiftKey5 X t) at hkc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hkc
    rw [signShiftKey5_coarse]
    apply hlocal
    simp only [recordKeys, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inr (Or.inl ⟨d, hd, hk⟩)
  · obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp ho
    change c ∈ r.2.2.1.image (jointSignMap X t) at hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    change ℓ ∈ (d.2.2.map (signShiftKey5 X t)).toFinset at hkc
    cases he : d.2.2 with
    | none => simp [he] at hkc
    | some k =>
      simp only [he, Option.map_some, Option.toFinset_some, Finset.mem_singleton] at hkc
      subst ℓ
      rw [signShiftKey5_coarse]
      apply hlocal
      simp only [recordKeys, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
      exact Or.inr (Or.inr ⟨d, hd, by simp [he]⟩)

 theorem normalized_record_scope (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (r : NormalizedHighRecordAt X q) :
    ∀ ℓ ∈ recordKeys X r.1, ℓ.coarse ∈ highGroupScope q := by
  obtain ⟨r₀, t, hr₀, hkey, he⟩ := r.2.2
  obtain ⟨y, μ, hrec⟩ := hr₀
  have hm := occurring_high_mask_none X r₀ ⟨y, μ, hrec⟩ q hkey
  have hq : X.g.key y.1 = q := by
    rw [← Lane_sol_s05_hist1b.roleKey_coarse X y.1, hrec.1, hkey]
    rfl
  have hlocal : ∀ ℓ ∈ recordKeys X r₀, coarseNear 2 q ℓ.coarse := by
    simpa only [hq] using record_keys_coarse_near X y μ r₀ hrec
  intro ℓ hℓ
  rw [he] at hℓ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    record_keys_shift_coarse X t r₀ q hm hlocal ℓ hℓ⟩

 def highRecordMean (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (r : X.AbsRecord) (hi : HiddenHigh5 X) : ℝ :=
  (lowRawLaw X b).expect (fun lo => X.step3Rate (b, (hiddenSplitEquiv5 X).symm (lo, hi)) r)

 theorem highRecordMean_depends (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (q : CoarseKey5 n) (r : NormalizedHighRecordAt X q) :
    FinProb.DependsOn (highRecordMean X b r.1) (highGroupScope q) := by
  intro hi hi' h
  apply congrArg (lowRawLaw X b).expect
  funext lo
  refine step3Rate_ext X (b, (hiddenSplitEquiv5 X).symm (lo, hi))
    (b, (hiddenSplitEquiv5 X).symm (lo, hi')) r.1 rfl ?_
  intro ℓ hℓ
  cases ℓ with
  | inl k => rfl
  | inr i => exact h i (normalized_record_scope X q r (.inr i) hℓ)

end
end HypercubeRamsey.Lane_sol_s05_h23
