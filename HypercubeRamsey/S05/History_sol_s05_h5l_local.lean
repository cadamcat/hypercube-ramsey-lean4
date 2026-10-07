import HypercubeRamsey.S05.History_sol_s05_h5l_avoid

namespace HypercubeRamsey.Lane_sol_s05_h5l

open Classical OAI.HypercubeRamsey

noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

/-- All arrays explicitly named by a record. -/
def recordArrays (r : X.AbsRecord) : Finset (Fin (X.p.T n) × X.Ty) :=
  r.2.1 ∪ r.2.2.1.image (fun c => (c.1, c.2.1)) ∪
    (r.2.2.2.toFinset.image fun c => (c.1, c.2.1))

/-- Columns read by the record's array kernels, its target and its optional entries. -/
def recordKeys (r : X.AbsRecord) : Finset X.Key :=
  insert r.1 ((recordArrays X r).biUnion (fun c => c.2.2.1) ∪
    r.2.2.1.biUnion (fun c => c.2.2.toFinset))

private theorem obs_mem (r : X.AbsRecord) (c) (hc : c ∈ r.2.1) :
    c ∈ recordArrays X r := by simp [recordArrays, hc]

private theorem ref_mem (r : X.AbsRecord) (c) (hc : c ∈ r.2.2.1) :
    (c.1, c.2.1) ∈ recordArrays X r := by
  simp only [recordArrays, Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inr ⟨c, hc, rfl⟩)

private theorem pool_mem (r : X.AbsRecord) (c M) (hc : r.2.2.2 = some (c.1, c.2, M)) :
    c ∈ recordArrays X r := by
  simp only [recordArrays, hc, Option.toFinset_some, Finset.image_singleton,
    Finset.mem_union, Finset.mem_singleton]
  exact Or.inr trivial

theorem blockLawOn_ext (H H' : X.KeyHist) (K : X.Ty) (S : Finset X.Key)
    (hb : H.1 = H'.1) (hc : ∀ ℓ ∈ S, H.2 ℓ = H'.2 ℓ) :
    X.blockLawOn H K S = X.blockLawOn H' K S := by
  unfold Setup5.blockLawOn
  congr 1
  funext z
  unfold Setup5.blockWeight
  rw [hb]
  congr 1
  exact Finset.prod_congr rfl (fun ℓ hℓ => by rw [hc ℓ hℓ])

private theorem replaced_cols (H H' : X.KeyHist) (target : X.Key)
    (θ : Fin (colLen5 (X.p.s n) target) → Fin N) (S : Finset X.Key)
    (hc : ∀ ℓ ∈ S, H.2 ℓ = H'.2 ℓ) :
    ∀ ℓ ∈ S, (X.withCol H target θ).2 ℓ = (X.withCol H' target θ).2 ℓ := by
  intro ℓ hℓ
  by_cases he : ℓ = target
  · subst ℓ; simp [Setup5.withCol]
  · simp only [Setup5.withCol, Function.update_of_ne he, hc ℓ hℓ]

/-- The record test is unchanged when its named arrays and columns are unchanged. -/
theorem step3Fail_ext (H H' : X.KeyHist) (r : X.AbsRecord)
    (a a' : X.ArraysOn (Fin (X.p.T n))) (hb : H.1 = H'.1)
    (hcol : ∀ ℓ ∈ recordKeys X r, H.2 ℓ = H'.2 ℓ)
    (ha : ∀ c ∈ recordArrays X r, a c = a' c) :
    X.step3FailOn H r a = X.step3FailOn H' r a' := by
  have ht : H.2 r.1 = H'.2 r.1 := hcol _ (by simp [recordKeys])
  have htypes (c) (hc : c ∈ recordArrays X r) :
      ∀ ℓ ∈ c.2.2.1, H.2 ℓ = H'.2 ℓ := by
    intro ℓ hℓ
    apply hcol
    simp only [recordKeys, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inr (Or.inl ⟨c, hc, hℓ⟩)
  have hmass (c) (hc : c ∈ recordArrays X r) (S : Finset X.Key) (hS : S ⊆ c.2.2.1) :
      X.blockMass H c.2 S = X.blockMass H' c.2 S :=
    X.blockMass_ext5 H H' c.2 S hb (fun ℓ hℓ => htypes c hc ℓ (hS hℓ))
  have hlaw (c : Fin (X.p.T n) × X.Ty) (hc : c ∈ recordArrays X r)
      (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
      X.blockLaw (X.withCol H r.1 θ) c.2 = X.blockLaw (X.withCol H' r.1 θ) c.2 := by
    exact blockLawOn_ext X (X.withCol H r.1 θ) (X.withCol H' r.1 θ) c.2 c.2.2.1 hb
      (replaced_cols X H H' r.1 θ c.2.2.1 (htypes c hc))
  have hdel (c) (hc : c ∈ recordArrays X r) :
      X.blockLawDel H c.2 r.1 = X.blockLawDel H' c.2 r.1 := by
    exact blockLawOn_ext X H H' c.2 (c.2.2.1.erase r.1) hb
      (fun ℓ hℓ => htypes c hc ℓ (Finset.mem_of_mem_erase hℓ))
  have hhit (c) (hc : c ∈ recordArrays X r) (y) : X.hitSet a c y = X.hitSet a' c y := by
    unfold Setup5.hitSet
    rw [ha c hc]
  have hgate (θ) : X.candGateOn H r a θ = X.candGateOn H' r a' θ := by
    apply propext
    unfold Setup5.candGateOn
    constructor <;> intro hh
    · constructor
      · intro c hc htarget
        have hc' := obs_mem X r c hc
        have hr := X.blockMass_ext5 (X.withCol H r.1 θ) (X.withCol H' r.1 θ)
          c.2 c.2.2.1 hb (replaced_cols X H H' r.1 θ _ (htypes c hc'))
        simpa only [hmass c hc' _ (Finset.erase_subset _ _), hr] using hh.1 c hc htarget
      · intro c M hc h
        simpa only [hhit c (pool_mem X r c M hc)] using hh.2 c M hc h
    · constructor
      · intro c hc htarget
        have hc' := obs_mem X r c hc
        have hr := X.blockMass_ext5 (X.withCol H r.1 θ) (X.withCol H' r.1 θ)
          c.2 c.2.2.1 hb (replaced_cols X H H' r.1 θ _ (htypes c hc'))
        simpa only [hmass c hc' _ (Finset.erase_subset _ _), hr] using hh.1 c hc htarget
      · intro c M hc h
        simpa only [hhit c (pool_mem X r c M hc)] using hh.2 c M hc h
  have hlik (θ excl) : X.obsLikOn H r a θ excl = X.obsLikOn H' r a' θ excl := by
    unfold Setup5.obsLikOn
    apply Finset.prod_congr rfl
    intro c hc
    have hc' := obs_mem X r c (Finset.mem_filter.mp hc).1
    rw [ha c hc', hlaw c hc' θ, hdel c hc']
  have hm (excl) : X.step3MassOn H r a excl = X.step3MassOn H' r a' excl := by
    unfold Setup5.step3MassOn
    rw [hb]
    simp_rw [hgate, hlik]
  have hp (excl θ) : X.step3PostOn H r a excl θ = X.step3PostOn H' r a' excl θ := by
    unfold Setup5.step3PostOn
    rw [hb, hgate, hlik, hm]
  have hsub (c) (hc : c ∈ r.2.2.1) :
      X.refSubsetOn H a (c.1, c.2.1) c.2.2 = X.refSubsetOn H' a' (c.1, c.2.1) c.2.2 := by
    have ha' := hhit (c.1, c.2.1) (ref_mem X r c hc)
    unfold Setup5.refSubsetOn
    split
    · rfl
    · cases ho : c.2.2 with
      | none => rfl
      | some ℓ =>
        cases ℓ with
        | inr i => rfl
        | inl k =>
          have hk : H.2 (.inl k) = H'.2 (.inl k) := by
            apply hcol
            simp only [recordKeys, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
            exact Or.inr (Or.inr ⟨c, hc, by simp [ho]⟩)
          simp only [Setup5.lowCol, hk, ha']
          rfl
  have href : X.refsOn H r a = X.refsOn H' r a' := by
    unfold Setup5.refsOn
    apply Finset.image_congr
    intro c hc
    change (c.1, c.2.1, X.refSubsetOn H a (c.1, c.2.1) c.2.2) =
      (c.1, c.2.1, X.refSubsetOn H' a' (c.1, c.2.1) c.2.2)
    rw [hsub c hc]
  have hpf (excl) : X.step3PostOn H r a excl = X.step3PostOn H' r a' excl := funext (hp excl)
  have hs (h) : X.highSource H r a h = X.highSource H' r a' h := by
    unfold Setup5.highSource
    rw [hpf, ht]
  have hd (c h) : X.highDeleted H r a c h = X.highDeleted H' r a' c h := by
    unfold Setup5.highDeleted
    rw [hpf, ht]
  have hcap : X.HighCapped H r a = X.HighCapped H' r a' := by
    simp only [Setup5.HighCapped, hs]
  have hprice : X.HighPriceFeasible H r a = X.HighPriceFeasible H' r a' := by
    unfold Setup5.HighPriceFeasible
    rw [href]
    simp only [hs, hd]
  simp only [Setup5.step3FailOn, ht, hgate, hm, href, hcap, hprice]

theorem step3Fail_array_depends (H : X.KeyHist) (r : X.AbsRecord) :
    FinProb.DependsOn (X.step3FailOn H r) (recordArrays X r) := by
  intro a a' ha
  exact step3Fail_ext X H H r a a' rfl (fun _ _ => rfl) ha

/-- The unused arrays integrate to one, even if their kernels change. -/
theorem step3Rate_ext (H H' : X.KeyHist) (r : X.AbsRecord) (hb : H.1 = H'.1)
    (hc : ∀ ℓ ∈ recordKeys X r, H.2 ℓ = H'.2 ℓ) :
    X.step3Rate H r = X.step3Rate H' r := by
  let F := fun a => if X.step3FailOn H r a then (1 : ℝ) else 0
  let F' := fun a => if X.step3FailOn H' r a then (1 : ℝ) else 0
  have hF : FinProb.DependsOn F (recordArrays X r) := by
    intro a a' ha
    dsimp [F]
    rw [step3Fail_array_depends X H r a a' ha]
  have hF' : FinProb.DependsOn F' (recordArrays X r) := by
    intro a a' ha
    dsimp [F']
    rw [step3Fail_array_depends X H' r a a' ha]
  have hFeq : F = F' := by
    funext a
    dsimp [F, F']
    rw [step3Fail_ext X H H' r a a hb hc (fun _ _ => rfl)]
  have hlaw (c : recordArrays X r) :
      FinProb.pi (fun _ : Fin (X.p.typeBlocks n c.1.2) => X.blockLaw H c.1.2) =
      FinProb.pi (fun _ : Fin (X.p.typeBlocks n c.1.2) => X.blockLaw H' c.1.2) := by
    congr 1
    funext i
    apply blockLawOn_ext X H H' c.1.2 _ hb
    intro ℓ hℓ
    apply hc
    simp only [recordKeys, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inr (Or.inl ⟨c.1, c.2, hℓ⟩)
  change (X.recArrayLaw H).pr _ = (X.recArrayLaw H').pr _
  have hpr : ∀ P : FinProb (X.ArraysOn (Fin (X.p.T n))), ∀ B,
      P.pr B = P.expect (fun a => if B a then (1 : ℝ) else 0) := by
    intro P B
    simp only [FinProb.pr, FinProb.expect, mul_ite, mul_one, mul_zero]
  rw [hpr, hpr]
  change (FinProb.pi _).expect F = (FinProb.pi _).expect F'
  rw [FinProb.pi_expect_depends _ _ F (fun _ _ _ _ => X.y₀) hF,
    FinProb.pi_expect_depends _ _ F' (fun _ _ _ _ => X.y₀) hF']
  simp_rw [hlaw, hFeq]

def recordLowScope (r : X.AbsRecord) : Finset (LowCoordinates X) :=
  Finset.univ.filter fun k => Sum.inl k ∈ recordKeys X r

theorem step3_low_depends (b : X.Base)
    (hi : CoarseKey5 n → Fin (X.p.s n) → Fin N) (r : X.AbsRecord) :
    FinProb.DependsOn
      (fun lo : LowCoordinates X → Fin 1 → Fin N =>
        X.step3Rate (b, fun ℓ => match ℓ with | .inl k => lo k | .inr i => hi i) r)
      (recordLowScope X r) := by
  intro lo lo' h
  refine step3Rate_ext X
    (b, fun ℓ => match ℓ with | .inl k => lo k | .inr i => hi i)
    (b, fun ℓ => match ℓ with | .inl k => lo' k | .inr i => hi i) r rfl ?_
  intro ℓ hℓ
  cases ℓ with
  | inl k => exact h k (by simp [recordLowScope, hℓ])
  | inr i => rfl

/-- The pretrim loss for a record is charged only to its low scope. -/
theorem step3_pretrim_mean (b : X.Base)
    (hi : CoarseKey5 n → Fin (X.p.s n) → Fin N) (tr : LowCoordinates X → Law N)
    (htr : ∀ k y, (tr k).w y ≤ 2 * (X.prior b (.inl k)).w y) (r : X.AbsRecord) :
    (FinProb.pi (fun k : LowCoordinates X => FinProb.pi (fun _ : Fin 1 => tr k))).expect
      (fun lo => X.step3Rate (b, fun ℓ => match ℓ with | .inl k => lo k | .inr i => hi i) r) ≤
    (2 : ℝ) ^ (recordLowScope X r).card *
      (FinProb.pi (fun k : LowCoordinates X =>
        FinProb.pi (fun _ : Fin 1 => X.prior b (.inl k)))).expect
        (fun lo => X.step3Rate (b, fun ℓ => match ℓ with | .inl k => lo k | .inr i => hi i) r) := by
  apply pi_expect_density_scope _ _ (recordLowScope X r) 2 (by norm_num) _ _ _
    (step3_low_depends X b hi r) (fun _ _ => X.y₀)
  · intro k hk θ
    simpa only [FinProb.pi, Fintype.prod_unique] using htr k (θ default)
  · intro lo
    unfold Setup5.step3Rate FinProb.pr
    exact Finset.sum_nonneg fun a ha => by split_ifs <;> simp [(X.recArrayLaw _).nonneg]

/-- References and an interface pool use arrays already present in the observation list. -/
theorem occurring_record_arrays (r : X.AbsRecord) (hr : X.RecOccurs r) :
    recordArrays X r = r.2.1 := by
  obtain ⟨y, μ, htarget, hobs, hrefs, hpool⟩ := hr
  apply Finset.Subset.antisymm
  · intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact hc
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
        have hd' := Eq.mp (congrArg (fun S => d ∈ S) hrefs) hd
        have hd'' := by
          letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
          exact Finset.mem_image.mp hd'
        obtain ⟨a, ha, he⟩ := hd''
        subst d
        rw [hobs]
        exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, rfl⟩
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      have hp : r.2.2.2 = some d := Option.mem_def.mp (Option.mem_toFinset.mp hd)
      rw [hp] at hpool
      obtain ⟨a, ha, hK, hi⟩ := hpool.2
      rw [hobs]
      refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
      exact Prod.ext hi.2.1.symm hK.symm
  · intro c hc
    exact obs_mem X r c hc

/-- A low target fixes both the central sign and the central severity of its record. -/
theorem low_record_central (r : X.AbsRecord) (hr : X.RecOccurs r)
    (k : LowCoordinates X) (hk : r.1 = .inl k) :
    X.RecOccursAt r k.2.1 k.2.2.val := by
  obtain ⟨y, μ, hy⟩ := hr
  have htarget := hy.1.trans hk
  have hlow : X.g.severity y.1 ≤ X.p.J n := by
    by_contra hh
    simp only [ChunkGeometry5.roleKey, hh, dite_eq_right] at htarget
    cases htarget
  have htuple :
      (X.g.key y.1, X.g.sign y.1, (⟨X.g.severity y.1, Nat.lt_succ_of_le hlow⟩ : Fin (X.p.J n + 1))) = k := by
    exact Sum.inl.inj (by simpa only [ChunkGeometry5.roleKey, dite_eq_left hlow] using htarget)
  refine ⟨y, μ, hy, ?_, ?_⟩
  · exact congrArg (fun k : LowCoordinates X => k.2.1) htuple
  · exact congrArg (fun k : LowCoordinates X => k.2.2.val) htuple

end
end HypercubeRamsey.Lane_sol_s05_h5l
