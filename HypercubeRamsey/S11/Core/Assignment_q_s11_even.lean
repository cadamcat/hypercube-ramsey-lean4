import HypercubeRamsey.S11.Core.Experiment

namespace HypercubeRamsey.Lane_q_s11_even

open HypercubeRamsey.S11.Core
open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

private def pairFlip {n : ℕ} (v : CubeVertex n) (S : Finset (Fin n)) : CubeVertex n :=
  fun j => if j ∈ S then !v j else v j

private noncomputable def pairRole {n : ℕ} (v : EvenRole n) (P : Pair (InnerCoord n)) : EvenRole n := by
  classical
  let S : Finset (Fin n) := P.1.image Subtype.val
  let hpair : ∃ a b : InnerCoord n, a ≠ b ∧ P.1 = {a, b} :=
    Finset.card_eq_two.mp P.2
  let a : InnerCoord n := Classical.choose hpair
  let b : InnerCoord n := Classical.choose (Classical.choose_spec hpair)
  have hab : a ≠ b := (Classical.choose_spec (Classical.choose_spec hpair)).1
  have hP : P.1 = {a, b} := (Classical.choose_spec (Classical.choose_spec hpair)).2
  have hS : S = {a.1, b.1} := by
    simp [S, hP]
  have hne : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  have hflip : pairFlip v.1 S = cubeFlip (cubeFlip v.1 a.1) b.1 := by
    funext j
    by_cases hja : j = a.1
    · subst j
      simp [pairFlip, S, hS, cubeFlip, Function.update_of_ne hne]
    · by_cases hjb : j = b.1
      · subst j
        simp [pairFlip, S, hS, cubeFlip, Function.update_of_ne (Ne.symm hne)]
      · simp_all [pairFlip, S, hS, cubeFlip,
          Function.update_of_ne hja, Function.update_of_ne hjb]
  refine ⟨pairFlip v.1 S, ?_⟩
  rw [hflip]
  have hfirst : ¬ IsEvenRole (cubeFlip v.1 a.1) := by
    intro he
    exact (cubeFlip_parity v.1 a.1).mp he v.2
  exact (cubeFlip_parity (cubeFlip v.1 a.1) b.1).mpr hfirst

private theorem pairRole_slice {n : ℕ} (v : EvenRole n) (P : Pair (InnerCoord n)) :
    sliceOf (pairRole v P).1 = sliceOf v.1 := by
  classical
  funext j
  have hnot : j.1 ∉ P.1.image Subtype.val := by
    intro hj
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hj
    have hlt := a.2
    have hval : a.1 = j.1 := hEq
    omega
  simp [sliceOf, pairRole, pairFlip, hnot]

private theorem pairRole_support {n : ℕ} (v : EvenRole n) (P : Pair (InnerCoord n)) :
    Finset.univ.filter (fun j : Fin n => v.1 j ≠ (pairRole v P).1 j) =
      P.1.image Subtype.val := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (v.1 j ≠ pairFlip v.1 (P.1.image Subtype.val) j) ↔
    j ∈ P.1.image Subtype.val
  by_cases hj : j ∈ P.1.image Subtype.val
  · have hflip : pairFlip v.1 (P.1.image Subtype.val) j = !v.1 j := by
      simp [pairFlip, hj]
    rw [hflip]
    constructor
    · intro _
      exact hj
    · intro _
      cases hv : v.1 j <;> simp [hv]
  · have hsame : pairFlip v.1 (P.1.image Subtype.val) j = v.1 j := by
      simp [pairFlip, hj]
    rw [hsame]
    constructor
    · intro h
      exact (h rfl).elim
    · intro h
      exact (hj h).elim

private noncomputable def localEvenRole {n : ℕ} (v : EvenRole n)
    (o : Option (Pair (InnerCoord n))) : EvenRole n :=
  match o with
  | none => v
  | some P => pairRole v P

private theorem pairFlip_pair {n : ℕ} (v : CubeVertex n) (a b : Fin n) (hab : a ≠ b) :
    pairFlip v {a, b} = cubeFlip (cubeFlip v a) b := by
  funext j
  by_cases hja : j = a
  · subst j
    simp [pairFlip, cubeFlip, Function.update_of_ne hab]
  · by_cases hjb : j = b
    · subst j
      simp [pairFlip, cubeFlip, Function.update_of_ne (Ne.symm hab)]
    · simp_all [pairFlip, cubeFlip, Function.update_of_ne hja, Function.update_of_ne hjb]

private theorem pairRole_eq_flip {n : ℕ} (v : EvenRole n) (P : Pair (InnerCoord n))
    (a b : InnerCoord n) (hab : a ≠ b) (hP : P.1 = {a, b}) :
    pairRole v P = evenNbr (oddNbr v a.1) b.1 := by
  apply Subtype.ext
  change pairFlip v.1 (P.1.image Subtype.val) = cubeFlip (cubeFlip v.1 a.1) b.1
  have himage : P.1.image Subtype.val = {a.1, b.1} := by simp [hP, hab]
  rw [himage]
  exact pairFlip_pair v.1 a.1 b.1 (by intro h; exact hab (Subtype.ext h))

private theorem localEvenRole_pair {n : ℕ} (v : EvenRole n) (a c : InnerCoord n)
    (hca : c ≠ a) :
    localEvenRole v (some ⟨{a, c}, Finset.card_pair (Ne.symm hca)⟩) =
      evenNbr (oddNbr v a.1) c.1 := by
  exact pairRole_eq_flip v _ a c (Ne.symm hca) rfl

private theorem localEvenRole_slice {n : ℕ} (v : EvenRole n)
    (o : Option (Pair (InnerCoord n))) :
    sliceOf (localEvenRole v o).1 = sliceOf v.1 := by
  cases o with
  | none => rfl
  | some P => exact pairRole_slice v P

private theorem innerFlip_slice {n : ℕ} (v : CubeVertex n) (a : InnerCoord n) :
    sliceOf (cubeFlip v a.1) = sliceOf v := by
  funext j
  have hne : a.1 ≠ j.1 := by
    intro heq
    have hlt := a.2
    have hge := j.2
    rw [heq] at hlt
    omega
  change Function.update v a.1 (!v a.1) j.1 = v j.1
  exact Function.update_of_ne (Ne.symm hne) _ _

private theorem outerFlip_slice {n : ℕ} (v : CubeVertex n) (j : OuterCoord n) :
    sliceOf (cubeFlip v j.1) = flipOuter (sliceOf v) j := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [sliceOf, cubeFlip, flipOuter]
  · have hne : j.1 ≠ k.1 := by
      intro heq
      exact hkj (Subtype.ext heq.symm)
    change Function.update v j.1 (!v j.1) k.1 =
      Function.update (sliceOf v) j (!v j.1) k
    rw [Function.update_of_ne (Ne.symm hne), Function.update_of_ne hkj]
    rfl

private theorem flipOuter_ne_self {n : ℕ} (s : OuterWord n) (j : OuterCoord n) :
    flipOuter s j ≠ s := by
  intro h
  have hj := congrFun h j
  simp [flipOuter] at hj

private theorem flipOuter_ne_of_ne {n : ℕ} (s : OuterWord n) (j k : OuterCoord n) (hjk : j ≠ k) :
    flipOuter s j ≠ flipOuter s k := by
  intro h
  have hj := congrFun h j
  simp [flipOuter, hjk] at hj

private theorem oddNbr_inner_slice {n : ℕ} (v : EvenRole n) (a : InnerCoord n) :
    sliceOf (oddNbr v a.1).1 = sliceOf v.1 := innerFlip_slice v.1 a

private theorem evenNbr_inner_slice {n : ℕ} (b : OddRole n) (a : InnerCoord n) :
    sliceOf (evenNbr b a.1).1 = sliceOf b.1 := innerFlip_slice b.1 a

private theorem oddNbr_outer_slice {n : ℕ} (v : EvenRole n) (j : OuterCoord n) :
    sliceOf (oddNbr v j.1).1 = flipOuter (sliceOf v.1) j := outerFlip_slice v.1 j

private theorem innerStarOf {n k N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (v : EvenRole n) (W : EvenRole n → Fin k → Fin N) (a : InnerCoord n) :
    starOf W (oddNbr v a.1) = ballStar (fun o => W (localEvenRole v o)) a := by
  funext c
  by_cases hc : c = a
  · subst c
    simp [starOf, oddNbr, evenNbr, localEvenRole, ballStar, cubeFlip]
  · have hpair := localEvenRole_pair v a c hc
    have hpair' : pairRole v ⟨{a, c}, Finset.card_pair (Ne.symm hc)⟩ =
        evenNbr (oddNbr v a.1) c.1 := by
      simpa [localEvenRole] using hpair
    simp only [starOf, oddNbr, evenNbr, ballStar, localEvenRole, dif_neg hc]
    exact (congrArg W hpair').symm

private noncomputable def oddStarScope {n : ℕ} (v : EvenRole n) : Option (OuterCoord n) → Finset (OddRole n)
  | none => Finset.univ.image fun a : InnerCoord n => oddNbr v a.1
  | some j => {oddNbr v j.1}

private noncomputable def evenStarScope {n : ℕ} (v : EvenRole n) :
    Option (OuterCoord n) → Finset (EvenRole n)
  | none => Finset.univ.image (localEvenRole v)
  | some j => Finset.univ.image fun a : InnerCoord n => evenNbr (oddNbr v j.1) a.1

private theorem oddScope_none_some_disjoint {n : ℕ} (v : EvenRole n) (j : OuterCoord n) :
    Disjoint (oddStarScope v none) (oddStarScope v (some j)) := by
  apply Finset.disjoint_left.mpr
  intro b hb₁ hb₂
  obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hb₁
  have hSingle : b = oddNbr v j.1 := Finset.mem_singleton.mp hb₂
  have hroles : oddNbr v a.1 = oddNbr v j.1 := hEq.trans hSingle
  have hs := congrArg (fun b : OddRole n => sliceOf b.1) hroles
  rw [oddNbr_inner_slice, oddNbr_outer_slice] at hs
  exact (flipOuter_ne_self (sliceOf v.1) j) hs.symm

private theorem oddScope_some_some_disjoint {n : ℕ} (v : EvenRole n) (j k : OuterCoord n)
    (hjk : j ≠ k) : Disjoint (oddStarScope v (some j)) (oddStarScope v (some k)) := by
  apply Finset.disjoint_left.mpr
  intro b hb₁ hb₂
  have hroles : oddNbr v j.1 = oddNbr v k.1 :=
    (Finset.mem_singleton.mp hb₁).symm.trans (Finset.mem_singleton.mp hb₂)
  have hs := congrArg (fun b : OddRole n => sliceOf b.1) hroles
  rw [oddNbr_outer_slice, oddNbr_outer_slice] at hs
  exact (flipOuter_ne_of_ne (sliceOf v.1) j k hjk) hs

private theorem oddScope_disjoint {n : ℕ} (v : EvenRole n) {o o' : Option (OuterCoord n)}
    (hoo' : o ≠ o') : Disjoint (oddStarScope v o) (oddStarScope v o') := by
  cases o with
  | none =>
    cases o' with
    | none => exact (hoo' rfl).elim
    | some j => exact oddScope_none_some_disjoint v j
  | some j =>
    cases o' with
    | none => exact disjoint_comm.mp (oddScope_none_some_disjoint v j)
    | some k =>
      have hjk : j ≠ k := by
        intro h
        exact hoo' (congrArg Option.some h)
      exact oddScope_some_some_disjoint v j k hjk

private theorem evenScope_none_some_disjoint {n : ℕ} (v : EvenRole n) (j : OuterCoord n) :
    Disjoint (evenStarScope v none) (evenStarScope v (some j)) := by
  apply Finset.disjoint_left.mpr
  intro u hu₁ hu₂
  obtain ⟨o, ho, hEq⟩ := Finset.mem_image.mp hu₁
  obtain ⟨a, ha, hEq'⟩ := Finset.mem_image.mp hu₂
  have huEq : localEvenRole v o = evenNbr (oddNbr v j.1) a.1 := hEq.trans hEq'.symm
  have hs := congrArg (fun u : EvenRole n => sliceOf u.1) huEq
  rw [localEvenRole_slice, evenNbr_inner_slice, oddNbr_outer_slice] at hs
  exact (flipOuter_ne_self (sliceOf v.1) j) hs.symm

private theorem evenScope_some_some_disjoint {n : ℕ} (v : EvenRole n) (j k : OuterCoord n)
    (hjk : j ≠ k) : Disjoint (evenStarScope v (some j)) (evenStarScope v (some k)) := by
  apply Finset.disjoint_left.mpr
  intro u hu₁ hu₂
  obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hu₁
  obtain ⟨b, hb, hEq'⟩ := Finset.mem_image.mp hu₂
  have hs := congrArg (fun u : EvenRole n => sliceOf u.1) (hEq.trans hEq'.symm)
  rw [evenNbr_inner_slice, oddNbr_outer_slice, evenNbr_inner_slice, oddNbr_outer_slice] at hs
  exact (flipOuter_ne_of_ne (sliceOf v.1) j k hjk) hs

private theorem evenScope_disjoint {n : ℕ} (v : EvenRole n) {o o' : Option (OuterCoord n)}
    (hoo' : o ≠ o') : Disjoint (evenStarScope v o) (evenStarScope v o') := by
  cases o with
  | none =>
    cases o' with
    | none => exact (hoo' rfl).elim
    | some j => exact evenScope_none_some_disjoint v j
  | some j =>
    cases o' with
    | none => exact disjoint_comm.mp (evenScope_none_some_disjoint v j)
    | some k =>
      have hjk : j ≠ k := by
        intro h
        exact hoo' (congrArg Option.some h)
      exact evenScope_some_some_disjoint v j k hjk

private noncomputable def fullStarScope {n : ℕ} (v : EvenRole n) : Finset (EvenRole n) :=
  insert v (Finset.univ.biUnion fun j : Fin n =>
    Finset.univ.image fun a : InnerCoord n => evenNbr (oddNbr v j) a.1)

private theorem fullStarScope_mem {n : ℕ} (v : EvenRole n) (j : Fin n) (a : InnerCoord n) :
    evenNbr (oddNbr v j) a.1 ∈ fullStarScope v := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

private theorem evenStarScope_subset_fullStarScope {n : ℕ} (v : EvenRole n)
    (o : Option (OuterCoord n)) : evenStarScope v o ⊆ fullStarScope v := by
  classical
  intro u hu
  cases o with
  | none =>
    obtain ⟨key, hkey, hEq⟩ := Finset.mem_image.mp hu
    cases key with
    | none =>
      have huEq : u = v := by simpa [localEvenRole] using hEq.symm
      rw [huEq]
      exact Finset.mem_insert_self _ _
    | some P =>
      obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp P.2
      have hrole : pairRole v P = evenNbr (oddNbr v a.1) b.1 := pairRole_eq_flip v P a b hab hset
      have hEqRole : pairRole v P = u := by simpa [localEvenRole] using hEq
      have hmem : pairRole v P ∈ fullStarScope v := by
        rw [hrole]
        exact fullStarScope_mem v a.1 b
      rw [← hEqRole]
      exact hmem
  | some j =>
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    exact fullStarScope_mem v j.1 a

private theorem fullStarScope_dist_le_two {n : ℕ} (v u : EvenRole n)
    (hu : u ∈ fullStarScope v) : hammingDist v.1 u.1 ≤ 2 := by
  classical
  rcases Finset.mem_insert.mp hu with huv | hu'
  · subst u
    simp [hammingDist]
  · obtain ⟨j, hj, huImage⟩ := Finset.mem_biUnion.mp hu'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp huImage
    have h1 : hammingDist v.1 (oddNbr v j).1 = 1 := by
      change hammingDist v.1 (cubeFlip v.1 j) = 1
      have hadj := cubeFlip_adj v.1 j
      change hammingDist v.1 (cubeFlip v.1 j) = 1 at hadj
      exact hadj
    have h2 : hammingDist (oddNbr v j).1 (evenNbr (oddNbr v j) a.1).1 = 1 := by
      change hammingDist (oddNbr v j).1 (cubeFlip (oddNbr v j).1 a.1) = 1
      have hadj := cubeFlip_adj (oddNbr v j).1 a.1
      change hammingDist (oddNbr v j).1 (cubeFlip (oddNbr v j).1 a.1) = 1 at hadj
      exact hadj
    calc
      hammingDist v.1 (evenNbr (oddNbr v j) a.1).1 ≤
          hammingDist v.1 (oddNbr v j).1 +
            hammingDist (oddNbr v j).1 (evenNbr (oddNbr v j) a.1).1 :=
        hammingDist_triangle v.1 (oddNbr v j).1 (evenNbr (oddNbr v j) a.1).1
      _ ≤ 2 := by omega

private theorem fullStarScope_disjoint_of_separated {n : ℕ} {v w : EvenRole n}
    (hsep : 5 ≤ hammingDist v.1 w.1) : Disjoint (fullStarScope v) (fullStarScope w) := by
  apply Finset.disjoint_left.mpr
  intro u huv huw
  have hv := fullStarScope_dist_le_two v u huv
  have hw := fullStarScope_dist_le_two w u huw
  have hsymm : hammingDist u.1 w.1 = hammingDist w.1 u.1 := by
    unfold hammingDist
    congr 1
    ext j
    simp [ne_comm]
  have hw' : hammingDist u.1 w.1 ≤ 2 := by rw [hsymm]; exact hw
  have hbound : hammingDist v.1 w.1 ≤ 4 := by
    calc
      hammingDist v.1 w.1 ≤ hammingDist v.1 u.1 + hammingDist u.1 w.1 :=
        hammingDist_triangle v.1 u.1 w.1
      _ ≤ 2 + 2 := Nat.add_le_add hv hw'
      _ = 4 := by norm_num
  omega

private theorem fullStarScope_card_le {n : ℕ} (v : EvenRole n) :
    (fullStarScope v).card ≤ 1 + n * Fintype.card (InnerCoord n) := by
  classical
  unfold fullStarScope
  calc
    (insert v (Finset.univ.biUnion fun j : Fin n =>
      Finset.univ.image fun a : InnerCoord n => evenNbr (oddNbr v j) a.1)).card ≤
        (Finset.univ.biUnion fun j : Fin n =>
          Finset.univ.image fun a : InnerCoord n => evenNbr (oddNbr v j) a.1).card + 1 := by
            exact Finset.card_insert_le v _
    _ ≤ (∑ j : Fin n,
          (Finset.univ.image fun a : InnerCoord n => evenNbr (oddNbr v j) a.1).card) + 1 := by
          exact Nat.add_le_add_right (Finset.card_biUnion_le (s := Finset.univ)
            (t := fun j : Fin n =>
              Finset.univ.image fun a : InnerCoord n => evenNbr (oddNbr v j) a.1)) 1
    _ ≤ (∑ _j : Fin n, Fintype.card (InnerCoord n)) + 1 := by
          gcongr with j hj
          exact Finset.card_image_le
    _ = n * Fintype.card (InnerCoord n) + 1 := by simp
    _ = 1 + n * Fintype.card (InnerCoord n) := by omega

private def oddNeighborScope {n : ℕ} (v : EvenRole n) : Finset (OddRole n) :=
  Finset.univ.image fun j : Fin n => oddNbr v j

private theorem hammingDist_symm {n : ℕ} (u w : CubeVertex n) :
    hammingDist u w = hammingDist w u := by
  unfold hammingDist
  congr 1
  ext j
  simp [ne_comm]

private theorem cubeFlip_dist_one {n : ℕ} (u : CubeVertex n) (j : Fin n) :
    hammingDist u (cubeFlip u j) = 1 := by
  have hadj := cubeFlip_adj u j
  change hammingDist u (cubeFlip u j) = 1 at hadj
  exact hadj

private theorem oddNeighborScope_disjoint {n : ℕ} {v w : EvenRole n}
    (hsep : 5 ≤ hammingDist v.1 w.1) : Disjoint (oddNeighborScope v) (oddNeighborScope w) := by
  apply Finset.disjoint_left.mpr
  intro b hbv hbw
  obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hbv
  obtain ⟨k, hk, hEq'⟩ := Finset.mem_image.mp hbw
  have hroles : oddNbr v j = oddNbr w k := hEq.trans hEq'.symm
  have hvb : hammingDist v.1 b.1 = 1 := by
    rw [← hEq]
    exact cubeFlip_dist_one v.1 j
  have hwb : hammingDist w.1 b.1 = 1 := by
    rw [← hEq']
    exact cubeFlip_dist_one w.1 k
  have hbound : hammingDist v.1 w.1 ≤ 2 := by
    calc
      hammingDist v.1 w.1 ≤ hammingDist v.1 b.1 + hammingDist b.1 w.1 :=
        hammingDist_triangle v.1 b.1 w.1
      _ = 2 := by rw [hvb, hammingDist_symm b.1 w.1, hwb]
  omega

private noncomputable def tupleStarFactor {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι)
    (t : OuterWord n → M.ι) (W : EvenRole n → Fin (kTup n) → Fin N)
    (v : EvenRole n) (x : Fin N) : ℝ :=
  ∑ f, oddProdW M t W f * ((N : ℝ) * evenRowF M y₀ p t f v x)

private theorem pi_expect_prod_of_disjoint
    {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (F : I → (∀ i, Ω i) → ℝ) (S : I → Finset ι)
    (hdep : ∀ i, FinProb.DependsOn (F i) (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    (FinProb.pi P).expect (fun ω => ∏ i, F i ω) =
      ∏ i, (FinProb.pi P).expect (F i) := by
  classical
  let law : FinProb (∀ i, Ω i) := FinProb.pi P
  let prodOn (T : Finset I) (ω : ∀ i, Ω i) : ℝ := ∏ i ∈ T, F i ω
  have hFor : ∀ T : Finset I,
      law.expect (prodOn T) = ∏ i ∈ T, law.expect (F i) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [prodOn, law, FinProb.expect, (FinProb.pi P).sum_eq_one]
    | @insert i T hi ih =>
      let scopeT : Finset ι := T.biUnion S
      have hdepT : FinProb.DependsOn (prodOn T) scopeT := by
        intro ω ω' hω
        apply Finset.prod_congr rfl
        intro j hj
        apply hdep j ω ω'
        intro k hk
        exact hω k (Finset.mem_biUnion.mpr ⟨j, hj, hk⟩)
      have hscoped : Disjoint (S i) scopeT := by
        apply Finset.disjoint_left.mpr
        intro u hu huT
        obtain ⟨j, hj, huJ⟩ := Finset.mem_biUnion.mp huT
        have hij : i ≠ j := by
          intro heq
          subst j
          exact hi hj
        exact Finset.disjoint_left.mp (hdisj i j hij) hu huJ
      have hmul := FinProb.pi_expect_mul_of_disjoint P (F i) (prodOn T)
        (S i) scopeT (hdep i) hdepT hscoped
      have hprod (ω : ∀ i, Ω i) : prodOn (insert i T) ω = F i ω * prodOn T ω := by
        simp [prodOn, hi]
      calc
        law.expect (prodOn (insert i T)) = law.expect (fun ω => F i ω * prodOn T ω) := by
          congr 1
          funext ω
          exact hprod ω
        _ = law.expect (F i) * law.expect (prodOn T) := hmul
        _ = law.expect (F i) * ∏ j ∈ T, law.expect (F j) := by rw [ih]
        _ = ∏ j ∈ insert i T, law.expect (F j) := by simp [hi]
  simpa [law, prodOn] using hFor (Finset.univ : Finset I)

private theorem pi_expect_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (g : Ω i → ℝ) :
    (FinProb.pi P).expect (fun ω => g (ω i)) = (P i).expect g := by
  classical
  let s : Finset ι := {i}
  let i0 : {j // j ∈ s} := ⟨i, by simp [s]⟩
  let eIndex : {j // j ∈ s} ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => i0
    left_inv := by
      intro j
      have hj : j.1 = i := Finset.mem_singleton.mp (by change j.1 ∈ ({i} : Finset ι); exact j.2)
      exact Subtype.ext hj.symm
    right_inv := by intro u; cases u; rfl
  }
  have indexEq (j : {j // j ∈ s}) : j.1 = i :=
    Finset.mem_singleton.mp (by change j.1 ∈ ({i} : Finset ι); exact j.2)
  let ePi : ((j : {j // j ∈ s}) → Ω j.1) ≃ Ω i := {
    toFun := fun a => a i0
    invFun := fun x j => Eq.mp (congrArg Ω (indexEq j).symm) x
    left_inv := by
      intro a
      funext j
      have hj : j = i0 := Subtype.ext (indexEq j)
      rw [hj]
      simp [i0, indexEq]
    right_inv := by
      intro x
      simp [i0, indexEq]
  }
  let gSub (a : (j : {j // j ∈ s}) → Ω j.1) : ℝ := g (a i0)
  have hMarg := FinProb.pi_marginal_expect P s gSub
  have hleft : (fun ω : (j : ι) → Ω j =>
      gSub (fun j : {j // j ∈ s} => ω j.1)) = fun ω : (j : ι) → Ω j => g (ω i) := by
    funext ω
    simp [gSub, i0]
  have hsub :
      (FinProb.pi (fun j : {j // j ∈ s} => P j.1)).expect gSub = (P i).expect g := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi.symm]
    apply Finset.sum_congr rfl
    intro x hx
    have hprod' :
        (∏ j : {j // j ∈ s}, (P j.1).w (ePi.symm x j)) =
          ∏ u : Unit, (P (eIndex.symm u).1).w (ePi.symm x (eIndex.symm u)) :=
      Fintype.prod_equiv eIndex _ _ (by
        intro j
        have hj : j = i0 := Subtype.ext (indexEq j)
        rw [hj]
        simp [eIndex])
    have hprod :
        (∏ u : Unit, (P (eIndex.symm u).1).w (ePi.symm x (eIndex.symm u))) = (P i).w x := by
      simp [eIndex, ePi, i0]
    simp only [FinProb.pi, hprod'.trans hprod]
    simp [gSub, ePi, i0]
  calc
    (FinProb.pi P).expect (fun ω => g (ω i)) =
        (FinProb.pi P).expect (fun ω => gSub (fun j => ω j.1)) := by rw [hleft]
    _ = (FinProb.pi (fun j : {j // j ∈ s} => P j.1)).expect gSub := hMarg
    _ = (P i).expect g := hsub

private theorem localEvenRole_injective {n : ℕ} (v : EvenRole n) :
    Function.Injective (localEvenRole v) := by
  classical
  intro o₁ o₂ h
  cases o₁ with
  | none =>
    cases o₂ with
    | none => rfl
    | some P =>
      have hv : v.1 = (pairRole v P).1 := congrArg Subtype.val h
      have hempty :
          Finset.univ.filter (fun j : Fin n => v.1 j ≠ (pairRole v P).1 j) = ∅ := by
        simp [hv]
      rw [pairRole_support] at hempty
      have hpos : 0 < P.1.card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have hmem : a.1 ∈ P.1.image Subtype.val := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      rw [hempty] at hmem
      simp at hmem
  | some P =>
    cases o₂ with
    | none =>
      have hv : (pairRole v P).1 = v.1 := congrArg Subtype.val h
      have hempty :
          Finset.univ.filter (fun j : Fin n => v.1 j ≠ (pairRole v P).1 j) = ∅ := by
        simp [hv]
      rw [pairRole_support] at hempty
      have hpos : 0 < P.1.card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have hmem : a.1 ∈ P.1.image Subtype.val := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      rw [hempty] at hmem
      simp at hmem
    | some Q =>
      have hroles : pairRole v P = pairRole v Q := h
      have hsets : P.1.image Subtype.val = Q.1.image Subtype.val := by
        have hh := congrArg (fun z : EvenRole n =>
          Finset.univ.filter (fun j : Fin n => v.1 j ≠ z.1 j)) hroles
        rw [pairRole_support, pairRole_support] at hh
        exact hh
      have hpq : P.1 = Q.1 := by
        apply Finset.ext
        intro a
        constructor
        · intro ha
          have hmem : a.1 ∈ Q.1.image Subtype.val := by
            rw [← hsets]
            exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
          obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem
          have heq : a = b := Subtype.ext hba.symm
          simpa [heq] using hb
        · intro ha
          have hmem : a.1 ∈ P.1.image Subtype.val := by
            rw [hsets]
            exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
          obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem
          have heq : a = b := Subtype.ext hba.symm
          simpa [heq] using hb
      exact congrArg some (Subtype.ext hpq)

theorem meanOddRow_raw {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι)
    (b : OddRole n) (hS : SliceFacts M y₀) (y : Fin N) :
    (rawTuples M y₀ t).expect (fun W => oddRowF M t W b y) =
      piRow M y₀ (t (sliceOf b.1)) y := by
  classical
  let η : InnerCoord n → EvenRole n := fun a => evenNbr b a.1
  have hη : Function.Injective η := by
    intro a c hac
    apply Subtype.ext
    by_contra hne
    have hval : cubeFlip b.1 a.1 = cubeFlip b.1 c.1 := congrArg Subtype.val hac
    have hcoord := congrArg (fun z : CubeVertex n => z a.1) hval
    have hne' : a.1 ≠ c.1 := by
      intro heq
      exact hne heq
    cases hb : b.1 a.1 <;>
      simp [cubeFlip, hb, Function.update_of_ne hne'] at hcoord
  let U : Finset (EvenRole n) := Finset.univ.image η
  let ηU : InnerCoord n → {u // u ∈ U} := fun a =>
    ⟨η a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hηU : Function.Bijective ηU := by
    constructor
    · intro a c hac
      exact hη (congrArg Subtype.val hac)
    · intro u
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp u.2
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact hEq
  let e : InnerCoord n ≃ {u // u ∈ U} := Equiv.ofBijective ηU hηU
  let Q : EvenRole n → FinProb (Fin (kTup n) → Fin N) := fun u =>
    tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n)
  let G : (∀ u : {u // u ∈ U}, Fin (kTup n) → Fin N) → ℝ := fun V =>
    oddRowW E M.G (gS n) (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1)))
      (fun a => V (e a)) y
  have hpi := FinProb.pi_marginal_expect Q U G
  let QI : InnerCoord n → FinProb (Fin (kTup n) → Fin N) := fun a => Q (η a)
  have hchange :
      (FinProb.pi (fun u : {u // u ∈ U} => Q u.1)).expect G =
        (FinProb.pi QI).expect (fun V => oddRowW E M.G (gS n)
          (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1))) V y) := by
    classical
    let ePi : (∀ a : InnerCoord n, Fin (kTup n) → Fin N) ≃
        (∀ u : {u // u ∈ U}, Fin (kTup n) → Fin N) := {
      toFun := fun V u => V (e.symm u)
      invFun := fun V a => V (e a)
      left_inv := by intro V; funext a; simp
      right_inv := by intro V; funext u; simp
    }
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi]
    apply Finset.sum_congr rfl
    intro V hV
    have hprod' :
        (∏ a : InnerCoord n, (Q (e a).1).w (ePi V (e a))) =
          ∏ u : {u // u ∈ U}, (Q u.1).w (ePi V u) :=
      Fintype.prod_equiv e _ _ (by intro a; simp [ePi])
    have hprod :
        (∏ u : {u // u ∈ U}, (Q u.1).w (ePi V u)) =
          ∏ a : InnerCoord n, (QI a).w (V a) := by
      simpa [QI, e, ηU, ePi] using hprod'.symm
    have heval : G (ePi V) = oddRowW E M.G (gS n)
        (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1))) V y := by
      simp [G, ePi]
    simpa only [FinProb.pi, hprod, heval]
  change (FinProb.pi Q).expect (fun W => G (fun u => W u.1)) = _
  rw [hpi, hchange]
  have hslice (a : InnerCoord n) : sliceOf (evenNbr b a.1).1 = sliceOf b.1 := by
    funext j
    have hne : a.1 ≠ j.1 := by
      intro heq
      have hlt := a.2
      have hge := j.2
      rw [heq] at hlt
      omega
    change Function.update b.1 a.1 (!b.1 a.1) j.1 = b.1 j.1
    exact Function.update_of_ne (Ne.symm hne) _ _
  simp [QI, Q, η, FinProb.expect, FinProb.pi, G, e, ηU,
    piRow, meanOddRow, starW, tupW, tupLaw, oddRowF, starOf, hslice]

theorem inner_output_sum {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι)
    (v : EvenRole n) (W : EvenRole n → Fin (kTup n) → Fin N)
    (hS : SliceFacts M y₀) (x : Fin N) :
    ∑ f, oddProdW M t W f *
        ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x) =
      ∑ z : InnerCoord n → Fin N,
        (∏ a, oddRowF M t W (oddNbr v a.1) (z a)) *
          ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x) := by
  classical
  let η : InnerCoord n → OddRole n := fun a => oddNbr v a.1
  have hη : Function.Injective η := by
    intro a c hac
    apply Subtype.ext
    by_contra hne
    have hval : cubeFlip v.1 a.1 = cubeFlip v.1 c.1 := congrArg Subtype.val hac
    have hcoord := congrArg (fun z : CubeVertex n => z a.1) hval
    have hne' : a.1 ≠ c.1 := by
      intro heq
      apply hne
      simp [heq]
    cases hv : v.1 a.1 <;>
      simp [cubeFlip, hv, Function.update_of_ne hne'] at hcoord
  let U : Finset (OddRole n) := Finset.univ.image η
  let ηU : InnerCoord n → {b // b ∈ U} := fun a =>
    ⟨η a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hηU : Function.Bijective ηU := by
    constructor
    · intro a c hac
      exact hη (congrArg Subtype.val hac)
    · intro b
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp b.2
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact hEq
  let e : InnerCoord n ≃ {b // b ∈ U} := Equiv.ofBijective ηU hηU
  let rowLaw (b : OddRole n) : FinProb (Fin N) := {
    w := oddRowF M t W b
    nonneg := (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b)
    sum_eq_one := (hS.rows (t (sliceOf b.1))).row_sum (starOf W b)
  }
  let rawOdd : FinProb (OddRole n → Fin N) := FinProb.pi rowLaw
  let restrict (f : OddRole n → Fin N) (b : {b // b ∈ U}) : Fin N := f b.1
  let innerFun (o : ∀ b : {b // b ∈ U}, Fin N) : ℝ :=
    (N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (fun a => o (ηU a)) x
  let val (f : OddRole n → Fin N) : ℝ :=
    (N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x
  have hval (f : OddRole n → Fin N) : val f = innerFun (restrict f) := by
    unfold val innerFun innerOut restrict
    congr 1
  have hMarginal := FinProb.pi_marginal_expect rowLaw U innerFun
  let QI (a : InnerCoord n) : FinProb (Fin N) := rowLaw (η a)
  let G (z : InnerCoord n → Fin N) : ℝ :=
    (N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x
  let ePi : (InnerCoord n → Fin N) ≃ ((b : {b // b ∈ U}) → Fin N) := {
    toFun := fun z b => z (e.symm b)
    invFun := fun z a => z (e a)
    left_inv := by intro z; funext a; simp
    right_inv := by intro z; funext b; simp
  }
  have hchange :
      (FinProb.pi (fun b : {b // b ∈ U} => rowLaw b.1)).expect innerFun =
        (FinProb.pi QI).expect G := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi]
    apply Finset.sum_congr rfl
    intro z hz
    have hprod' :
        (∏ a : InnerCoord n, (rowLaw (e a).1).w (ePi z (e a))) =
          ∏ b : {b // b ∈ U}, (rowLaw b.1).w (ePi z b) :=
      Fintype.prod_equiv e _ _ (by intro a; simp [ePi])
    have hprod :
        (∏ b : {b // b ∈ U}, (rowLaw b.1).w (ePi z b)) =
          ∏ a : InnerCoord n, (QI a).w (z a) := by
      simpa [QI, e, ηU, ePi] using hprod'.symm
    have heval : innerFun (ePi z) = G z := by
      simp [innerFun, G, ePi, ηU, e]
    simpa only [FinProb.pi, hprod, heval]
  calc
    ∑ f, oddProdW M t W f * val f = rawOdd.expect val := by
      simp [FinProb.expect, FinProb.pi, oddProdW, rawOdd, rowLaw, val]
    _ = rawOdd.expect (fun f => innerFun (restrict f)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro f hf
      rw [hval]
    _ = (FinProb.pi (fun b : {b // b ∈ U} => rowLaw b.1)).expect innerFun := hMarginal
    _ = (FinProb.pi QI).expect G := hchange
    _ = ∑ z : InnerCoord n → Fin N,
        (∏ a, oddRowF M t W (oddNbr v a.1) (z a)) *
          ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x) := by
      simp [FinProb.expect, FinProb.pi, η, QI, rowLaw, G]

theorem internal_star_raw {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (t : OuterWord n → M.ι) (v : EvenRole n) (x : Fin N) (hS : SliceFacts M y₀) :
    (rawTuples M y₀ t).expect (fun W =>
      ∑ f, oddProdW M t W f *
        ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x)) =
      (N : ℝ) * alphaRow M y₀ (t (sliceOf v.1)) x := by
  classical
  let η : Option (Pair (InnerCoord n)) → EvenRole n := localEvenRole v
  have hη : Function.Injective η := localEvenRole_injective v
  let U : Finset (EvenRole n) := Finset.univ.image η
  let ηU : Option (Pair (InnerCoord n)) → {u // u ∈ U} := fun o =>
    ⟨η o, Finset.mem_image.mpr ⟨o, Finset.mem_univ _, rfl⟩⟩
  have hηU : Function.Bijective ηU := by
    constructor
    · intro a b hab
      exact hη (congrArg Subtype.val hab)
    · intro u
      obtain ⟨o, ho, hEq⟩ := Finset.mem_image.mp u.2
      refine ⟨o, ?_⟩
      apply Subtype.ext
      exact hEq
  let e : Option (Pair (InnerCoord n)) ≃ {u // u ∈ U} := Equiv.ofBijective ηU hηU
  let Q (u : EvenRole n) : FinProb (Fin (kTup n) → Fin N) :=
    tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n)
  let QI (o : Option (Pair (InnerCoord n))) : FinProb (Fin (kTup n) → Fin N) := Q (η o)
  let restrict (W : EvenRole n → Fin (kTup n) → Fin N) (u : {u // u ∈ U}) := W u.1
  let G (V : ∀ u : {u // u ∈ U}, Fin (kTup n) → Fin N) : ℝ :=
    (N : ℝ) * ∑ z : InnerCoord n → Fin N,
      outW E M.G (gS n) (M.μ (t (sliceOf v.1))) (M.ν (t (sliceOf v.1)))
        (fun o => V (ηU o)) z * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x
  let H (V : Option (Pair (InnerCoord n)) → Fin (kTup n) → Fin N) : ℝ :=
    (N : ℝ) * ∑ z : InnerCoord n → Fin N,
      outW E M.G (gS n) (M.μ (t (sliceOf v.1))) (M.ν (t (sliceOf v.1))) V z *
        sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x
  let ePi : (Option (Pair (InnerCoord n)) → Fin (kTup n) → Fin N) ≃
      (∀ u : {u // u ∈ U}, Fin (kTup n) → Fin N) := {
    toFun := fun V u => V (e.symm u)
    invFun := fun V o => V (e o)
    left_inv := by intro V; funext o; simp
    right_inv := by intro V; funext u; simp
  }
  have hchange :
      (FinProb.pi (fun u : {u // u ∈ U} => Q u.1)).expect G =
        (FinProb.pi QI).expect H := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi]
    apply Finset.sum_congr rfl
    intro V hV
    have hprod' :
        (∏ o : Option (Pair (InnerCoord n)), (Q (e o).1).w (ePi V (e o))) =
          ∏ u : {u // u ∈ U}, (Q u.1).w (ePi V u) :=
      Fintype.prod_equiv e _ _ (by intro o; simp [ePi])
    have hprod :
        (∏ u : {u // u ∈ U}, (Q u.1).w (ePi V u)) =
          ∏ o : Option (Pair (InnerCoord n)), (QI o).w (V o) := by
      simpa [QI, e, ηU, ePi] using hprod'.symm
    have heval : G (ePi V) = H V := by simp [G, H, ePi, ηU, e]
    simpa only [FinProb.pi, hprod, heval]
  have hstar (W : EvenRole n → Fin (kTup n) → Fin N) (a : InnerCoord n) :
      starOf W (oddNbr v a.1) = ballStar (fun o => W (η o)) a := by
    funext c
    by_cases hc : c = a
    · subst c
      simp [starOf, oddNbr, evenNbr, localEvenRole, η, ballStar, cubeFlip]
    · have hpair := localEvenRole_pair v a c hc
      simp [starOf, oddNbr, evenNbr, localEvenRole, η, ballStar, hc, hpair]
  have hpoint (W : EvenRole n → Fin (kTup n) → Fin N) :
      ∑ f, oddProdW M t W f *
          ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x) =
        G (restrict W) := by
    rw [inner_output_sum M y₀ t v W hS x]
    have hV : (fun o => W (ηU o).1) = fun o => W (η o) := by
      funext o
      rfl
    unfold G restrict outW
    rw [hV]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    have hprod :
        (∏ a : InnerCoord n, oddRowF M t W (oddNbr v a.1) (z a)) =
          ∏ a : InnerCoord n,
            oddRowW E M.G (gS n) (M.μ (t (sliceOf v.1))) (M.ν (t (sliceOf v.1)))
              (ballStar (fun o => W (η o)) a) (z a) := by
      apply Finset.prod_congr rfl
      intro a ha
      change oddRowW E M.G (gS n) (M.μ (t (sliceOf (oddNbr v a.1).1)))
        (M.ν (t (sliceOf (oddNbr v a.1).1))) (starOf W (oddNbr v a.1)) (z a) = _
      rw [hstar]
      have hslice : sliceOf (oddNbr v a.1).1 = sliceOf v.1 := by
        funext j
        have hne : a.1 ≠ j.1 := by
          intro heq
          have hlt := a.2
          have hge := j.2
          rw [heq] at hlt
          omega
        change Function.update v.1 a.1 (!v.1 a.1) j.1 = v.1 j.1
        exact Function.update_of_ne (Ne.symm hne) _ _
      rw [hslice]
    rw [hprod]
    ring
  have hMarginal := FinProb.pi_marginal_expect Q U G
  calc
    (rawTuples M y₀ t).expect (fun W =>
      ∑ f, oddProdW M t W f *
        ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x)) =
      (rawTuples M y₀ t).expect (fun W => G (restrict W)) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro W hW
        change (rawTuples M y₀ t).w W *
            (∑ f, oddProdW M t W f *
              ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x)) =
          (rawTuples M y₀ t).w W * G (restrict W)
        rw [hpoint W]
    _ = (FinProb.pi (fun u : {u // u ∈ U} => Q u.1)).expect G := hMarginal
    _ = (FinProb.pi QI).expect H := hchange
    _ = (N : ℝ) * alphaRow M y₀ (t (sliceOf v.1)) x := by
      have hfactor {Ω : Type} [Fintype Ω] (A B : Ω → ℝ) :
          ∑ ω, A ω * ((N : ℝ) * B ω) = (N : ℝ) * ∑ ω, A ω * B ω := by
        calc
          ∑ ω, A ω * ((N : ℝ) * B ω) = ∑ ω, (N : ℝ) * (A ω * B ω) := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
          _ = (N : ℝ) * ∑ ω, A ω * B ω := by rw [← Finset.mul_sum]
      simpa [FinProb.expect, FinProb.pi, QI, Q, H, alphaRow, meanEvenRow,
        ballW, outW, tupLaw, tupW, localEvenRole_slice, η] using
        (hfactor (fun W => ballW E M.G (M.μ (t (sliceOf v.1)))
            (y₀ (t (sliceOf v.1))) W)
          (fun W => ∑ z : InnerCoord n → Fin N,
            outW E M.G (gS n) (M.μ (t (sliceOf v.1))) (M.ν (t (sliceOf v.1))) W z *
          sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x))

theorem full_output_sum {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι)
    (t : OuterWord n → M.ι) (v : EvenRole n) (W : EvenRole n → Fin (kTup n) → Fin N)
    (x : Fin N) (hS : SliceFacts M y₀) :
    ∑ f, oddProdW M t W f * ((N : ℝ) * evenRowF M y₀ p t f v x) =
      ∑ z : Fin n → Fin N,
        (∏ j : Fin n, oddRowF M t W (oddNbr v j) (z j)) *
          ((N : ℝ) * (sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1)))
            (fun a : InnerCoord n => z a.1) x *
              ∏ j : OuterCoord n,
                hit E M.G x (z j.1) / deg E M.G (piBar M y₀ p) x)) := by
  classical
  let η : Fin n → OddRole n := fun j => oddNbr v j
  have hη : Function.Injective η := by
    intro j k hjk
    by_contra hne
    have hval : cubeFlip v.1 j = cubeFlip v.1 k := congrArg Subtype.val hjk
    have hcoord := congrArg (fun z : CubeVertex n => z j) hval
    cases hv : v.1 j <;> simp [cubeFlip, hv, Function.update_of_ne hne] at hcoord
  let U : Finset (OddRole n) := Finset.univ.image η
  let ηU : Fin n → {b // b ∈ U} := fun j =>
    ⟨η j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hηU : Function.Bijective ηU := by
    constructor
    · intro j k hjk
      exact hη (congrArg Subtype.val hjk)
    · intro b
      obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp b.2
      refine ⟨j, ?_⟩
      apply Subtype.ext
      exact hEq
  let e : Fin n ≃ {b // b ∈ U} := Equiv.ofBijective ηU hηU
  let rowLaw (b : OddRole n) : FinProb (Fin N) := {
    w := oddRowF M t W b
    nonneg := (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b)
    sum_eq_one := (hS.rows (t (sliceOf b.1))).row_sum (starOf W b)
  }
  let rawOdd : FinProb (OddRole n → Fin N) := FinProb.pi rowLaw
  let restrict (f : OddRole n → Fin N) (b : {b // b ∈ U}) : Fin N := f b.1
  let innerFun (o : ∀ b : {b // b ∈ U}, Fin N) : ℝ :=
    (N : ℝ) *
      (sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1)))
          (fun a : InnerCoord n => o (ηU a.1)) x *
        ∏ j : OuterCoord n,
          hit E M.G x (o (ηU j.1)) / deg E M.G (piBar M y₀ p) x)
  let val (f : OddRole n → Fin N) : ℝ := (N : ℝ) * evenRowF M y₀ p t f v x
  have hval (f : OddRole n → Fin N) : val f = innerFun (restrict f) := by
    have hinner : innerOut f v = fun a : InnerCoord n => restrict f (ηU a.1) := by
      funext a
      rfl
    unfold val innerFun evenRowF
    rw [hinner]
  let G (z : Fin n → Fin N) : ℝ :=
    (N : ℝ) *
      (sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1)))
          (fun a : InnerCoord n => z a.1) x *
        ∏ j : OuterCoord n,
          hit E M.G x (z j.1) / deg E M.G (piBar M y₀ p) x)
  let QI (j : Fin n) : FinProb (Fin N) := rowLaw (η j)
  let ePi : (Fin n → Fin N) ≃ ((b : {b // b ∈ U}) → Fin N) := {
    toFun := fun z b => z (e.symm b)
    invFun := fun z j => z (e j)
    left_inv := by intro z; funext j; simp
    right_inv := by intro z; funext b; simp
  }
  have hchange :
      (FinProb.pi (fun b : {b // b ∈ U} => rowLaw b.1)).expect innerFun =
        (FinProb.pi QI).expect G := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi]
    apply Finset.sum_congr rfl
    intro z hz
    have hprod' :
        (∏ j : Fin n, (rowLaw (e j).1).w (ePi z (e j))) =
          ∏ b : {b // b ∈ U}, (rowLaw b.1).w (ePi z b) :=
      Fintype.prod_equiv e _ _ (by intro j; simp [ePi])
    have hprod :
        (∏ b : {b // b ∈ U}, (rowLaw b.1).w (ePi z b)) =
          ∏ j : Fin n, (QI j).w (z j) := by
      simpa [QI, e, ηU, ePi] using hprod'.symm
    have heval : innerFun (ePi z) = G z := by simp [innerFun, G, ePi, ηU, e]
    simpa only [FinProb.pi, hprod, heval]
  have hMarginal := FinProb.pi_marginal_expect rowLaw U innerFun
  calc
    ∑ f, oddProdW M t W f * val f = rawOdd.expect val := by
      simp [FinProb.expect, FinProb.pi, oddProdW, rawOdd, rowLaw, val]
    _ = rawOdd.expect (fun f => innerFun (restrict f)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro f hf
      rw [hval]
    _ = (FinProb.pi (fun b : {b // b ∈ U} => rowLaw b.1)).expect innerFun := hMarginal
    _ = (FinProb.pi QI).expect G := hchange
    _ = ∑ z : Fin n → Fin N,
        (∏ j : Fin n, oddRowF M t W (oddNbr v j) (z j)) *
          ((N : ℝ) * (sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1)))
            (fun a : InnerCoord n => z a.1) x *
              ∏ j : OuterCoord n,
                hit E M.G x (z j.1) / deg E M.G (piBar M y₀ p) x)) := by
      simp [FinProb.expect, FinProb.pi, η, QI, rowLaw, G]

private theorem tupleStarFactor_depends {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (t : OuterWord n → M.ι) (v : EvenRole n) (x : Fin N)
    (hS : SliceFacts M y₀) (W W' : EvenRole n → Fin (kTup n) → Fin N)
    (hWW : ∀ u, u ∈ fullStarScope v → W u = W' u) :
    tupleStarFactor M y₀ p t W v x = tupleStarFactor M y₀ p t W' v x := by
  classical
  unfold tupleStarFactor
  rw [full_output_sum M y₀ p t v W x hS, full_output_sum M y₀ p t v W' x hS]
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hstar : starOf W (oddNbr v j) = starOf W' (oddNbr v j) := by
    funext a
    simp only [starOf]
    exact hWW (evenNbr (oddNbr v j) a.1) (fullStarScope_mem v j a)
  simp [oddRowF, hstar]

private theorem odd_output_product {n N m : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (W : EvenRole n → Fin (kTup n) → Fin N) (x : Fin N) (hS : SliceFacts M y₀)
    (a : Fin m → EvenRole n)
    (hsep : ∀ i j, i ≠ j → 5 ≤ hammingDist (a i).1 (a j).1) :
    ∑ f, oddProdW M t W f *
        ∏ i : Fin m, ((N : ℝ) * evenRowF M y₀ p t f (a i) x) =
      ∏ i : Fin m, tupleStarFactor M y₀ p t W (a i) x := by
  classical
  let rowLaw (b : OddRole n) : FinProb (Fin N) := {
    w := oddRowF M t W b
    nonneg := (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b)
    sum_eq_one := (hS.rows (t (sliceOf b.1))).row_sum (starOf W b)
  }
  let labelFactor (i : Fin m) (f : OddRole n → Fin N) : ℝ :=
    (N : ℝ) * evenRowF M y₀ p t f (a i) x
  let scope (i : Fin m) : Finset (OddRole n) := oddNeighborScope (a i)
  have hdep (i : Fin m) : FinProb.DependsOn (labelFactor i) (scope i) := by
    intro f g hfg
    have hin : innerOut f (a i) = innerOut g (a i) := by
      funext j
      exact hfg (oddNbr (a i) j.1)
        (Finset.mem_image.mpr ⟨j.1, Finset.mem_univ _, rfl⟩)
    unfold labelFactor evenRowF
    rw [hin]
    apply congrArg (fun q : ℝ =>
      (N : ℝ) * (sigmaW E M.G (gS n) (M.μ (t (sliceOf (a i).1)))
        (innerOut g (a i)) x * q))
    apply Finset.prod_congr rfl
    intro j hj
    rw [hfg (oddNbr (a i) j.1)
      (Finset.mem_image.mpr ⟨j.1, Finset.mem_univ _, rfl⟩)]
  have hdisj : ∀ i j, i ≠ j → Disjoint (scope i) (scope j) := by
    intro i j hij
    exact oddNeighborScope_disjoint (hsep i j hij)
  have hmeans (i : Fin m) :
      (FinProb.pi rowLaw).expect (labelFactor i) = tupleStarFactor M y₀ p t W (a i) x := by
    simp [FinProb.expect, FinProb.pi, labelFactor, tupleStarFactor, oddProdW, rowLaw]
  have hprod := pi_expect_prod_of_disjoint rowLaw labelFactor scope hdep hdisj
  calc
    ∑ f, oddProdW M t W f * ∏ i : Fin m, ((N : ℝ) * evenRowF M y₀ p t f (a i) x) =
        (FinProb.pi rowLaw).expect (fun f => ∏ i, labelFactor i f) := by
          simp [FinProb.expect, FinProb.pi, oddProdW, rowLaw, labelFactor]
    _ = ∏ i, (FinProb.pi rowLaw).expect (labelFactor i) := hprod
    _ = ∏ i, tupleStarFactor M y₀ p t W (a i) x := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hmeans i

theorem raw_tuple_star_product {n N m : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι)
    (t : OuterWord n → M.ι) (x : Fin N) (hS : SliceFacts M y₀)
    (a : Fin m → EvenRole n)
    (hsep : ∀ i j, i ≠ j → 5 ≤ hammingDist (a i).1 (a j).1) :
    (rawTuples M y₀ t).expect (fun W => ∏ i, tupleStarFactor M y₀ p t W (a i) x) =
      ∏ i, (rawTuples M y₀ t).expect (fun W => tupleStarFactor M y₀ p t W (a i) x) := by
  classical
  let Q : EvenRole n → FinProb (Fin (kTup n) → Fin N) := fun u =>
    tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n)
  let F (i : Fin m) (W : EvenRole n → Fin (kTup n) → Fin N) :=
    tupleStarFactor M y₀ p t W (a i) x
  have hdep : ∀ i, FinProb.DependsOn (F i) (fullStarScope (a i)) := by
    intro i W W' hWW
    exact tupleStarFactor_depends M y₀ p t (a i) x hS W W' hWW
  have hdisj : ∀ i j, i ≠ j → Disjoint (fullStarScope (a i)) (fullStarScope (a j)) := by
    intro i j hij
    exact fullStarScope_disjoint_of_separated (hsep i j hij)
  change (FinProb.pi Q).expect (fun W => ∏ i, F i W) =
    ∏ i, (FinProb.pi Q).expect (F i)
  exact pi_expect_prod_of_disjoint Q F (fun i => fullStarScope (a i)) hdep hdisj

theorem raw_separated_star_product_bound {n N m : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι)
    (t : OuterWord n → M.ι) (hS : SliceFacts M y₀) (hStar : StarMean11 M y₀ p t)
    (x : Fin N) (a : Fin m → EvenRole n)
    (hsep : ∀ i j, i ≠ j → 5 ≤ hammingDist (a i).1 (a j).1) :
    (rawTuples M y₀ t).expect (fun W =>
      ∑ f, oddProdW M t W f * ∏ i : Fin m,
        ((N : ℝ) * evenRowF M y₀ p t f (a i) x)) ≤
      ∏ i : Fin m, compB M y₀ p t (sliceOf (a i).1) x := by
  classical
  have hpi : ∀ y, 0 ≤ piBar M y₀ p y := by
    intro y
    unfold piBar mixW
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (p.nonneg i) ((hS.rows i).pi_nonneg y)
  have hdegBar : ∀ y, 0 ≤ deg E M.G (piBar M y₀ p) y := by
    intro y
    unfold deg
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hpi z) (by unfold hit; split_ifs <;> norm_num)
  have hdegRow : ∀ i y, 0 ≤ deg E M.G (piRow M y₀ i) y := by
    intro i y
    unfold deg
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg ((hS.rows i).pi_nonneg z) (by unfold hit; split_ifs <;> norm_num)
  have hsigma (v : EvenRole n) (f : OddRole n → Fin N) :
      0 ≤ sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x := by
    unfold sigmaW
    split_ifs <;> positivity
  have hrow (f : OddRole n → Fin N) (v : EvenRole n) :
      0 ≤ evenRowF M y₀ p t f v x := by
    unfold evenRowF
    apply mul_nonneg (hsigma v f) ?_
    apply Finset.prod_nonneg
    intro j hj
    exact div_nonneg (by unfold hit; split_ifs <;> norm_num) (hdegBar x)
  have hrowProd (f : OddRole n → Fin N) (W : EvenRole n → Fin (kTup n) → Fin N)
      (i : Fin m) : 0 ≤ (N : ℝ) * evenRowF M y₀ p t f (a i) x :=
    mul_nonneg (Nat.cast_nonneg _) (hrow f (a i))
  have hstarNonneg (i : Fin m) :
      0 ≤ (rawTuples M y₀ t).expect (fun W => tupleStarFactor M y₀ p t W (a i) x) := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro W hW
    apply mul_nonneg ((rawTuples M y₀ t).nonneg W)
    unfold tupleStarFactor
    apply Finset.sum_nonneg
    intro f hf
    apply mul_nonneg
    · unfold oddProdW
      apply Finset.prod_nonneg
      intro b hb
      exact (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b) (f b)
    · exact hrowProd f W i
  have hcompNonneg (i : Fin m) : 0 ≤ compB M y₀ p t (sliceOf (a i).1) x := by
    unfold compB
    apply mul_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) ((hS.alpha (t (sliceOf (a i).1))).nonneg x)
    · apply Finset.prod_nonneg
      intro j hj
      exact div_nonneg
        (hdegRow (t (flipOuter (sliceOf (a i).1) j)) x) (hdegBar x)
  have hpoint (W : EvenRole n → Fin (kTup n) → Fin N) :
      (∑ f, oddProdW M t W f * ∏ i : Fin m,
        ((N : ℝ) * evenRowF M y₀ p t f (a i) x)) =
        ∏ i : Fin m, tupleStarFactor M y₀ p t W (a i) x := by
    exact odd_output_product M y₀ p t W x hS a hsep
  calc
    (rawTuples M y₀ t).expect (fun W =>
        ∑ f, oddProdW M t W f * ∏ i : Fin m,
          ((N : ℝ) * evenRowF M y₀ p t f (a i) x)) =
      (rawTuples M y₀ t).expect (fun W =>
        ∏ i : Fin m, tupleStarFactor M y₀ p t W (a i) x) := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro W hW
          change (rawTuples M y₀ t).w W *
              (∑ f, oddProdW M t W f * ∏ i : Fin m,
                ((N : ℝ) * evenRowF M y₀ p t f (a i) x)) =
            (rawTuples M y₀ t).w W *
              (∏ i : Fin m, tupleStarFactor M y₀ p t W (a i) x)
          rw [hpoint W]
    _ = ∏ i : Fin m,
          (rawTuples M y₀ t).expect (fun W => tupleStarFactor M y₀ p t W (a i) x) :=
        raw_tuple_star_product M y₀ p t x hS a hsep
    _ ≤ ∏ i : Fin m, compB M y₀ p t (sliceOf (a i).1) x := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact hstarNonneg i
          · intro i hi
            simpa [StarMean11, tupleStarFactor] using hStar (a i) x

theorem star_mean_full {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι)
    (t : OuterWord n → M.ι) (hS : SliceFacts M y₀) : StarMean11 M y₀ p t := by
  classical
  intro v x
  let den : ℝ := deg E M.G (piBar M y₀ p) x
  let oddRowLaw (W : EvenRole n → Fin (kTup n) → Fin N) (b : OddRole n) : FinProb (Fin N) := {
    w := oddRowF M t W b
    nonneg := (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b)
    sum_eq_one := (hS.rows (t (sliceOf b.1))).row_sum (starOf W b)
  }
  let oddFactor (W : EvenRole n → Fin (kTup n) → Fin N)
      (o : Option (OuterCoord n)) (f : OddRole n → Fin N) : ℝ :=
    match o with
    | none => (N : ℝ) * sigmaW E M.G (gS n)
        (M.μ (t (sliceOf v.1))) (innerOut f v) x
    | some j => hit E M.G x (f (oddNbr v j.1)) / den
  let innerFactor (W : EvenRole n → Fin (kTup n) → Fin N) : ℝ :=
    ∑ f, oddProdW M t W f *
      ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x)
  let outerFactor (W : EvenRole n → Fin (kTup n) → Fin N) (j : OuterCoord n) : ℝ :=
    ∑ y, oddRowF M t W (oddNbr v j.1) y * (hit E M.G x y / den)
  let tupleFactor (W : EvenRole n → Fin (kTup n) → Fin N)
      (o : Option (OuterCoord n)) : ℝ :=
    match o with
    | none => innerFactor W
    | some j => outerFactor W j
  let tupleLaw (u : EvenRole n) : FinProb (Fin (kTup n) → Fin N) :=
    tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n)
  have hdepOdd (W : EvenRole n → Fin (kTup n) → Fin N) (o : Option (OuterCoord n)) :
      FinProb.DependsOn (oddFactor W o) (oddStarScope v o) := by
    cases o with
    | none =>
      intro f g hfg
      apply congrArg (fun z : InnerCoord n → Fin N =>
        (N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x)
      funext a
      apply hfg (oddNbr v a.1)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    | some j =>
      intro f g hfg
      have hb : f (oddNbr v j.1) = g (oddNbr v j.1) :=
        hfg (oddNbr v j.1) (by simp [oddStarScope])
      simp [oddFactor, hb]
  have hdisjOdd : ∀ o o', o ≠ o' →
      Disjoint (oddStarScope v o) (oddStarScope v o') := fun o o' hoo => oddScope_disjoint v hoo
  have hlabelProduct (W : EvenRole n → Fin (kTup n) → Fin N) (f : OddRole n → Fin N) :
      (∏ o : Option (OuterCoord n), oddFactor W o f) =
        (N : ℝ) * evenRowF M y₀ p t f v x := by
    rw [Fintype.prod_option]
    simp only [oddFactor]
    unfold evenRowF
    ring
  have hinnerLabel (W : EvenRole n → Fin (kTup n) → Fin N) :
      (FinProb.pi (oddRowLaw W)).expect (oddFactor W none) = innerFactor W := by
    simp [FinProb.expect, FinProb.pi, oddFactor, innerFactor, oddProdW, oddRowLaw]
  have houterLabel (W : EvenRole n → Fin (kTup n) → Fin N) (j : OuterCoord n) :
      (FinProb.pi (oddRowLaw W)).expect (oddFactor W (some j)) = outerFactor W j := by
    simpa [FinProb.pi, FinProb.expect, oddFactor, outerFactor, oddRowLaw, den] using
      (pi_expect_coordinate (oddRowLaw W) (oddNbr v j.1)
        (fun y => hit E M.G x y / den))
  have hoddPoint (W : EvenRole n → Fin (kTup n) → Fin N) :
      ∑ f, oddProdW M t W f * ((N : ℝ) * evenRowF M y₀ p t f v x) =
        innerFactor W * ∏ j : OuterCoord n, outerFactor W j := by
    let law : FinProb (OddRole n → Fin N) := FinProb.pi (oddRowLaw W)
    have hprod := pi_expect_prod_of_disjoint (oddRowLaw W) (oddFactor W) (oddStarScope v)
      (hdepOdd W) hdisjOdd
    calc
      ∑ f, oddProdW M t W f * ((N : ℝ) * evenRowF M y₀ p t f v x) =
          law.expect (fun f => ∏ o : Option (OuterCoord n), oddFactor W o f) := by
        simp [FinProb.expect, FinProb.pi, law, oddProdW, oddRowLaw, hlabelProduct]
      _ = ∏ o : Option (OuterCoord n), law.expect (oddFactor W o) := hprod
      _ = innerFactor W * ∏ j : OuterCoord n, outerFactor W j := by
        rw [Fintype.prod_option, hinnerLabel]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        exact houterLabel W j
  have hdepTuple (o : Option (OuterCoord n)) :
      FinProb.DependsOn (fun W => tupleFactor W o) (evenStarScope v o) := by
    cases o with
    | none =>
      intro W W' hWW
      change innerFactor W = innerFactor W'
      unfold innerFactor
      rw [inner_output_sum M y₀ t v W hS x, inner_output_sum M y₀ t v W' hS x]
      apply Finset.sum_congr rfl
      intro z hz
      congr 1
      apply Finset.prod_congr rfl
      intro a ha
      have hlocal : (fun o => W (localEvenRole v o)) = fun o => W' (localEvenRole v o) := by
        funext o
        exact hWW (localEvenRole v o)
          (Finset.mem_image.mpr ⟨o, Finset.mem_univ _, rfl⟩)
      have hstar : starOf W (oddNbr v a.1) = starOf W' (oddNbr v a.1) := by
        rw [innerStarOf M v W a, innerStarOf M v W' a, hlocal]
      simp [oddRowF, hstar]
    | some j =>
      intro W W' hWW
      change outerFactor W j = outerFactor W' j
      unfold outerFactor
      apply Finset.sum_congr rfl
      intro y hy
      have hstar : starOf W (oddNbr v j.1) = starOf W' (oddNbr v j.1) := by
        funext a
        simp only [starOf]
        exact hWW (evenNbr (oddNbr v j.1) a.1)
          (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
      simp [oddRowF, hstar]
  have hdisjTuple : ∀ o o', o ≠ o' →
      Disjoint (evenStarScope v o) (evenStarScope v o') := fun o o' hoo => evenScope_disjoint v hoo
  have htupleProduct := pi_expect_prod_of_disjoint tupleLaw (fun o W => tupleFactor W o)
    (evenStarScope v) hdepTuple hdisjTuple
  have hinnerMean : (rawTuples M y₀ t).expect innerFactor =
      (N : ℝ) * alphaRow M y₀ (t (sliceOf v.1)) x := by
    exact internal_star_raw M y₀ t v x hS
  have houterMean (j : OuterCoord n) :
      (rawTuples M y₀ t).expect (fun W => outerFactor W j) =
        deg E M.G (piRow M y₀ (t (flipOuter (sliceOf v.1) j))) x / den := by
    unfold FinProb.expect outerFactor
    calc
      ∑ W, (rawTuples M y₀ t).w W *
          ∑ y, oddRowF M t W (oddNbr v j.1) y * (hit E M.G x y / den) =
        ∑ y, (∑ W, (rawTuples M y₀ t).w W * oddRowF M t W (oddNbr v j.1) y) *
          (hit E M.G x y / den) := by
            change (∑ W ∈ (Finset.univ : Finset (EvenRole n → Fin (kTup n) → Fin N)),
                (rawTuples M y₀ t).w W *
                  ∑ y ∈ (Finset.univ : Finset (Fin N)),
                    oddRowF M t W (oddNbr v j.1) y * (hit E M.G x y / den)) = _
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro y hy
            calc
              ∑ W ∈ (Finset.univ : Finset (EvenRole n → Fin (kTup n) → Fin N)),
                  (rawTuples M y₀ t).w W *
                    (oddRowF M t W (oddNbr v j.1) y * (hit E M.G x y / den)) =
                (∑ W ∈ (Finset.univ : Finset (EvenRole n → Fin (kTup n) → Fin N)),
                  (rawTuples M y₀ t).w W * oddRowF M t W (oddNbr v j.1) y) *
                    (hit E M.G x y / den) := by
                      calc
                        ∑ W ∈ (Finset.univ : Finset (EvenRole n → Fin (kTup n) → Fin N)),
                            (rawTuples M y₀ t).w W *
                              (oddRowF M t W (oddNbr v j.1) y * (hit E M.G x y / den)) =
                          ∑ W ∈ (Finset.univ : Finset (EvenRole n → Fin (kTup n) → Fin N)),
                            ((rawTuples M y₀ t).w W * oddRowF M t W (oddNbr v j.1) y) *
                              (hit E M.G x y / den) := by
                                apply Finset.sum_congr rfl
                                intro W hW
                                ring
                        _ = _ := by rw [← Finset.sum_mul]
              _ = _ := rfl
      _ = ∑ y, piRow M y₀ (t (flipOuter (sliceOf v.1) j)) y *
            (hit E M.G x y / den) := by
        apply Finset.sum_congr rfl
        intro y hy
        have hmean :
            ∑ W, (rawTuples M y₀ t).w W * oddRowF M t W (oddNbr v j.1) y =
              piRow M y₀ (t (sliceOf (oddNbr v j.1).1)) y := by
          simpa [FinProb.expect] using meanOddRow_raw M y₀ t (oddNbr v j.1) hS y
        rw [hmean]
        rw [oddNbr_outer_slice]
      _ = deg E M.G (piRow M y₀ (t (flipOuter (sliceOf v.1) j))) x / den := by
        calc
          ∑ y, piRow M y₀ (t (flipOuter (sliceOf v.1) j)) y *
              (hit E M.G x y / den) =
              (∑ y, piRow M y₀ (t (flipOuter (sliceOf v.1) j)) y * hit E M.G x y) / den := by
                calc
                  ∑ y, piRow M y₀ (t (flipOuter (sliceOf v.1) j)) y *
                      (hit E M.G x y / den) =
                    ∑ y, (piRow M y₀ (t (flipOuter (sliceOf v.1) j)) y * hit E M.G x y) / den := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      ring
                  _ = _ := by rw [Finset.sum_div]
          _ = _ := rfl
  calc
    (rawTuples M y₀ t).expect (fun W =>
        ∑ f, oddProdW M t W f * ((N : ℝ) * evenRowF M y₀ p t f v x)) =
      (rawTuples M y₀ t).expect (fun W => ∏ o : Option (OuterCoord n), tupleFactor W o) := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro W hW
          change (rawTuples M y₀ t).w W *
              (∑ f, oddProdW M t W f * ((N : ℝ) * evenRowF M y₀ p t f v x)) =
            (rawTuples M y₀ t).w W * (∏ o : Option (OuterCoord n), tupleFactor W o)
          rw [hoddPoint W]
          simp [Fintype.prod_option, tupleFactor]
    _ = ∏ o : Option (OuterCoord n),
          (rawTuples M y₀ t).expect (fun W => tupleFactor W o) := htupleProduct
    _ = (N : ℝ) * alphaRow M y₀ (t (sliceOf v.1)) x *
          ∏ j : OuterCoord n,
            (deg E M.G (piRow M y₀ (t (flipOuter (sliceOf v.1) j))) x / den) := by
          rw [Fintype.prod_option, hinnerMean]
          congr 1
          apply Finset.prod_congr rfl
          intro j hj
          exact houterMean j
    _ ≤ compB M y₀ p t (sliceOf v.1) x := by
          simp [compB, den]

end HypercubeRamsey.Lane_q_s11_even
