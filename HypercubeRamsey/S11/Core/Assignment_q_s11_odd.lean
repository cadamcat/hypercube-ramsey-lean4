import HypercubeRamsey.S11.Core.Experiment
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S07.TagStage

namespace HypercubeRamsey.Lane_q_s11_odd

open HypercubeRamsey HypercubeRamsey.S11.Core OAI.HypercubeRamsey
open Classical
open scoped BigOperators

private def oddNbors {n : ℕ} (v : EvenRole n) : Finset (OddRole n) :=
  Finset.univ.image (oddNbr v)

private noncomputable def oddScope {n : ℕ} (b : OddRole n) : Finset (EvenRole n) :=
  Finset.univ.image (fun a : InnerCoord n => evenNbr b a.1)

private noncomputable def rowLaw11 {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι)
    (W : EvenRole n → Fin (kTup n) → Fin N) (hS : SliceFacts M y₀) (b : OddRole n) : FinProb (Fin N) where
  w := oddRowF M t W b
  nonneg := (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b)
  sum_eq_one := (hS.rows (t (sliceOf b.1))).row_sum (starOf W b)

private theorem finprob_ext {α : Type*} [Fintype α] {P Q : FinProb α}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk pw hp hs =>
    cases Q with
    | mk qw hq hsq =>
      have hw : pw = qw := funext h
      subst qw
      rfl

private lemma pi_expect_eq_on_scope {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (P Q : ∀ i, FinProb (Ω i)) (s : Finset ι) (f : (∀ i, Ω i) → ℝ)
    (hf : FinProb.DependsOn f s) (hPQ : ∀ i ∈ s, P i = Q i) :
    (FinProb.pi P).expect f = (FinProb.pi Q).expect f := by
  classical
  let ω₀ : ∀ i, Ω i := fun i => Classical.choice (inferInstance : Nonempty (Ω i))
  rw [FinProb.pi_expect_depends P s f ω₀ hf, FinProb.pi_expect_depends Q s f ω₀ hf]
  congr 1
  apply finprob_ext
  intro a
  simp only [FinProb.pi]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun R : FinProb (Ω i.1) => R.w (a i)) (hPQ i.1 i.2)

private lemma pi_local_sum_glue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ι) (f : (∀ i, Ω i) → ℝ)
    (hf : FinProb.DependsOn f s) :
    ∀ ω, (∑ a : (∀ i : s, Ω i.1),
      (∏ i : s, (P i.1).w (a i)) * f (S07.glue s ω a)) = (FinProb.pi P).expect f := by
  classical
  intro ω
  let ω₀ : ∀ i, Ω i := fun i => Classical.choice (inferInstance : Nonempty (Ω i))
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  have hval (a : ∀ i : s, Ω i.1) :
      f (S07.glue s ω a) = f (e.symm (a, fun i => ω₀ i.1)) := by
    apply hf
    intro i hi
    simp [S07.glue, e, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have hproj := FinProb.pi_expect_depends P s f ω₀ hf
  have hsum :
      (∑ a : (∀ i : s, Ω i.1),
        (∏ i : s, (P i.1).w (a i)) * f (S07.glue s ω a)) =
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect
        (fun a => f (e.symm (a, fun i => ω₀ i.1))) := by
    simp only [FinProb.expect, FinProb.pi]
    apply Finset.sum_congr rfl
    intro a _
    rw [hval]
  exact hsum.trans hproj.symm

private lemma oddNbr_mem {n : ℕ} (v : EvenRole n) (j : Fin n) : oddNbr v j ∈ oddNbors v :=
  Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

private lemma oddScope_mem {n : ℕ} (b : OddRole n) (a : InnerCoord n) :
    evenNbr b a.1 ∈ oddScope b :=
  Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

private lemma innerNeighbor_inj {n : ℕ} (b : OddRole n) :
    Function.Injective (fun a : InnerCoord n => evenNbr b a.1) := by
  intro a a' haa
  apply Subtype.ext
  by_contra hne
  have heq : cubeFlip b.1 a.1 = cubeFlip b.1 a'.1 := congrArg Subtype.val haa
  have hval : a.1 ≠ a'.1 := hne
  have heval := congrFun heq a.1
  have hleft : cubeFlip b.1 a.1 a.1 = !(b.1 a.1) := by simp [HypercubeRamsey.cubeFlip]
  have hright : cubeFlip b.1 a'.1 a.1 = b.1 a.1 := by
    simp [HypercubeRamsey.cubeFlip, hval]
  rw [hleft, hright] at heval
  cases hv : b.1 a.1 <;> simp [hv] at heval

private noncomputable def innerScopeEquiv {n : ℕ} (b : OddRole n) :
    InnerCoord n ≃ {u : EvenRole n // u ∈ oddScope b} where
  toFun a := ⟨evenNbr b a.1, oddScope_mem b a⟩
  invFun u := Classical.choose (Finset.mem_image.mp u.2)
  left_inv := by
    intro a
    apply innerNeighbor_inj
    exact (Classical.choose_spec (Finset.mem_image.mp (oddScope_mem b a))).2
  right_inv := by
    intro u
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp u.2)).2

private lemma innerNeighbor_slice {n : ℕ} (b : OddRole n) (a : InnerCoord n) :
    sliceOf (evenNbr b a.1).1 = sliceOf b.1 := by
  funext j
  have hne : a.1 ≠ j.1 := by
    intro heq
    have hleft : a.1.val < hIn n := a.2
    have hright : hIn n ≤ j.1.val := j.2
    rw [← heq] at hright
    omega
  change Function.update b.1 a.1 (!b.1 a.1) j.1 = b.1 j.1
  exact Function.update_of_ne hne.symm _ _

private lemma oddRow_depends_on_scope {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (t : OuterWord n → M.ι) (b : OddRole n) (y : Fin N) :
    FinProb.DependsOn (fun W => oddRowF M t W b y) (oddScope b) := by
  intro W W' hW
  have hstar : starOf W b = starOf W' b := by
    funext a
    exact hW _ (oddScope_mem b a)
  simp [oddRowF, hstar]

private lemma oddScopes_disjoint_of_sep {n : ℕ} (b c : OddRole n)
    (hsep : 3 ≤ hammingDist b.1 c.1) : Disjoint (oddScope b) (oddScope c) := by
  apply Finset.disjoint_left.mpr
  intro u hb hc
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hb
  obtain ⟨a', _, ha'⟩ := Finset.mem_image.mp hc
  have hdist1 : hammingDist b.1 u.1 = 1 := by
    rw [← ha]
    have h := HypercubeRamsey.cubeFlip_adj b.1 a.1
    change hammingDist b.1 (cubeFlip b.1 a.1) = 1 at h
    exact h
  have hdist2 : hammingDist c.1 u.1 = 1 := by
    rw [← ha']
    have h := HypercubeRamsey.cubeFlip_adj c.1 a'.1
    change hammingDist c.1 (cubeFlip c.1 a'.1) = 1 at h
    exact h
  have hbc : hammingDist b.1 c.1 ≤ 2 := by
    calc
      hammingDist b.1 c.1 ≤ hammingDist b.1 u.1 + hammingDist u.1 c.1 :=
        HypercubeRamsey.hammingDist_triangle _ _ _
      _ ≤ 1 + 1 := Nat.add_le_add hdist1.le (by
        simpa [HypercubeRamsey.hammingDist, ne_comm] using hdist2.le)
      _ = 2 := by norm_num
  omega

private lemma rawOddRow_mean {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι) (hS : SliceFacts M y₀)
    (hN : 0 < N) (b : OddRole n) (y : Fin N) :
    (rawTuples M y₀ t).expect (fun W => oddRowF M t W b y) =
      piRow M y₀ (t (sliceOf b.1)) y := by
  classical
  let P : EvenRole n → FinProb (Fin (kTup n) → Fin N) := fun v =>
    tupLaw E M.G (M.μ (t (sliceOf v.1))) (y₀ (t (sliceOf v.1))) (kTup n)
  let φ : (EvenRole n → Fin (kTup n) → Fin N) → ℝ := fun W => oddRowF M t W b y
  let ω₀ : EvenRole n → Fin (kTup n) → Fin N := fun _ _ => ⟨0, hN⟩
  have hdep : FinProb.DependsOn φ (oddScope b) := oddRow_depends_on_scope M t b y
  have hproj := FinProb.pi_expect_depends P (oddScope b) φ ω₀ hdep
  let extension : (∀ u : {u : EvenRole n // u ∈ oddScope b}, Fin (kTup n) → Fin N) →
      (EvenRole n → Fin (kTup n) → Fin N) := fun a =>
        (Equiv.piEquivPiSubtypeProd (fun u => u ∈ oddScope b)
          (fun _ => Fin (kTup n) → Fin N)).symm (a, fun u => ω₀ u.1)
  let ePi := (innerScopeEquiv b).piCongrLeft (fun _ => Fin (kTup n) → Fin N)
  have hstar (ws : InnerCoord n → Fin (kTup n) → Fin N) :
      starOf (extension (ePi ws)) b = ws := by
    funext a
    dsimp [starOf]
    have hval : (ePi ws) (innerScopeEquiv b a) = ws a :=
      Equiv.piCongrLeft_apply_apply (fun _ => Fin (kTup n) → Fin N)
        (innerScopeEquiv b) ws a
    have hcoord : innerScopeEquiv b a = ⟨evenNbr b a.1, oddScope_mem b a⟩ := rfl
    dsimp [extension]
    simp only [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos (oddScope_mem b a)]
    rw [← hcoord, hval]
  have hweights (ws : InnerCoord n → Fin (kTup n) → Fin N) :
      (∏ u : {u : EvenRole n // u ∈ oddScope b}, (P u.1).w ((ePi ws) u)) =
        starW E M.G (M.μ (t (sliceOf b.1))) (y₀ (t (sliceOf b.1))) ws := by
    unfold starW
    calc
      (∏ u : {u : EvenRole n // u ∈ oddScope b}, (P u.1).w ((ePi ws) u)) =
          ∏ a : InnerCoord n, (P (evenNbr b a.1)).w (ws a) := by
            symm
            exact Fintype.prod_equiv (innerScopeEquiv b)
              (fun a => (P (evenNbr b a.1)).w (ws a))
              (fun u => (P u.1).w ((ePi ws) u)) (by
                intro a
                have hval : (innerScopeEquiv b a).1 = evenNbr b a.1 := rfl
                rw [hval]
                simp [ePi, Equiv.piCongrLeft_apply_apply])
      _ = ∏ a : InnerCoord n,
          tupW E M.G (M.μ (t (sliceOf b.1))) (y₀ (t (sliceOf b.1))) (ws a) := by
            apply Finset.prod_congr rfl
            intro a _
            simp only [P]
            rw [innerNeighbor_slice]
            simp [P, tupLaw, FinProb.pi, tupW]
  have hscopeMean :
      (FinProb.pi (fun u : {u : EvenRole n // u ∈ oddScope b} => P u.1)).expect
        (fun a => φ (extension a)) = meanOddRow E M.G (InnerCoord n) (kTup n) (gS n)
          (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1)))
          (y₀ (t (sliceOf b.1))) y := by
    change (∑ a : (∀ u : {u : EvenRole n // u ∈ oddScope b}, Fin (kTup n) → Fin N),
        (∏ u : {u : EvenRole n // u ∈ oddScope b}, (P u.1).w (a u)) *
          φ (extension a)) = _
    calc
      (∑ a : (∀ u : {u : EvenRole n // u ∈ oddScope b}, Fin (kTup n) → Fin N),
          (∏ u : {u : EvenRole n // u ∈ oddScope b}, (P u.1).w (a u)) * φ (extension a)) =
          ∑ ws : InnerCoord n → Fin (kTup n) → Fin N,
            starW E M.G (M.μ (t (sliceOf b.1))) (y₀ (t (sliceOf b.1))) ws *
              oddRowW E M.G (gS n) (M.μ (t (sliceOf b.1)))
                (M.ν (t (sliceOf b.1))) ws y := by
          symm
          exact Fintype.sum_equiv ePi
            (fun ws => starW E M.G (M.μ (t (sliceOf b.1))) (y₀ (t (sliceOf b.1))) ws *
              oddRowW E M.G (gS n) (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1))) ws y)
            (fun a => (∏ u : {u : EvenRole n // u ∈ oddScope b}, (P u.1).w (a u)) * φ (extension a))
            (by
              intro ws
              rw [hweights ws]
              simp [φ, oddRowF, hstar ws])
      _ = meanOddRow E M.G (InnerCoord n) (kTup n) (gS n)
            (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1)))
            (y₀ (t (sliceOf b.1))) y := by rfl
  have hproj' : (FinProb.pi P).expect φ =
      (FinProb.pi (fun u : {u : EvenRole n // u ∈ oddScope b} => P u.1)).expect
        (fun a => φ (extension a)) := by
    simpa [extension] using hproj
  change (FinProb.pi P).expect φ = _
  calc
    (FinProb.pi P).expect φ =
        meanOddRow E M.G (InnerCoord n) (kTup n) (gS n)
          (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1))) (y₀ (t (sliceOf b.1))) y :=
      hproj'.trans hscopeMean
    _ = piRow M y₀ (t (sliceOf b.1)) y := rfl

private lemma pi_expect_finprod_disjoint {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (P : ι → FinProb Ω) {m : ℕ} (S : Fin m → Finset ι)
    (f : Fin m → (ι → Ω) → ℝ)
    (hdep : ∀ i, FinProb.DependsOn (f i) (S i))
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i ω) = ∏ i, (FinProb.pi P).expect (f i) := by
  classical
  induction m with
  | zero => simpa [FinProb.expect] using (FinProb.pi P).sum_eq_one
  | succ m ih =>
    let S' : Fin m → Finset ι := fun i => S i.castSucc
    let f' : Fin m → (ι → Ω) → ℝ := fun i => f i.castSucc
    let U : Finset ι := Finset.univ.biUnion S'
    have hdep' : ∀ i, FinProb.DependsOn (f' i) (S' i) := by
      intro i
      exact hdep i.castSucc
    have hdis' : ∀ i j, i ≠ j → Disjoint (S' i) (S' j) := by
      intro i j hij
      exact hdis i.castSucc j.castSucc (fun heq =>
        hij (Fin.ext (by simpa using congrArg Fin.val heq)))
    have hprodDep : FinProb.DependsOn (fun ω => ∏ i : Fin m, f' i ω) U := by
      intro ω ω' hagree
      apply Finset.prod_congr rfl
      intro i hi
      apply hdep' i ω ω'
      intro u hu
      exact hagree u (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hu⟩)
    have hlastDis : Disjoint U (S (Fin.last m)) := by
      apply Finset.disjoint_left.mpr
      intro u hu hv
      rcases Finset.mem_biUnion.mp hu with ⟨i, _, hi⟩
      have hne : i.castSucc ≠ Fin.last m := ne_of_lt (Fin.castSucc_lt_last i)
      exact Finset.disjoint_left.mp (hdis i.castSucc (Fin.last m) hne) hi hv
    have hfac := FinProb.pi_expect_mul_of_disjoint P
      (fun ω => ∏ i : Fin m, f' i ω) (f (Fin.last m)) U (S (Fin.last m)) hprodDep
      (hdep (Fin.last m)) hlastDis
    have hprod : (fun ω => ∏ i : Fin (m + 1), f i ω) =
        (fun ω => (∏ i : Fin m, f' i ω) * f (Fin.last m) ω) := by
      funext ω
      simp [f', Fin.prod_univ_castSucc]
    rw [hprod, hfac]
    have hih := ih S' f' hdep' hdis'
    rw [hih, Fin.prod_univ_castSucc]

private lemma massFail_depends_on_oddNbors {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι) (v : EvenRole n) :
    FinProb.DependsOn (fun f : OddRole n → Fin N =>
      if MassFail M y₀ p t f v then (1 : ℝ) else 0) (oddNbors v) := by
  intro f g hfg
  have hnbr : ∀ j : Fin n, f (oddNbr v j) = g (oddNbr v j) :=
    fun j => hfg _ (oddNbr_mem v j)
  have hin : innerOut f v = innerOut g v := by
    funext a
    exact hnbr a.1
  have hrow : ∀ x, evenRowF M y₀ p t f v x = evenRowF M y₀ p t g v x := by
    intro x
    unfold evenRowF
    rw [hin]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => by rw [hnbr j.1])
  have hmass : MassFail M y₀ p t f v = MassFail M y₀ p t g v := by
    unfold MassFail
    rw [show (∑ x, evenRowF M y₀ p t f v x) = ∑ x, evenRowF M y₀ p t g v x from
      Finset.sum_congr rfl (fun x _ => hrow x)]
  simp [hmass]

private lemma rawOddRows_product_mean {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι) (hS : SliceFacts M y₀)
    (hN : 0 < N) {m : ℕ} (b : Fin m → OddRole n) (y : Fin N)
    (hsep : ∀ i j, i ≠ j → 3 ≤ hammingDist (b i).1 (b j).1) :
    (rawTuples M y₀ t).expect (fun W => ∏ i, (N : ℝ) * oddRowF M t W (b i) y) =
      ∏ i, compA M y₀ t (sliceOf (b i).1) y := by
  classical
  let P : EvenRole n → FinProb (Fin (kTup n) → Fin N) := fun v =>
    tupLaw E M.G (M.μ (t (sliceOf v.1))) (y₀ (t (sliceOf v.1))) (kTup n)
  let f : Fin m → (EvenRole n → Fin (kTup n) → Fin N) → ℝ := fun i W =>
    (N : ℝ) * oddRowF M t W (b i) y
  have hdep : ∀ i, FinProb.DependsOn (f i) (oddScope (b i)) := by
    intro i W W' hW
    dsimp [f]
    exact congrArg (fun z : ℝ => (N : ℝ) * z)
      (oddRow_depends_on_scope M t (b i) y W W' hW)
  have hdis : ∀ i j, i ≠ j → Disjoint (oddScope (b i)) (oddScope (b j)) := by
    intro i j hij
    exact oddScopes_disjoint_of_sep (b i) (b j) (hsep i j hij)
  have hfac := pi_expect_finprod_disjoint P (fun i => oddScope (b i)) f hdep hdis
  change (FinProb.pi P).expect (fun W => ∏ i, f i W) = _ at hfac
  change (FinProb.pi P).expect (fun W => ∏ i, f i W) = _
  rw [hfac]
  apply Finset.prod_congr rfl
  intro i hi
  dsimp [f, P, compA]
  change (∑ W, (FinProb.pi P).w W * ((N : ℝ) * oddRowF M t W (b i) y)) =
    (N : ℝ) * piRow M y₀ (t (sliceOf (b i).1)) y
  calc
    (∑ W, (FinProb.pi P).w W * ((N : ℝ) * oddRowF M t W (b i) y)) =
        (N : ℝ) * ∑ W, (FinProb.pi P).w W * oddRowF M t W (b i) y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro W _
      ring
    _ = (N : ℝ) * piRow M y₀ (t (sliceOf (b i).1)) y := by
      rw [← rawOddRow_mean M y₀ t hS hN (b i) y]
      rfl

private lemma neighbor_row_eq {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (t : OuterWord n → M.ι) (v : EvenRole n)
    (W W' : EvenRole n → Fin (kTup n) → Fin N)
    (hW : ∀ u ∈ evenBall v 2, W u = W' u) (b : OddRole n) (hb : b ∈ oddNbors v) :
    ∀ y, oddRowF M t W b y = oddRowF M t W' b y := by
  intro y
  obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hb
  have hb' : b = oddNbr v j := hjb.symm
  subst b
  have hstar : starOf W (oddNbr v j) = starOf W' (oddNbr v j) := by
    funext a
    have h1 : hammingDist v.1 (oddNbr v j).1 = 1 := by
      have := HypercubeRamsey.cubeFlip_adj v.1 j
      change hammingDist v.1 (cubeFlip v.1 j) = 1 at this
      exact this
    have h2 : hammingDist (oddNbr v j).1 (evenNbr (oddNbr v j) a.1).1 = 1 := by
      have := HypercubeRamsey.cubeFlip_adj (oddNbr v j).1 a.1
      change hammingDist (oddNbr v j).1 (cubeFlip (oddNbr v j).1 a.1) = 1 at this
      exact this
    have hdist : hammingDist v.1 (evenNbr (oddNbr v j) a.1).1 ≤ 2 := by
      calc
        hammingDist v.1 (evenNbr (oddNbr v j) a.1).1 ≤
            hammingDist v.1 (oddNbr v j).1 +
              hammingDist (oddNbr v j).1 (evenNbr (oddNbr v j) a.1).1 :=
          HypercubeRamsey.hammingDist_triangle _ _ _
        _ = 2 := by rw [h1, h2]
    have hu : evenNbr (oddNbr v j) a.1 ∈ evenBall v 2 := by
      simp [evenBall, hdist]
    exact hW _ hu
  simpa [oddRowF, hstar]

private lemma massFailGiven_eq_of_near_eq {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (W W' : EvenRole n → Fin (kTup n) → Fin N) (v : EvenRole n) (hS : SliceFacts M y₀)
    (hN : 0 < N) (hW : ∀ u ∈ evenBall v 2, W u = W' u) :
    massFailGiven M y₀ p t W v = massFailGiven M y₀ p t W' v := by
  let φ : (OddRole n → Fin N) → ℝ := fun f => if MassFail M y₀ p t f v then 1 else 0
  have hφ := massFail_depends_on_oddNbors M y₀ p t v
  have hrows : ∀ b ∈ oddNbors v, rowLaw11 M y₀ t W hS b = rowLaw11 M y₀ t W' hS b := by
    intro b hb
    apply finprob_ext
    intro y
    exact neighbor_row_eq M t v W W' hW b hb y
  letI : ∀ b : OddRole n, Nonempty (Fin N) := fun _ => ⟨⟨0, hN⟩⟩
  have hexpect := pi_expect_eq_on_scope
    (fun b => rowLaw11 M y₀ t W hS b) (fun b => rowLaw11 M y₀ t W' hS b)
    (oddNbors v) φ hφ hrows
  change (FinProb.pi (fun b => rowLaw11 M y₀ t W hS b)).expect φ =
    (FinProb.pi (fun b => rowLaw11 M y₀ t W' hS b)).expect φ at hexpect
  simpa [massFailGiven, FinProb.expect, FinProb.pi, rowLaw11, oddProdW, φ] using hexpect

private lemma tupleBad_depends {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (t : OuterWord n → M.ι)
    (v : EvenRole n) (hS : SliceFacts M y₀) (hN : 0 < N) :
    FinProb.DependsOn (fun W => TupleBad M y₀ p P t v W) (evenBall v 2) := by
  intro W W' hW
  have heq := massFailGiven_eq_of_near_eq M y₀ p t W W' v hS hN hW
  simp [TupleBad, heq]

private theorem one_sub_mul_le_pow (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (d : ℕ) :
    1 - (d : ℝ) * x ≤ (1 - x) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hb0 : 0 ≤ 1 - x := by linarith
    have hb1 : 1 - x ≤ 1 := by linarith
    have hpow : (1 - x) ^ d ≤ 1 := pow_le_one₀ hb0 hb1
    rw [pow_succ]
    have hstep : (1 - x) ^ d - x ≤ (1 - x) ^ d * (1 - x) := by nlinarith
    calc
      1 - ((d + 1 : ℕ) : ℝ) * x = (1 - (d : ℝ) * x) - x := by push_cast; ring
      _ ≤ (1 - x) ^ d - x := sub_le_sub_right ih _
      _ ≤ (1 - x) ^ d * (1 - x) := hstep

private lemma tuple_numeric {n : ℕ} {P : ℝ} (hn : 4 ≤ n) (hP : 10 ≤ P) :
    let x := 2 * (n : ℝ) ^ (-P)
    0 ≤ x ∧ x < 1 ∧
      (n : ℝ) ^ (-P) ≤ x * (1 - x) ^ ((n + 1) ^ 4) := by
  dsimp
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : (1 : ℝ) ≤ n := by linarith
  have hpowP : (n : ℝ) ^ (-P) ≤ (n : ℝ) ^ (-10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hpowNonneg : 0 ≤ (n : ℝ) ^ (-P) := Real.rpow_nonneg (by positivity) _
  have hn10 : (n : ℝ) ^ (-10 : ℝ) ≤ (1 / 1024 : ℝ) := by
    have hnPow : (1024 : ℝ) ≤ (n : ℝ) ^ (10 : ℝ) := by
      have hp : (4 : ℝ) ^ (10 : ℝ) ≤ (n : ℝ) ^ (10 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hnR (by norm_num)
      calc
        1024 ≤ (4 : ℝ) ^ (10 : ℝ) := by norm_num
        _ ≤ (n : ℝ) ^ (10 : ℝ) := hp
    calc
      (n : ℝ) ^ (-10 : ℝ) = ((n : ℝ) ^ (10 : ℝ))⁻¹ := Real.rpow_neg (by positivity) 10
      _ ≤ (1024 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hnPow
      _ = 1 / 1024 := by norm_num
  have hsmall : (n : ℝ) ^ (-P) ≤ 1 / 1024 := le_trans hpowP hn10
  have hx0 : 0 ≤ 2 * (n : ℝ) ^ (-P) := by positivity
  have hx1 : 2 * (n : ℝ) ^ (-P) ≤ 1 / 512 := by nlinarith
  have hnd : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have hDelta : ((n + 1 : ℕ) : ℝ) ^ 4 ≤ (2 * (n : ℝ)) ^ 4 := by
    exact_mod_cast (Nat.pow_le_pow_left (by exact_mod_cast hnd) 4)
  have hDelta' : ((n + 1 : ℕ) : ℝ) ^ 4 ≤ 16 * (n : ℝ) ^ 4 := by nlinarith [hDelta]
  have hsmall2 : 2 * (n : ℝ) ^ (-P) * ((n + 1 : ℕ) : ℝ) ^ 4 ≤ 1 / 2 := by
    have hn6 : (n : ℝ) ^ (-6 : ℝ) ≤ 1 / 4096 := by
      have hp : (4096 : ℝ) ≤ (n : ℝ) ^ (6 : ℝ) := by
        have h4 : (4 : ℝ) ^ (6 : ℝ) ≤ (n : ℝ) ^ (6 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hnR (by norm_num)
        calc
          4096 = (4 : ℝ) ^ (6 : ℝ) := by norm_num
          _ ≤ (n : ℝ) ^ (6 : ℝ) := h4
      calc
        (n : ℝ) ^ (-6 : ℝ) = ((n : ℝ) ^ (6 : ℝ))⁻¹ := Real.rpow_neg (by positivity) 6
        _ ≤ (4096 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
        _ = 1 / 4096 := by norm_num
    have hpow6 : (n : ℝ) ^ (4 - P) ≤ (n : ℝ) ^ (-6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    have hcombine : (n : ℝ) ^ (-P) * (n : ℝ) ^ 4 = (n : ℝ) ^ (4 - P) := by
      calc
        (n : ℝ) ^ (-P) * (n : ℝ) ^ 4 =
            (n : ℝ) ^ (-P) * (n : ℝ) ^ (4 : ℝ) := by
              exact congrArg (fun z : ℝ => (n : ℝ)^(-P) * z)
                (Real.rpow_natCast (n : ℝ) 4).symm
        _ = (n : ℝ) ^ ((-P) + 4) := by
              rw [← Real.rpow_add (by positivity) (-P) (4 : ℝ)]
        _ = (n : ℝ) ^ (4 - P) := by congr 1 <;> ring
    calc
      2 * (n : ℝ) ^ (-P) * ((n + 1 : ℕ) : ℝ) ^ 4 ≤
          32 * (n : ℝ) ^ (4 - P) := by
        calc
          2 * (n : ℝ) ^ (-P) * ((n + 1 : ℕ) : ℝ) ^ 4 ≤
              32 * (n : ℝ) ^ (-P) * (n : ℝ) ^ 4 := by
                have hmul := mul_le_mul_of_nonneg_left hDelta' (by positivity : 0 ≤ 2 * (n : ℝ) ^ (-P))
                nlinarith
          _ = 32 * (n : ℝ) ^ (4 - P) := by
            calc
              32 * (n : ℝ)^(-P) * (n : ℝ)^4 = 32 * ((n : ℝ)^(-P) * (n : ℝ)^4) := by ring
              _ = 32 * (n : ℝ)^(4-P) := congrArg (fun z : ℝ => 32 * z) hcombine
      _ ≤ 32 * (1 / 4096 : ℝ) := by nlinarith [hpow6, hn6]
      _ ≤ 1 / 2 := by norm_num
  have hBern := one_sub_mul_le_pow (2 * (n : ℝ) ^ (-P)) hx0 (by linarith) ((n + 1) ^ 4)
  refine ⟨hx0, by linarith, ?_⟩
  have hhalf : (1 / 2 : ℝ) ≤ (1 - 2 * (n : ℝ) ^ (-P)) ^ ((n + 1) ^ 4) := by
    have hcast : (((n + 1) ^ 4 : ℕ) : ℝ) = ((n : ℝ) + 1) ^ 4 := by norm_cast
    have hsmall2' : (((n + 1) ^ 4 : ℕ) : ℝ) * (2 * (n : ℝ) ^ (-P)) ≤ 1 / 2 := by
      rw [hcast]
      simpa [mul_comm] using hsmall2
    linarith [hBern, hsmall2']
  nlinarith [hhalf]

private lemma tuple_penalty_bound {n m : ℕ} {P : ℝ} (hn : 4 ≤ n) (hm : m ≤ n)
    (hP : 10 ≤ P) (count : ℕ) (hcount : count ≤ m * (n + 1) ^ 3) :
    ((1 - 2 * (n : ℝ)^(-P)) ^ count)⁻¹ ≤ 2 ^ m := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hsmall : (n : ℝ)^(-P) ≤ (n : ℝ)^(-10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpow10 : (n : ℝ)^(-10 : ℝ) ≤ 1 / 1024 := by
    have hpow : (1024 : ℝ) ≤ (n : ℝ)^(10 : ℝ) := by
      have h4 : (4 : ℝ)^(10 : ℝ) ≤ (n : ℝ)^(10 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hnR (by norm_num)
      exact le_trans (by norm_num : (1024 : ℝ) ≤ (4 : ℝ)^(10 : ℝ)) h4
    calc
      (n : ℝ)^(-10 : ℝ) = ((n : ℝ)^(10 : ℝ))⁻¹ := Real.rpow_neg (by positivity) 10
      _ ≤ (1024 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpow
      _ = 1 / 1024 := by norm_num
  have hx0 : 0 ≤ 2 * (n : ℝ)^(-P) := by positivity
  have hx1 : 2 * (n : ℝ)^(-P) ≤ 1 / 512 := by nlinarith [hsmall, hpow10]
  have hcountR : (count : ℝ) ≤ (m : ℝ) * ((n + 1 : ℕ) : ℝ)^3 := by exact_mod_cast hcount
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hplus : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have hplus' : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hball : ((n + 1 : ℕ) : ℝ)^3 ≤ 8 * (n : ℝ)^3 := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)) hplus' 3
    calc
      ((n + 1 : ℕ) : ℝ)^3 ≤ (2 * (n : ℝ))^3 := hpow
      _ = 8 * (n : ℝ)^3 := by ring
  have hcombine : (n : ℝ)^(-P) * (n : ℝ)^4 = (n : ℝ)^(4 - P) := by
    calc
      (n : ℝ)^(-P) * (n : ℝ)^4 = (n : ℝ)^(-P) * (n : ℝ)^(4 : ℝ) := by
        exact congrArg (fun z : ℝ => (n : ℝ)^(-P) * z) (Real.rpow_natCast (n : ℝ) 4).symm
      _ = (n : ℝ)^((-P) + 4) := by rw [← Real.rpow_add (by positivity) (-P) (4 : ℝ)]
      _ = (n : ℝ)^(4 - P) := by congr 1 <;> ring
  have hexp : (n : ℝ)^(4 - P) ≤ (n : ℝ)^(-6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hn6 : (n : ℝ)^(-6 : ℝ) ≤ 1 / 4096 := by
    have hpow : (4096 : ℝ) ≤ (n : ℝ)^(6 : ℝ) := by
      have h4 : (4 : ℝ)^(6 : ℝ) ≤ (n : ℝ)^(6 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hnR (by norm_num)
      exact le_trans (by norm_num : (4096 : ℝ) ≤ (4 : ℝ)^(6 : ℝ)) h4
    calc
      (n : ℝ)^(-6 : ℝ) = ((n : ℝ)^(6 : ℝ))⁻¹ := Real.rpow_neg (by positivity) 6
      _ ≤ (4096 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpow
      _ = 1 / 4096 := by norm_num
  have hsmallCount : (count : ℝ) * (2 * (n : ℝ)^(-P)) ≤ 1 / 2 := by
    calc
      (count : ℝ) * (2 * (n : ℝ)^(-P)) ≤
          ((m : ℝ) * ((n + 1 : ℕ) : ℝ)^3) * (2 * (n : ℝ)^(-P)) :=
        mul_le_mul_of_nonneg_right hcountR (by positivity)
      _ ≤ ((n : ℝ) * (8 * (n : ℝ)^3)) * (2 * (n : ℝ)^(-P)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hmR hball (by positivity) (by positivity)
      _ = 16 * (n : ℝ)^4 * (n : ℝ)^(-P) := by ring
      _ = 16 * (n : ℝ)^(4 - P) := by rw [← hcombine]; ring
      _ ≤ 16 * (n : ℝ)^(-6 : ℝ) := by nlinarith [hexp]
      _ ≤ 16 * (1 / 4096 : ℝ) := by nlinarith [hn6]
      _ ≤ 1 / 2 := by norm_num
  have hBern := one_sub_mul_le_pow (2 * (n : ℝ)^(-P)) hx0 (by linarith [hx1]) count
  have hpowlower : (1 / 2 : ℝ) ≤ (1 - 2 * (n : ℝ)^(-P)) ^ count := by
    have hBern' : 1 - (count : ℝ) * (2 * (n : ℝ)^(-P)) ≤
        (1 - 2 * (n : ℝ)^(-P)) ^ count := by simpa using hBern
    linarith [hBern', hsmallCount]
  have hp : 0 < (1 - 2 * (n : ℝ)^(-P)) ^ count := lt_of_lt_of_le (by norm_num) hpowlower
  have hinv : ((1 - 2 * (n : ℝ)^(-P)) ^ count)⁻¹ ≤ 2 := by
    calc
      ((1 - 2 * (n : ℝ)^(-P)) ^ count)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
        inv_anti₀ (by norm_num) hpowlower
      _ = 2 := by norm_num
  by_cases hm0 : m = 0
  · subst m
    have hc0 : count = 0 := by simpa using hcount
    simp [hc0]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have htwo : (2 : ℝ) ≤ 2 ^ m := by
      cases m with
      | zero => omega
      | succ k =>
          rw [pow_succ]
          nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)]
    exact hinv.trans htwo

private def diffSet {d : ℕ} (v u : CubeVertex d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => u i ≠ v i)

private def vertexOfDiff {d : ℕ} (v : CubeVertex d) (s : Finset (Fin d)) : CubeVertex d :=
  fun i => if i ∈ s then !(v i) else v i

private def diffEquiv {d : ℕ} (v : CubeVertex d) : CubeVertex d ≃ Finset (Fin d) where
  toFun := diffSet v
  invFun := vertexOfDiff v
  left_inv := by
    intro u
    funext i
    by_cases hi : u i = v i
    · simp [vertexOfDiff, diffSet, hi]
    · have hm : i ∈ diffSet v u := by simp [diffSet, hi]
      have heq : v i = !(u i) := by cases hu : u i <;> cases hv : v i <;> simp_all
      simp [vertexOfDiff, hm, heq]
  right_inv := by
    intro s
    ext i
    by_cases hi : i ∈ s <;> simp [diffSet, vertexOfDiff, hi]

private lemma diffSet_card {d : ℕ} (v u : CubeVertex d) :
    (diffSet v u).card = hammingDist u v := by
  simp [diffSet, hammingDist, ne_comm]

private def ballToSubsets {d r : ℕ} (v : CubeVertex d) :
    {u : CubeVertex d // hammingDist u v ≤ r} ≃ {s : Finset (Fin d) // s.card ≤ r} where
  toFun u := ⟨diffSet v u.1, by rw [diffSet_card]; exact u.2⟩
  invFun s := ⟨vertexOfDiff v s.1, by rw [← diffSet_card]; simp [diffSet, vertexOfDiff]; exact s.2⟩
  left_inv := by intro u; exact Subtype.ext ((diffEquiv v).left_inv u.1)
  right_inv := by intro s; exact Subtype.ext ((diffEquiv v).right_inv s.1)

private def smallSubsetFiberEquiv (d r : ℕ) (i : Fin (r + 1)) :
    {s : {s : Finset (Fin d) // s.card ≤ r} // (⟨s.1.card, by omega⟩ : Fin (r + 1)) = i} ≃
      {s : Finset (Fin d) // s.card = i.val} where
  toFun s := ⟨s.1.1, by have h := congrArg Fin.val s.2; simpa using h⟩
  invFun s := ⟨⟨s.1, by rw [s.2]; omega⟩, by apply Fin.ext; exact s.2⟩
  left_inv := by intro s; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro s; apply Subtype.ext; rfl

private def subsetsSmallEquiv (d r : ℕ) :
    {s : Finset (Fin d) // s.card ≤ r} ≃
      Σ i : Fin (r + 1), {s : Finset (Fin d) // s.card = i.val} := by
  let f : {s : Finset (Fin d) // s.card ≤ r} → Fin (r + 1) := fun s => ⟨s.1.card, by omega⟩
  exact (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight (smallSubsetFiberEquiv d r))

private theorem card_small_subsets (d r : ℕ) :
    Fintype.card {s : Finset (Fin d) // s.card ≤ r} =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  rw [Fintype.card_congr (subsetsSmallEquiv d r), Fintype.card_sigma]
  have hfiber (i : Fin (r + 1)) :
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Nat.choose d i.val := by
    let S : Finset (Finset (Fin d)) := Finset.univ.powersetCard i.val
    let e : {s : Finset (Fin d) // s.card = i.val} ≃ S :=
      { toFun := fun s => ⟨s.1, by rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, s.2⟩⟩
        invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
        left_inv := by intro s; apply Subtype.ext; rfl
        right_inv := by intro s; apply Subtype.ext; rfl }
    calc
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Fintype.card S := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose d i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

private theorem hammingBall_card (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  have hcard : Fintype.card {u : CubeVertex d // hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubeVertex d => hammingDist u v ≤ r))
  exact hcard.symm.trans ((Fintype.card_congr (ballToSubsets v)).trans (card_small_subsets d r))

private lemma hammingBall_card_le_four (n : ℕ) (v : CubeVertex n) :
    (HypercubeRamsey.hammingBall v 4).card ≤ (n + 1) ^ 4 := by
  have hcard := hammingBall_card n 4 v
  have hsum : (∑ i ∈ Finset.range 5, Nat.choose n i : ℕ) ≤
      ∑ i ∈ Finset.range 5, n ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.choose_le_pow n i
  have hsumR : (∑ i ∈ Finset.range 5, (Nat.choose n i : ℝ)) ≤
      ∑ i ∈ Finset.range 5, (n : ℝ) ^ i := by exact_mod_cast hsum
  have hsumId : ∑ i ∈ Finset.range 5, (n : ℝ) ^ i =
      1 + (n : ℝ) + (n : ℝ)^2 + (n : ℝ)^3 + (n : ℝ)^4 := by norm_num [Finset.sum_range_succ]
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hp : (1 + (n : ℝ) + (n : ℝ)^2 + (n : ℝ)^3 + (n : ℝ)^4) ≤ ((n : ℝ) + 1) ^ 4 := by
    nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ)^2), mul_nonneg hn0 (sq_nonneg (n : ℝ))]
  have hreal : ((HypercubeRamsey.hammingBall v 4).card : ℝ) ≤ ((n : ℝ) + 1)^4 := by
    simp only [HypercubeRamsey.hammingBall]
    have hcard' : (Finset.univ.filter (fun u : CubeVertex n => hammingDist v u ≤ 4)).card =
        ∑ i ∈ Finset.range 5, Nat.choose n i := by
      simpa [HypercubeRamsey.hammingDist, ne_comm] using hcard
    rw [hcard']
    rw [Nat.cast_sum]
    calc
      (∑ i ∈ Finset.range 5, (Nat.choose n i : ℝ)) ≤ ∑ i ∈ Finset.range 5, (n : ℝ)^i := hsumR
      _ = 1 + (n : ℝ) + (n : ℝ)^2 + (n : ℝ)^3 + (n : ℝ)^4 := hsumId
      _ ≤ ((n : ℝ) + 1)^4 := hp
  exact_mod_cast hreal

private lemma hammingBall_card_le_three (n : ℕ) (v : CubeVertex n) :
    (HypercubeRamsey.hammingBall v 3).card ≤ (n + 1) ^ 3 := by
  have hcard := hammingBall_card n 3 v
  have hsum : (∑ i ∈ Finset.range 4, Nat.choose n i) ≤
      ∑ i ∈ Finset.range 4, n ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.choose_le_pow n i
  have hsumR : (∑ i ∈ Finset.range 4, (Nat.choose n i : ℝ)) ≤
      ∑ i ∈ Finset.range 4, (n : ℝ) ^ i := by exact_mod_cast hsum
  have hsumId : ∑ i ∈ Finset.range 4, (n : ℝ) ^ i =
      1 + (n : ℝ) + (n : ℝ)^2 + (n : ℝ)^3 := by norm_num [Finset.sum_range_succ]
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hp : (1 + (n : ℝ) + (n : ℝ)^2 + (n : ℝ)^3) ≤ ((n : ℝ) + 1) ^ 3 := by
    nlinarith [sq_nonneg (n : ℝ), mul_nonneg hn0 (sq_nonneg (n : ℝ))]
  have hreal : ((HypercubeRamsey.hammingBall v 3).card : ℝ) ≤ ((n : ℝ) + 1)^3 := by
    simp only [HypercubeRamsey.hammingBall]
    have hcard' : (Finset.univ.filter (fun u : CubeVertex n => hammingDist v u ≤ 3)).card =
        ∑ i ∈ Finset.range 4, Nat.choose n i := by
      simpa [HypercubeRamsey.hammingDist, ne_comm] using hcard
    rw [hcard']
    rw [Nat.cast_sum]
    calc
      (∑ i ∈ Finset.range 4, (Nat.choose n i : ℝ)) ≤ ∑ i ∈ Finset.range 4, (n : ℝ)^i := hsumR
      _ = 1 + (n : ℝ) + (n : ℝ)^2 + (n : ℝ)^3 := hsumId
      _ ≤ ((n : ℝ) + 1)^3 := hp
  exact_mod_cast hreal

private lemma evenBall_card_le_four {n : ℕ} (v : EvenRole n) :
    (evenBall v 4).card ≤ (n + 1) ^ 4 := by
  let f : EvenRole n → CubeVertex n := fun u => u.1
  have hinj : Function.Injective f := by intro a b h; exact Subtype.ext h
  have himage : (evenBall v 4).card = ((evenBall v 4).image f).card :=
    (Finset.card_image_of_injective _ hinj).symm
  have hsubset : (evenBall v 4).image f ⊆ HypercubeRamsey.hammingBall v.1 4 := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    simp only [HypercubeRamsey.hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hw).2
  calc
    (evenBall v 4).card = ((evenBall v 4).image f).card := himage
    _ ≤ (HypercubeRamsey.hammingBall v.1 4).card := Finset.card_le_card hsubset
    _ ≤ (n + 1) ^ 4 := hammingBall_card_le_four n v.1

private lemma odd_center_even_ball_card_le_three {n : ℕ} (b : OddRole n) :
    (Finset.univ.filter fun v : EvenRole n => hammingDist b.1 v.1 ≤ 3).card ≤ (n + 1) ^ 3 := by
  let f : EvenRole n → CubeVertex n := fun v => v.1
  have hinj : Function.Injective f := by intro u v h; exact Subtype.ext h
  have himage : (Finset.univ.filter fun v : EvenRole n => hammingDist b.1 v.1 ≤ 3).card =
      ((Finset.univ.filter fun v : EvenRole n => hammingDist b.1 v.1 ≤ 3).image f).card :=
    (Finset.card_image_of_injective _ hinj).symm
  have hsubset : ((Finset.univ.filter fun v : EvenRole n => hammingDist b.1 v.1 ≤ 3).image f) ⊆
      HypercubeRamsey.hammingBall b.1 3 := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
    simp only [HypercubeRamsey.hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [HypercubeRamsey.hammingDist, ne_comm] using (Finset.mem_filter.mp hv).2
  calc
    (Finset.univ.filter fun v : EvenRole n => hammingDist b.1 v.1 ≤ 3).card =
        ((Finset.univ.filter fun v : EvenRole n => hammingDist b.1 v.1 ≤ 3).image f).card := himage
    _ ≤ (HypercubeRamsey.hammingBall b.1 3).card := Finset.card_le_card hsubset
    _ ≤ (n + 1)^3 := hammingBall_card_le_three n b.1

private lemma hammingDist_comm' {n : ℕ} (u v : CubeVertex n) :
    hammingDist u v = hammingDist v u := by
  simp [HypercubeRamsey.hammingDist, ne_comm]

private lemma tuple_events_touching_oddScopes_card {n : ℕ} {m : ℕ}
    (b : Fin m → OddRole n) :
    let U := Finset.univ.biUnion (fun i : Fin m => oddScope (b i))
    ((Finset.univ.filter fun v : EvenRole n => ¬ Disjoint (evenBall v 2) U).card : ℝ) ≤
      (m : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 3 := by
  classical
  dsimp only
  let T : Finset (EvenRole n) := Finset.univ.filter fun v =>
    ¬ Disjoint (evenBall v 2) (Finset.univ.biUnion (fun i : Fin m => oddScope (b i)))
  let R : Fin m → Finset (EvenRole n) := fun i =>
    Finset.univ.filter fun v => hammingDist (b i).1 v.1 ≤ 3
  have hsub : T ⊆ Finset.univ.biUnion R := by
    intro v hv
    rcases Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hv).2 with ⟨u, hu1, hu2⟩
    rcases Finset.mem_biUnion.mp hu2 with ⟨i, _, hi⟩
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hi
    have hbu : hammingDist (b i).1 u.1 = 1 := by
      rw [← ha]
      have h := HypercubeRamsey.cubeFlip_adj (b i).1 a.1
      change hammingDist (b i).1 (cubeFlip (b i).1 a.1) = 1 at h
      exact h
    have huv : hammingDist u.1 v.1 ≤ 2 := by
      have hmem := (Finset.mem_filter.mp hu1).2
      simpa [hammingDist_comm'] using hmem
    have hdist : hammingDist (b i).1 v.1 ≤ 3 := by
      calc
        hammingDist (b i).1 v.1 ≤ hammingDist (b i).1 u.1 + hammingDist u.1 v.1 :=
          HypercubeRamsey.hammingDist_triangle _ _ _
        _ ≤ 1 + 2 := Nat.add_le_add (le_of_eq hbu) huv
        _ = 3 := by norm_num
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩⟩
  have hcard : (T.card : ℝ) ≤
      ∑ i : Fin m, ((Finset.univ.filter fun v : EvenRole n => hammingDist (b i).1 v.1 ≤ 3).card : ℝ) := by
    calc
      (T.card : ℝ) ≤ ((Finset.univ.biUnion R).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ i : Fin m, ((R i).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := R))
      _ = ∑ i : Fin m,
          ((Finset.univ.filter fun v : EvenRole n => hammingDist (b i).1 v.1 ≤ 3).card : ℝ) := by
        simp [R]
  calc
    ((Finset.univ.filter fun v : EvenRole n => ¬ Disjoint (evenBall v 2)
      (Finset.univ.biUnion fun i : Fin m => oddScope (b i))).card : ℝ) = T.card := by
        simp [T]
    _ ≤ ∑ i : Fin m,
        ((Finset.univ.filter fun v : EvenRole n => hammingDist (b i).1 v.1 ≤ 3).card : ℝ) := hcard
    _ ≤ ∑ _i : Fin m, ((n + 1 : ℕ) : ℝ)^3 := by
      apply Finset.sum_le_sum
      intro i hi
      exact_mod_cast odd_center_even_ball_card_le_three (b i)
    _ = (m : ℝ) * ((n + 1 : ℕ) : ℝ)^3 := by simp [mul_comm]

private lemma tuple_degree_bound {n : ℕ} (v : EvenRole n) :
    (Finset.univ.filter fun w : EvenRole n =>
      w ≠ v ∧ ¬ Disjoint (evenBall v 2) (evenBall w 2)).card ≤ (n + 1) ^ 4 := by
  have hsubset : (Finset.univ.filter fun w : EvenRole n =>
      w ≠ v ∧ ¬ Disjoint (evenBall v 2) (evenBall w 2)) ⊆ evenBall v 4 := by
    intro w hw
    rcases (Finset.mem_filter.mp hw).2 with ⟨_, hnd⟩
    rcases Finset.not_disjoint_iff.mp hnd with ⟨u, huv, huw⟩
    have h1 : hammingDist v.1 u.1 ≤ 2 := (Finset.mem_filter.mp huv).2
    have h2 : hammingDist w.1 u.1 ≤ 2 := (Finset.mem_filter.mp huw).2
    have hdist : hammingDist v.1 w.1 ≤ 4 := by
      calc
        hammingDist v.1 w.1 ≤ hammingDist v.1 u.1 + hammingDist u.1 w.1 :=
          HypercubeRamsey.hammingDist_triangle _ _ _
        _ ≤ 2 + 2 := Nat.add_le_add h1 (by simpa [hammingDist_comm'] using h2)
        _ = 4 := by norm_num
    simp [evenBall, hdist]
  calc
    (Finset.univ.filter fun w : EvenRole n =>
      w ≠ v ∧ ¬ Disjoint (evenBall v 2) (evenBall w 2)).card ≤ (evenBall v 4).card :=
        Finset.card_le_card hsubset
    _ ≤ (n + 1)^4 := evenBall_card_le_four v

theorem tuple_lll (δ x₀ K P : ℝ) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p → GatedTags M y₀ p P t → TupleLLL11 M y₀ p P t := by
  refine ⟨4, ?_⟩
  intro n hn N E X Y κ M y₀ p t hF hGate
  have hN : 0 < N := lt_of_lt_of_le (Nat.pow_pos (by omega)) hF.host
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hnum := tuple_numeric hn hP
  change S07.LLLInput
    (fun v : EvenRole n => tupLaw E M.G (M.μ (t (sliceOf v.1))) (y₀ (t (sliceOf v.1))) (kTup n))
    (fun v W => TupleBad M y₀ p P t v W) (fun v => evenBall v 2)
    (xTup n P) ((n + 1) ^ 4)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hnum.1
  · exact hnum.2.1
  · intro v
    exact tupleBad_depends M y₀ p P t v hF.slice hN
  · intro v
    apply le_trans ?_ (evenBall_card_le_four v)
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases hj with ⟨_, hnd⟩
    rcases Finset.not_disjoint_iff.mp hnd with ⟨u, huv, huj⟩
    have h1 : hammingDist v.1 u.1 ≤ 2 := (Finset.mem_filter.mp huv).2
    have h2 : hammingDist j.1 u.1 ≤ 2 := (Finset.mem_filter.mp huj).2
    have hdist : hammingDist v.1 j.1 ≤ 4 := by
      calc
        hammingDist v.1 j.1 ≤ hammingDist v.1 u.1 + hammingDist u.1 j.1 :=
          HypercubeRamsey.hammingDist_triangle _ _ _
        _ ≤ 2 + 2 := Nat.add_le_add h1
          (by simpa [HypercubeRamsey.hammingDist, ne_comm] using h2)
        _ = 4 := by norm_num
    simpa [evenBall, hdist]
  · intro v
    let s := sliceOf v.1
    have hnot : ¬ T1 M y₀ p P t s := by
      intro h
      exact hGate.2 s (Or.inl h)
    have hraw : rawFail M y₀ p t v ≤ (n : ℝ) ^ (-(2 * P)) := by
      by_contra h
      apply hnot
      exact ⟨v, rfl, lt_of_not_ge h⟩
    have hqpos : 0 < (n : ℝ) ^ (-P) := Real.rpow_pos_of_pos (by positivity) _
    have hmean := FinProb.markov (rawTuples M y₀ t)
      (fun W => massFailGiven M y₀ p t W v) ((n : ℝ) ^ (-P))
      (by
        intro W
        unfold massFailGiven
        apply Finset.sum_nonneg
        intro f _
        exact mul_nonneg
          (Finset.prod_nonneg fun b _ =>
            (hF.slice.rows (t (sliceOf b.1))).row_nonneg (starOf W b) (f b))
          (by split_ifs <;> norm_num)) hqpos
    have hbadle : (FinProb.pi (fun u : EvenRole n =>
        tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n))).pr
          (fun W => (n : ℝ)^(-P) ≤ massFailGiven M y₀ p t W v) ≤
        rawFail M y₀ p t v / (n : ℝ)^(-P) := by
      simpa [rawFail, rawTuples] using hmean
    have hprob : (FinProb.pi (fun u : EvenRole n =>
        tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n))).pr
          (fun W => TupleBad M y₀ p P t v W) ≤ (n : ℝ)^(-P) := by
      calc
        _ ≤ (FinProb.pi (fun u : EvenRole n =>
            tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n))).pr
              (fun W => (n : ℝ)^(-P) ≤ massFailGiven M y₀ p t W v) :=
          FinProb.pr_mono _ _ _ (by intro W hW; exact le_of_lt hW)
        _ ≤ rawFail M y₀ p t v / (n : ℝ)^(-P) := hbadle
        _ ≤ (n : ℝ)^(-P) := by
          apply (div_le_iff₀ hqpos).2
          have hpow : (n : ℝ) ^ (-(2 * P)) = ((n : ℝ)^(-P))^2 := by
            calc
              (n : ℝ) ^ (-(2 * P)) = (n : ℝ) ^ ((-P) * (2 : ℝ)) := by congr 1 <;> ring
              _ = ((n : ℝ)^(-P)) ^ (2 : ℝ) := Real.rpow_mul (by positivity) (-P) (2 : ℝ)
              _ = ((n : ℝ)^(-P)) ^ 2 := Real.rpow_natCast _ 2
          rw [hpow] at hraw
          simpa [pow_two] using hraw
    simpa [xTup] using le_trans hprob hnum.2.2

theorem odd_moment (δ x₀ K P : ℝ) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p → GatedTags M y₀ p P t → S07.CondProductBound →
      TupleLLL11 M y₀ p P t → OddMoment11 M y₀ p P t := by
  refine ⟨4, ?_⟩
  intro n hn N E X Y κ M y₀ p t hF hGate hCondProduct hTupleLLL
  have hN : 0 < N := lt_of_lt_of_le (Nat.pow_pos (by omega)) hF.host
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  intro y m hmn b hsep
  let Q : EvenRole n → FinProb (Fin (kTup n) → Fin N) := fun v =>
    tupLaw E M.G (M.μ (t (sliceOf v.1))) (y₀ (t (sliceOf v.1))) (kTup n)
  let U : Finset (EvenRole n) := Finset.univ.biUnion (fun i : Fin m => oddScope (b i))
  let Φ : (EvenRole n → Fin (kTup n) → Fin N) → ℝ := fun W =>
    ∏ i, (N : ℝ) * oddRowF M t W (b i) y
  have hdep : FinProb.DependsOn Φ U := by
    intro W W' hW
    dsimp [Φ]
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    apply oddRow_depends_on_scope M t (b i) y W W'
    intro v hv
    exact hW v (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hv⟩)
  have hPhi0 : ∀ W, 0 ≤ Φ W := by
    intro W
    dsimp [Φ]
    apply Finset.prod_nonneg
    intro i hi
    apply mul_nonneg (by positivity)
    exact (hF.slice.rows (t (sliceOf (b i).1))).row_nonneg (starOf W (b i)) y
  have hRawMean : (FinProb.pi Q).expect Φ =
      ∏ i, compA M y₀ t (sliceOf (b i).1) y := by
    simpa [Q, Φ, rawTuples] using rawOddRows_product_mean M y₀ t hF.slice hN b y hsep
  have hlocal : ∀ ω, (∑ a : (∀ v : U, Fin (kTup n) → Fin N),
      (∏ v : U, (Q v.1).w (a v)) * Φ (S07.glue U ω a)) ≤
        ∏ i, compA M y₀ t (sliceOf (b i).1) y := by
    intro ω
    rw [pi_local_sum_glue Q U Φ hdep ω, hRawMean]
  have hLLL : S07.LLLInput Q (fun v W => TupleBad M y₀ p P t v W)
      (fun v => evenBall v 2) (xTup n P) ((n + 1) ^ 4) := by
    change S07.LLLInput Q (fun v W => TupleBad M y₀ p P t v W)
      (fun v => evenBall v 2) (xTup n P) ((n + 1) ^ 4) at hTupleLLL
    exact hTupleLLL
  have hAvoid := hCondProduct (P := Q) (Bad := fun v W => TupleBad M y₀ p P t v W)
    (sc := fun v => evenBall v 2) (x := xTup n P) (Δ := (n + 1)^4) hLLL
  let count := (Finset.univ.filter fun v : EvenRole n => ¬ Disjoint (evenBall v 2) U).card
  have hcount : count ≤ m * (n + 1)^3 := by
    dsimp [count, U]
    exact_mod_cast (tuple_events_touching_oddScopes_card b)
  have hfactor : ((1 - xTup n P) ^ count)⁻¹ ≤ 2 ^ m := by
    simpa [count, xTup] using tuple_penalty_bound hn hmn hP count hcount
  have hbaseNonneg : 0 ≤ ∏ i, compA M y₀ t (sliceOf (b i).1) y := by
    apply Finset.prod_nonneg
    intro i hi
    unfold compA
    apply mul_nonneg (by positivity)
    exact (hF.slice.rows (t (sliceOf (b i).1))).pi_nonneg y
  have hbound := hAvoid.2 U Φ hPhi0
    (∏ i, compA M y₀ t (sliceOf (b i).1) y) hlocal
  change (tupleLaw M y₀ p P t).expect Φ ≤ _ at hbound
  calc
    (tupleLaw M y₀ p P t).expect Φ ≤
        ((1 - xTup n P) ^ count)⁻¹ *
          (∏ i, compA M y₀ t (sliceOf (b i).1) y) := by simpa [count] using hbound
    _ ≤ 2 ^ m * ∏ i, compA M y₀ t (sliceOf (b i).1) y :=
      mul_le_mul_of_nonneg_right hfactor hbaseNonneg
    _ = 2 ^ m * ∏ i, compA M y₀ t (sliceOf (b i).1) y := rfl
  
  

end HypercubeRamsey.Lane_q_s11_odd
