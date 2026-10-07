import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.S03.Clock.Steps_p_clock_r4
import HypercubeRamsey.S05.Clock_q_s05_even
import HypercubeRamsey.S05.Stages_p_s05_h
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Tools.SignedTest
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_q_s09_gain1

open HypercubeRamsey OAI.HypercubeRamsey Classical
open Filter
open scoped BigOperators

private theorem nonempty_of_probability {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  classical
  have hpos : 0 < ∑ a, P.w a := by rw [P.sum_eq_one]; norm_num
  obtain ⟨a, ha, hap⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := P.w)
      (by intro a ha; exact P.nonneg a)).mp hpos
  exact ⟨a⟩

private theorem pi_pr_slice_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (i : ι) (F : (∀ i, Ω i) → Prop) (B : ℝ)
    (hbound : ∀ (b : ∀ j : {j // j ≠ i}, Ω j.1),
      (FinProb.pi (fun j : {j // j ∉ ({i} : Finset ι)} => P j.1)).w
        (fun j => b ⟨j.1, by simpa using j.2⟩) ≠ 0 →
      (P i).pr (fun o => F (Function.update (fun j => if h : j = i then
        cast (congrArg Ω h.symm) (Classical.choice (nonempty_of_probability (P i))) else b ⟨j, h⟩)
        i o)) ≤ B) :
    (FinProb.pi P).pr F ≤ B := by
  classical
  let S : Finset ι := {i}
  let J := {j // j ∈ S}
  letI : Unique J := ⟨⟨i, by simp [S]⟩, fun j => by
    apply Subtype.ext
    exact Finset.mem_singleton.mp (by simpa [S] using j.2)⟩
  let j₀ : J := default
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ S) Ω
  let base : ∀ j, Ω j := fun j => Classical.choice (nonempty_of_probability (P j))
  let ωb : (∀ j : {j // j ∉ S}, Ω j.1) → ∀ j, Ω j := fun b j =>
    if h : j = i then cast (congrArg Ω h.symm) (base i)
    else b ⟨j, by simpa [S] using h⟩
  let Ps : FinProb (∀ j : J, Ω j.1) := FinProb.pi (fun j : J => P j.1)
  let Pc : FinProb (∀ j : {j // j ∉ S}, Ω j.1) :=
    FinProb.pi (fun j : {j // j ∉ S} => P j.1)
  have hsplice (a : ∀ j : J, Ω j.1) (b : ∀ j : {j // j ∉ S}, Ω j.1) :
      e.symm (a, b) = Function.update (ωb b) i (a j₀) := by
    funext j
    by_cases hj : j = i
    · subst j
      have hsub : (⟨i, by simp [S]⟩ : J) = j₀ := Subsingleton.elim _ _
      simp [e, S, ωb, Equiv.piEquivPiSubtypeProd]
      change a (⟨i, by simp [S]⟩ : J) = a j₀
      cases hsub
      rfl
    · simp [Function.update, hj, e, S, ωb, Equiv.piEquivPiSubtypeProd_symm_apply]
  have hweight (a : ∀ j : J, Ω j.1) : Ps.w a = (P i).w (a j₀) := by
    change (∏ j : J, (P j.1).w (a j)) = _
    simp [J, j₀, S]
  have hinner (b : ∀ j : {j // j ∉ S}, Ω j.1) :
      Pc.w b *
          (∑ a : ∀ j : J, Ω j.1, Ps.w a *
            (if F (Function.update (ωb b) i (a j₀)) then 1 else 0)) ≤ Pc.w b * B := by
    let ea : (∀ j : J, Ω j.1) ≃ Ω i := Equiv.piUnique (fun j : J => Ω j.1)
    have heval (o : Ω i) : (ea.symm o) j₀ = o := by
      simp [ea, j₀]
    have hsum :
        (∑ a : ∀ j : J, Ω j.1, Ps.w a * (if F (Function.update (ωb b) i (a j₀)) then 1 else 0)) =
          (P i).pr (fun o => F (Function.update (ωb b) i o)) := by
      rw [← Equiv.sum_comp ea.symm]
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro o ho
      rw [hweight (ea.symm o), heval o]
      by_cases hF : F (Function.update (ωb b) i o) <;> simp [hF]
    let b' : ∀ j : {j // j ≠ i}, Ω j.1 := fun j => b ⟨j.1, by simpa [S] using j.2⟩
    by_cases hb : Pc.w b = 0
    · simp [hb]
    · have hb' :
          (FinProb.pi (fun j : {j // j ∉ ({i} : Finset ι)} => P j.1)).w
            (fun j => b' ⟨j.1, by simpa using j.2⟩) ≠ 0 := by
        simpa [Pc, S, b'] using hb
      have hbnd := hbound b' hb'
      rw [hsum]
      have hPc : Pc.w b =
          (FinProb.pi (fun j : {j // j ∉ ({i} : Finset ι)} => P j.1)).w
            (fun j => b' ⟨j.1, by simpa using j.2⟩) := by
        simp [Pc, S, b']
      rw [hPc]
      simpa [ωb, base, b', S] using mul_le_mul_of_nonneg_left hbnd (Pc.nonneg b)
  have hsplit := Clock.pi_expect_split_p_clock_r4 P S (fun ω => if F ω then 1 else 0)
  have hprob : (FinProb.pi P).pr F =
      ∑ a : ∀ j : J, Ω j.1, ∑ b : ∀ j : {j // j ∉ S}, Ω j.1,
        Ps.w a * Pc.w b * (if F (e.symm (a, b)) then 1 else 0) := by
    calc
      (FinProb.pi P).pr F = (FinProb.pi P).expect (fun ω => if F ω then 1 else 0) := by
        simp [FinProb.pr, FinProb.expect]
      _ = _ := hsplit
  rw [hprob]
  calc
    (∑ a, ∑ b, Ps.w a * Pc.w b * (if F (e.symm (a, b)) then 1 else 0)) =
        ∑ b, Pc.w b * ∑ a, Ps.w a * (if F (Function.update (ωb b) i (a j₀)) then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [hsplice]
          ring
    _ ≤ ∑ b, Pc.w b * B := by
          apply Finset.sum_le_sum
          intro b hb
          exact hinner b
    _ = B := by simp [← Finset.sum_mul, Pc.sum_eq_one]

private theorem condExp_eq_condLaw_expect9 {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (hA : 0 < P.pr A) (f : Ω → ℝ) :
    P.condExp f A = (P.cond A hA).expect f := by
  unfold FinProb.condExp FinProb.expect FinProb.cond
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h] <;> ring

private noncomputable def regularityOrder9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n)
    (t : Fin 3) : List I.ID :=
  if t.val = 2 then coreOrder9 I v b else fullOrder9 I v b

private noncomputable def regularityBase9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (b : OddSites9 n)
    (ω : Outcome9 I N) (t : Fin 3) : Law N :=
  if t.val = 0 then maskedLaw9 S ω b else siteSecond9 S b.1

private theorem fullOrder_nodup9 {P : Params9} {n : ℕ}
    (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n) : (fullOrder9 I v b).Nodup := by
  classical
  let O := outerIDs9 I v b
  let K := coreIDs9 I v b
  have hdis : Disjoint O K := by
    rw [Finset.disjoint_left]
    intro x hxO hxK
    have hxO' := (Finset.mem_sdiff.mp hxO).2
    have hxK' := (Finset.mem_erase.mp hxK).2
    exact hxO' (Finset.mem_inter.mp hxK').2
  have hO : O.toList.Nodup := Finset.nodup_toList O
  have hK : K.toList.Nodup := Finset.nodup_toList K
  have hcross : ∀ x ∈ O.toList, ∀ y ∈ K.toList, x ≠ y := by
    intro x hx y hy hxy
    subst y
    exact (Finset.disjoint_left.mp hdis) (by simpa using hx) (by simpa using hy)
  have hOK : (O.toList ++ K.toList).Nodup := List.nodup_append.mpr ⟨hO, hK, hcross⟩
  have hcenterCore : I.center v.1 ∈ I.core v.1 := I.center_mem_core v.1 v.2
  have hcenterO : I.center v.1 ∉ O := by
    intro h
    exact (Finset.mem_sdiff.mp h).2 hcenterCore
  have hcenterK : I.center v.1 ∉ K := by
    intro h
    exact (Finset.mem_erase.mp h).1 rfl
  have hlast : ∀ x ∈ O.toList ++ K.toList, x ≠ I.center v.1 := by
    intro x hx hxeq
    have hx' : x ∈ O.toList ∨ x ∈ K.toList := List.mem_append.mp hx
    rcases hx' with hx' | hx'
    · have hxCenter : I.center v.1 ∈ O.toList := by simpa [hxeq] using hx'
      exact hcenterO (by simpa using hxCenter)
    · have hxCenter : I.center v.1 ∈ K.toList := by simpa [hxeq] using hx'
      exact hcenterK (by simpa using hxCenter)
  change (O.toList ++ K.toList ++ [I.center v.1]).Nodup
  apply List.nodup_append.mpr
  refine ⟨hOK, by simp, ?_⟩
  intro x hx y hy
  simp at hy
  subst y
  exact hlast x hx

private theorem regularityOrder_nodup9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n) (b : OddSites9 n)
    (t : Fin 3) : (regularityOrder9 S I v b t).Nodup := by
  classical
  by_cases ht : t.val = 2
  · simp [regularityOrder9, ht]
    exact Finset.nodup_toList _
  · simp [regularityOrder9, ht]
    exact fullOrder_nodup9 I v b

private theorem nodup_getElem_not_mem_take {α : Type*} [DecidableEq α] {l : List α}
    (hl : l.Nodup) (k : Fin l.length) : l[k.val] ∉ (l.take k.val).toFinset := by
  intro hmem
  have hmem' : l[k.val] ∈ l.take k.val := List.mem_toFinset.mp hmem
  have hself : l[k.val] ∈ l := by
    exact List.mem_iff_getElem.mpr ⟨k.val, k.isLt, rfl⟩
  have hidx : l.idxOf l[k.val] = k.val := hl.idxOf_getElem k.val k.isLt
  have hlt := (List.mem_take_iff_idxOf_lt hself).mp hmem'
  rw [hidx] at hlt
  omega

private def RegularityTestIndex9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n) :=
  Σ b : StarOdd9 v, Σ t : Fin 3, Fin (regularityOrder9 S I v b.1 t).length

private abbrev BoundedRegularityTestIndex9 {P : Params9} {n : ℕ}
    (I : IDMap9 P n) (v : EvenSites9 n) :=
  ((StarOdd9 v × Fin 3) × Fin (2 * n + 1))

private noncomputable def prefixRegularBefore9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (b : StarOdd9 v) (t : Fin 3)
    (k : Fin (regularityOrder9 S I v b.1 t).length) (ω : Outcome9 I N) : Prop :=
  let ord := regularityOrder9 S I v b.1 t
  let base := regularityBase9 S I b.1 ω t
  (∀ j c', j < k.val → ord[j]? = some c' →
    (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j))

private noncomputable def badPrefixTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (b : StarOdd9 v) (t : Fin 3)
    (k : Fin (regularityOrder9 S I v b.1 t).length) (ω : Outcome9 I N) : Prop :=
  let ord := regularityOrder9 S I v b.1 t
  let base := regularityBase9 S I b.1 ω t
  prefixRegularBefore9 S I E G v b t k ω ∧
  2 * P.bStar n < |rowDeg E G (anc9 ω ord[k.val])
    (prefixLaw9 E G ω base ord k.val) - 1 / 2|

private def badBoundedRegularityTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (q : BoundedRegularityTestIndex9 I v) (ω : Outcome9 I N) : Prop :=
  ∃ k : Fin (regularityOrder9 S I v q.1.1.1 q.1.2).length,
    k.val = q.2.val ∧ badPrefixTest9 S I E G v q.1.1 q.1.2 k ω

private theorem hitSet_update_anchor9 {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} {E : Fin N → Fin N → Prop} {G : Colour}
    (ω : Outcome9 I N) (c : I.ID) (x : Fin N) (ids : Finset I.ID)
    (hnot : c ∉ ids) :
    hitSet9 E G (Function.update ω (Sum.inl c) x) ids = hitSet9 E G ω ids := by
  classical
  ext y
  simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h d hd
  · have hdne : d ≠ c := by
      intro hdc
      subst d
      exact hnot hd
    have hanc : anc9 (Function.update ω (Sum.inl c) x) d = anc9 ω d := by
      simp [anc9, Function.update, Sum.inl.injEq, hdne]
      rfl
    simpa only [hanc] using h d hd
  · have hdne : d ≠ c := by
      intro hdc
      subst d
      exact hnot hd
    have hanc : anc9 (Function.update ω (Sum.inl c) x) d = anc9 ω d := by
      simp [anc9, Function.update, Sum.inl.injEq, hdne]
      rfl
    simpa only [hanc] using h d hd

private theorem regularityBase_update9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (b : OddSites9 n)
    (ω : Outcome9 I N) (c : I.ID) (x : Fin N) (t : Fin 3) :
    regularityBase9 S I b (Function.update ω (Sum.inl c) x) t = regularityBase9 S I b ω t := by
  classical
  by_cases ht : t.val = 0
  · simp only [regularityBase9, if_pos ht]
    unfold maskedLaw9
    apply congrArg (restrictOr9 (siteSecond9 S b.1))
    change Function.update ω (Sum.inl c) x (Sum.inr b) = ω (Sum.inr b)
    simp [Function.update, Sum.inr_ne_inl]
  · simp only [regularityBase9, if_neg ht]

private theorem prefixLaw_update_anchor9 {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} {E : Fin N → Fin N → Prop} {G : Colour}
    (ω : Outcome9 I N) (c : I.ID) (x : Fin N) (base : Law N) (ord : List I.ID)
    (k : ℕ) (hnot : c ∉ (ord.take k).toFinset) :
    prefixLaw9 E G (Function.update ω (Sum.inl c) x) base ord k =
      prefixLaw9 E G ω base ord k := by
  unfold prefixLaw9
  rw [@hitSet_update_anchor9 P n N M I E G ω c x (ord.take k).toFinset hnot]

private theorem prefixRegularBefore_update9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (b : StarOdd9 v) (t : Fin 3)
    (k : Fin (regularityOrder9 S I v b.1 t).length) (ω : Outcome9 I N)
    (hnodup : (regularityOrder9 S I v b.1 t).Nodup) (x : Fin N) :
    prefixRegularBefore9 S I E G v b t k (Function.update ω (Sum.inl
      (regularityOrder9 S I v b.1 t)[k.val]) x) ↔ prefixRegularBefore9 S I E G v b t k ω := by
  classical
  let ord := regularityOrder9 S I v b.1 t
  let c : I.ID := ord[k.val]
  have hbase : regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t =
      regularityBase9 S I b.1 ω t := @regularityBase_update9 P n N M S I b.1 ω c x t
  have hidxc : ord.idxOf c = k.val := hnodup.idxOf_getElem k.val k.isLt
  have hnotTake (j : ℕ) (hj : j < k.val) : c ∉ (ord.take j).toFinset := by
    intro hc
    have hc' : c ∈ ord.take j := List.mem_toFinset.mp hc
    have hcIn : c ∈ ord := by
      change ord[k.val] ∈ ord
      exact List.mem_iff_getElem.mpr ⟨k.val, k.isLt, rfl⟩
    have hlt := (List.mem_take_iff_idxOf_lt hcIn).mp hc'
    rw [hidxc] at hlt
    omega
  have hdegreeEq (j : ℕ) (c' : I.ID) (hj : j < k.val)
      (hget : ord[j]? = some c') :
      rowDeg E G (anc9 (Function.update ω (Sum.inl c) x) c')
          (prefixLaw9 E G (Function.update ω (Sum.inl c) x)
            (regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t) ord j) =
        rowDeg E G (anc9 ω c') (prefixLaw9 E G ω (regularityBase9 S I b.1 ω t) ord j) := by
    have hget' : j < ord.length ∧ ord[j] = c' := by
      rcases List.getElem?_eq_some_iff.mp hget with ⟨hj', hval⟩
      exact ⟨hj', hval⟩
    have hidxj : ord.idxOf c' = j := by
      rw [← hget'.2]
      exact hnodup.idxOf_getElem j hget'.1
    have hcne : c' ≠ c := by
      intro heq
      rw [heq, hidxc] at hidxj
      omega
    have hanc : anc9 (Function.update ω (Sum.inl c) x) c' = anc9 ω c' := by
      simp [anc9, Function.update, Sum.inl.injEq, hcne]
      rfl
    rw [hbase]
    rw [@prefixLaw_update_anchor9 P n N M I E G ω c x
      (regularityBase9 S I b.1 ω t) ord j (hnotTake j hj)]
    rw [hanc]
  change
    (∀ j c', j < k.val → ord[j]? = some c' →
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 (Function.update ω (Sum.inl c) x) c')
        (prefixLaw9 E G (Function.update ω (Sum.inl c) x)
          (regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t) ord j)) ↔
    (∀ j c', j < k.val → ord[j]? = some c' →
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c')
        (prefixLaw9 E G ω (regularityBase9 S I b.1 ω t) ord j))
  rw [hbase]
  constructor
  · intro h j c' hj hget
    calc
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 (Function.update ω (Sum.inl c) x) c')
          (prefixLaw9 E G (Function.update ω (Sum.inl c) x)
            (regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t) ord j) :=
        h j c' hj hget
      _ = rowDeg E G (anc9 ω c')
          (prefixLaw9 E G ω (regularityBase9 S I b.1 ω t) ord j) := hdegreeEq j c' hj hget
  · intro h j c' hj hget
    calc
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c')
          (prefixLaw9 E G ω (regularityBase9 S I b.1 ω t) ord j) := h j c' hj hget
      _ = rowDeg E G (anc9 (Function.update ω (Sum.inl c) x) c')
          (prefixLaw9 E G (Function.update ω (Sum.inl c) x)
            (regularityBase9 S I b.1 (Function.update ω (Sum.inl c) x) t) ord j) :=
        (hdegreeEq j c' hj hget).symm

private noncomputable def badRegularityTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (v : EvenSites9 n) (q : RegularityTestIndex9 S I v) (ω : Outcome9 I N) : Prop :=
  badPrefixTest9 S I E G v q.1 q.2.1 q.2.2 ω

private theorem law_restrict_degree_mass9 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (A : Finset (Fin N)) (x : Fin N)
    (hm : 0 < ∑ y ∈ A, μ.w y) :
    (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) =
      (∑ y ∈ A, μ.w y) * rowDeg E G x (μ.restrict A hm) := by
  classical
  let m : ℝ := ∑ y ∈ A, μ.w y
  have hm' : 0 < m := hm
  have hdegree : rowDeg E G x (μ.restrict A hm) =
      (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) / m := by
    unfold rowDeg
    simp only [Law.restrict]
    have hfilter : Finset.univ.filter (fun y : Fin N => y ∈ A ∧ Hits E G x y) =
        A.filter (fun y => Hits E G x y) := by
      ext y
      simp
    calc
      (∑ y, (if y ∈ A then μ.w y / m else 0) *
          (if Hits E G x y then 1 else 0)) =
          ∑ y, if y ∈ A ∧ Hits E G x y then μ.w y / m else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hA : y ∈ A <;> by_cases hHit : Hits E G x y <;> simp [hA, hHit]
      _ = ∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y / m := by
            rw [← Finset.sum_filter, hfilter]
      _ = (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) / m := by
            rw [Finset.sum_div]
  calc
    (∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) =
        m * ((∑ y ∈ A.filter (fun y => Hits E G x y), μ.w y) / m) := by
          rw [mul_div_cancel₀ _ (ne_of_gt hm')]
    _ = (∑ y ∈ A, μ.w y) * rowDeg E G x (μ.restrict A hm) := by
          rw [hdegree]

private noncomputable def prefixMass9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID) (k : ℕ) : ℝ :=
  ∑ y ∈ hitSet9 E G ω (ord.take k).toFinset, base.w y

private theorem prefixMass_lower9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID) :
    ∀ k : ℕ, k ≤ ord.length →
      (∀ j c', j < k → ord[j]? = some c' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j)) →
      (49 / 100 : ℝ) ^ k ≤ prefixMass9 E G ω base ord k := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk hprev
      have hmass : prefixMass9 E G ω base ord 0 = 1 := by
        simp [prefixMass9, hitSet9, base.sum_eq_one]
      rw [hmass]
      norm_num
  | succ k ih =>
      intro hk hprev
      have hklen : k < ord.length := by omega
      let c : I.ID := ord[k]
      have hkc : ord[k]? = some c := by simp [c]
      have hcurrent := hprev k c (by omega) hkc
      have hprev' : ∀ j c', j < k → ord[j]? = some c' →
          (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j) := by
        intro j c' hj hget
        exact hprev j c' (by omega) hget
      have hmassPrev := ih (by omega) hprev'
      have hmassPrevPos : 0 < prefixMass9 E G ω base ord k := by
        exact lt_of_lt_of_le (by positivity : 0 < (49 / 100 : ℝ) ^ k) hmassPrev
      let A := hitSet9 E G ω (ord.take k).toFinset
      have hmassA : 0 < ∑ y ∈ A, base.w y := by
        change 0 < prefixMass9 E G ω base ord k at hmassPrevPos
        simpa [prefixMass9, A] using hmassPrevPos
      have hprefix : prefixLaw9 E G ω base ord k = base.restrict A hmassPrevPos := by
        change restrictOr9 base A = base.restrict A hmassPrevPos
        unfold restrictOr9
        rw [dif_pos hmassA]
      have htake : ord.take k ++ [ord[k]] = ord.take (k + 1) :=
        List.take_concat_get' ord k hklen
      have hids : (ord.take (k + 1)).toFinset = insert c (ord.take k).toFinset := by
        calc
          (ord.take (k + 1)).toFinset = (ord.take k ++ [ord[k]]).toFinset := by rw [← htake]
          _ = insert c (ord.take k).toFinset := by
            rw [List.toFinset_append]
            simp [c, Finset.union_comm]
      have hset : hitSet9 E G ω (insert c (ord.take k).toFinset) =
          (hitSet9 E G ω (ord.take k).toFinset).filter
            (fun y => Hits E G (anc9 ω c) y) := by
        ext y
        simp [hitSet9, c, Finset.mem_insert, and_left_comm, and_comm, and_assoc]
      have hrec : prefixMass9 E G ω base ord (k + 1) =
          prefixMass9 E G ω base ord k * rowDeg E G (anc9 ω c) (base.restrict A hmassPrevPos) := by
        unfold prefixMass9
        rw [hids]
        rw [hset]
        exact law_restrict_degree_mass9 E G base A (anc9 ω c) hmassA
      rw [hprefix] at hcurrent
      rw [hrec]
      have hdegree_nonneg : 0 ≤ rowDeg E G (anc9 ω c) (base.restrict A hmassPrevPos) :=
        le_trans (by norm_num) hcurrent
      calc
        (49 / 100 : ℝ) ^ (k + 1) = (49 / 100 : ℝ) ^ k * (49 / 100 : ℝ) := by rw [pow_succ]
        _ ≤ prefixMass9 E G ω base ord k *
            rowDeg E G (anc9 ω c) (base.restrict A hmassPrevPos) :=
          mul_le_mul hmassPrev hcurrent (by norm_num) (le_trans (by positivity) hmassPrev)

private theorem orderRegular_prefix_degrees9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID)
    (hord : orderRegular9 E G ω base ord) (hbstar : P.bStar n ≤ 1 / 200) :
    ∀ m : ℕ, m ≤ ord.length → ∀ j c', j < m → ord[j]? = some c' →
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j) := by
  classical
  intro m
  induction m with
  | zero =>
      intro hm j c' hj hget
      omega
  | succ m ih =>
      intro hm j c' hj hget
      by_cases hjm : j < m
      · exact ih (by omega) j c' hjm hget
      · have hjEq : j = m := by omega
        subst j
        have hprev : ∀ l d, l < m → ord[l]? = some d →
            (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω d) (prefixLaw9 E G ω base ord l) := by
          intro l d hlt hget'
          exact ih (by omega) l d hlt hget'
        have hregular := hord m c' hget hprev
        have hlow := (abs_le.mp hregular).1
        have hbstarBound : 2 * P.bStar n ≤ 1 / 100 := by nlinarith
        linarith

private theorem coreHit_mass_lower_regular9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (b : StarOdd9 v)
    (hcore : orderRegular9 E G ω (siteSecond9 S b.1.1) (coreOrder9 I v b.1))
    (hbstar : P.bStar n ≤ 1 / 200) :
    (49 / 100 : ℝ) ^ coreCount9 I v b.1 ≤
      ∑ y ∈ coreHitSet9 E G ω v b.1, (siteSecond9 S b.1.1).w y := by
  classical
  let ord := coreOrder9 I v b.1
  have hdegrees := orderRegular_prefix_degrees9 S I E G ω (siteSecond9 S b.1.1)
    ord hcore hbstar
  have hlen : ord.length ≤ coreCount9 I v b.1 := by
    simp [ord, coreOrder9, coreCount9]
    exact Finset.card_erase_le
  have hmassLen : (49 / 100 : ℝ) ^ ord.length ≤
      prefixMass9 E G ω (siteSecond9 S b.1.1) ord ord.length := by
    exact prefixMass_lower9 S I E G ω (siteSecond9 S b.1.1) ord ord.length le_rfl (hdegrees ord.length le_rfl)
  have hpow : (49 / 100 : ℝ) ^ coreCount9 I v b.1 ≤ (49 / 100 : ℝ) ^ ord.length :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hlen
  have hmassEq : prefixMass9 E G ω (siteSecond9 S b.1.1) ord ord.length =
      ∑ y ∈ coreHitSet9 E G ω v b.1, (siteSecond9 S b.1.1).w y := by
    unfold prefixMass9
    change (∑ y ∈ hitSet9 E G ω
        ((coreIDs9 I v b.1).toList.take ((coreIDs9 I v b.1).toList.length)).toFinset,
          (siteSecond9 S b.1.1).w y) = _
    rw [List.take_length]
    simp [coreHitSet9]
  calc
    (49 / 100 : ℝ) ^ coreCount9 I v b.1 ≤ (49 / 100 : ℝ) ^ ord.length := hpow
    _ ≤ prefixMass9 E G ω (siteSecond9 S b.1.1) ord ord.length := hmassLen
    _ = ∑ y ∈ coreHitSet9 E G ω v b.1, (siteSecond9 S b.1.1).w y := hmassEq

private theorem exists_badPrefix_of_not_orderRegular9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (ord : List I.ID)
    (hn : ¬ orderRegular9 E G ω base ord) :
    ∃ k : Fin ord.length,
      (∀ j c', j < k.val → ord[j]? = some c' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base ord j)) ∧
      2 * P.bStar n < |rowDeg E G (anc9 ω ord[k.val])
        (prefixLaw9 E G ω base ord k.val) - 1 / 2| := by
  classical
  unfold orderRegular9 at hn
  push_neg at hn
  rcases hn with ⟨k, c, hkc, hprev, hfail⟩
  rcases List.getElem?_eq_some_iff.mp hkc with ⟨hk, hval⟩
  let kFin : Fin ord.length := ⟨k, hk⟩
  have hfail' : 2 * P.bStar n <
      |rowDeg E G (anc9 ω ord[kFin.val]) (prefixLaw9 E G ω base ord k) - 1 / 2| := by
    have hfail'' := hfail
    rw [← hval] at hfail''
    simpa [kFin] using hfail''
  refine ⟨kFin, ?_, ?_⟩
  · simpa using hprev
  · simpa using hfail'

private theorem exists_badRegularityTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (hbad : ¬ starRegular9 S E G ω v) :
    ∃ q : RegularityTestIndex9 S I v, badRegularityTest9 S I E G v q ω := by
  classical
  unfold starRegular9 at hbad
  push_neg at hbad
  rcases hbad with ⟨b, hadj, horders⟩
  by_cases hmasked : orderRegular9 E G ω (maskedLaw9 S ω b) (fullOrder9 I v b)
  · by_cases hunmasked : orderRegular9 E G ω (siteSecond9 S b.1) (fullOrder9 I v b)
    · have hcore : ¬ orderRegular9 E G ω (siteSecond9 S b.1) (coreOrder9 I v b) :=
        horders hmasked hunmasked
      obtain ⟨k, hprev, htail⟩ := exists_badPrefix_of_not_orderRegular9 S I E G ω
        (siteSecond9 S b.1) (coreOrder9 I v b) hcore
      let b' : StarOdd9 v := ⟨b, hadj⟩
      let t : Fin 3 := ⟨2, by omega⟩
      refine ⟨⟨b', ⟨t, k⟩⟩, ?_⟩
      simpa [badRegularityTest9, badPrefixTest9, prefixRegularBefore9, regularityOrder9,
        regularityBase9, t, b'] using
        And.intro hprev htail
    · obtain ⟨k, hprev, htail⟩ := exists_badPrefix_of_not_orderRegular9 S I E G ω
        (siteSecond9 S b.1) (fullOrder9 I v b) hunmasked
      let b' : StarOdd9 v := ⟨b, hadj⟩
      let t : Fin 3 := ⟨1, by omega⟩
      refine ⟨⟨b', ⟨t, k⟩⟩, ?_⟩
      simpa [badRegularityTest9, badPrefixTest9, prefixRegularBefore9, regularityOrder9,
        regularityBase9, t, b'] using
        And.intro hprev htail
  · obtain ⟨k, hprev, htail⟩ := exists_badPrefix_of_not_orderRegular9 S I E G ω
      (maskedLaw9 S ω b) (fullOrder9 I v b) hmasked
    let b' : StarOdd9 v := ⟨b, hadj⟩
    let t : Fin 3 := ⟨0, by omega⟩
    refine ⟨⟨b', ⟨t, k⟩⟩, ?_⟩
    simpa [badRegularityTest9, badPrefixTest9, prefixRegularBefore9, regularityOrder9,
      regularityBase9, t, b'] using
      And.intro hprev htail

private theorem regularityOrder_length_le_seen_add_one9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n) (b : StarOdd9 v)
    (t : Fin 3) :
    (regularityOrder9 S I v b t).length ≤ (I.seen b.1).card + 1 := by
  classical
  let O := outerIDs9 I v b.1
  let K := coreIDs9 I v b.1
  have hO : O ⊆ I.seen b.1 := by
    intro x hx
    exact (Finset.mem_sdiff.mp (by simpa [O, outerIDs9] using hx)).1
  have hK : K ⊆ I.seen b.1 := by
    intro x hx
    rcases (by simpa [K, coreIDs9] using hx) with ⟨_, hxSeen, _⟩
    exact hxSeen
  have hdis : Disjoint O K := by
    rw [Finset.disjoint_left]
    intro x hxO hxK
    rcases (by simpa [O, outerIDs9] using hxO) with ⟨_, hxNotCore⟩
    rcases (by simpa [K, coreIDs9] using hxK) with ⟨_, _, hxCore⟩
    exact hxNotCore hxCore
  have hcard : O.card + K.card ≤ (I.seen b.1).card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset hO hK)
  by_cases ht : t.val = 2
  · simp [regularityOrder9, ht, coreOrder9, K]
    exact Nat.le_trans (Finset.card_le_card hK) (Nat.le_add_right _ _)
  · have hfull : (regularityOrder9 S I v b t).length = O.card + K.card + 1 := by
      simp [regularityOrder9, ht, fullOrder9, O, K, List.length_append]
      omega
    rw [hfull]
    omega

private theorem starOdd_card_le9 {n : ℕ} (v : EvenSites9 n) : Fintype.card (StarOdd9 v) ≤ n := by
  classical
  let Adj : CubeVertex n → Prop := fun b => (cube n).Adj v.1 b
  let e : StarOdd9 v → {b : CubeVertex n // Adj b} := fun b => ⟨b.1.1, b.2⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    change a.1.1 = b.1.1
    exact congrArg (fun z : {y : CubeVertex n // Adj y} => z.1) hab
  have hcard : Fintype.card {b : CubeVertex n // Adj b} =
      (Finset.univ.filter Adj).card := by
    simpa [Adj] using (Fintype.card_subtype (fun b : CubeVertex n => Adj b))
  calc
    Fintype.card (StarOdd9 v) ≤ Fintype.card {b : CubeVertex n // Adj b} :=
      Fintype.card_le_of_injective e he
    _ = (Finset.univ.filter Adj).card := hcard
    _ ≤ n := by simpa [Adj] using cube_adj_neighbors_card_le n v.1

private theorem boundedRegularityTestIndex_card_le9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (v : EvenSites9 n)
    (hscale : ScaleExps9 P) (hAt : ScalesAt9 P n) :
    Fintype.card (BoundedRegularityTestIndex9 I v) ≤ 9 * n ^ 2 := by
  classical
  rcases hscale with ⟨_, hepsσ, _, _, _⟩
  rcases hAt with ⟨hn, hm, _, _, _, _, _, _⟩
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hexpT : 1 - (P.σ : ℝ) + P.eps ≤ 1 := by linarith
  have hT : P.idBudget n ≤ (n : ℝ) := by
    unfold Params9.idBudget
    simpa using Real.rpow_le_rpow_of_exponent_le hnR hexpT
  have hmR : (P.m n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
  have hseenR (b : StarOdd9 v) :
      ((I.seen b.1).card : ℝ) ≤ 2 * (n : ℝ) := by
    have hodd := I.odd_ids b.1.1 b.1.2
    have hodd' : ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := by
      simpa [IDMap9.seen] using hodd
    calc
      ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := hodd'
      _ ≤ (n : ℝ) + (n : ℝ) := add_le_add hT hmR
      _ = 2 * (n : ℝ) := by ring
  have hlen (b : StarOdd9 v) (t : Fin 3) :
      (regularityOrder9 S I v b.1 t).length ≤ 2 * n + 1 := by
    have h := regularityOrder_length_le_seen_add_one9 S I v b t
    have hseen : (I.seen b.1).card ≤ 2 * n := by exact_mod_cast hseenR b
    omega
  have hstar := starOdd_card_le9 v
  have hcard : Fintype.card (BoundedRegularityTestIndex9 I v) ≤ 9 * n ^ 2 := by
    have hcardEq : Fintype.card (BoundedRegularityTestIndex9 I v) =
        Fintype.card (StarOdd9 v) * 3 * (2 * n + 1) := by
      dsimp [BoundedRegularityTestIndex9]
      rw [Fintype.card_prod, Fintype.card_prod]
      simp [Nat.mul_assoc]
    rw [hcardEq]
    calc
      _ ≤ n * 3 * (2 * n + 1) := Nat.mul_le_mul_right (2 * n + 1)
        (Nat.mul_le_mul_right 3 hstar)
      _ ≤ 9 * n ^ 2 := by nlinarith [hn]
  exact hcard

private theorem exists_badBoundedRegularityTest9 {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (hscale : ScaleExps9 P) (hAt : ScalesAt9 P n)
    (hbad : ¬ starRegular9 S E G ω v) :
    ∃ q : BoundedRegularityTestIndex9 I v, badBoundedRegularityTest9 S I E G v q ω := by
  classical
  obtain ⟨q, hq⟩ := exists_badRegularityTest9 S I E G ω v hbad
  rcases q with ⟨b, ⟨t, k⟩⟩
  have hlen : (regularityOrder9 S I v b.1 t).length ≤ 2 * n + 1 := by
    have h := regularityOrder_length_le_seen_add_one9 S I v b t
    have hT : P.idBudget n ≤ (n : ℝ) := by
      rcases hscale with ⟨_, hepsσ, _, _, _⟩
      rcases hAt with ⟨hn, _, _, _, _, _, _, _⟩
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hexpT : 1 - (P.σ : ℝ) + P.eps ≤ 1 := by linarith
      unfold Params9.idBudget
      simpa using Real.rpow_le_rpow_of_exponent_le hnR hexpT
    have hmR : (P.m n : ℝ) ≤ (n : ℝ) := by
      rcases hAt with ⟨_, hm, _, _, _, _, _, _⟩
      exact_mod_cast hm
    have hodd : ((I.seen b.1).card : ℝ) ≤ 2 * (n : ℝ) := by
      have hbound := I.odd_ids b.1.1 b.1.2
      have hbound' : ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := by
        simpa [IDMap9.seen] using hbound
      have hodd2 : ((I.seen b.1).card : ℝ) ≤ 2 * (n : ℝ) := by
        calc
          ((I.seen b.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := hbound'
          _ ≤ (n : ℝ) + (n : ℝ) := add_le_add hT hmR
          _ = 2 * (n : ℝ) := by ring
      exact hodd2
    have hseen : (I.seen b.1).card ≤ 2 * n := by exact_mod_cast hodd
    omega
  let k' : Fin (2 * n + 1) := ⟨k.val, lt_of_lt_of_le k.isLt hlen⟩
  let q' : BoundedRegularityTestIndex9 I v := ((b, t), k')
  refine ⟨q', ?_⟩
  refine ⟨k, ?_, ?_⟩
  · rfl
  · simpa [badRegularityTest9] using hq

private theorem regularity_polynomial_tail9 {u χ : ℝ} (hu : 0 < u) (hχ : 0 < χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      18 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (u + 8 * χ))) ≤
          Real.exp (-((n : ℝ) ^ u / 2)) ∧
        Real.log (100 / 49) ≤ (n : ℝ) ^ u := by
  have hlittle : (fun x : ℝ => 16 * Real.log x) =o[atTop] fun x => x ^ u := by
    have h := (isLittleO_log_rpow_rpow_atTop 1 hu).const_mul_left 16
    simpa using h
  have hnat : (fun n : ℕ => 16 * Real.log (n : ℝ)) =o[atTop]
      fun n => (n : ℝ) ^ u := by
    exact (hlittle.comp_tendsto tendsto_natCast_atTop_atTop).congr_left (fun _ => rfl)
  obtain ⟨nL, hL⟩ := Filter.eventually_atTop.mp hnat.eventuallyLE
  have hpowTendsto : Tendsto (fun n : ℕ => (n : ℝ) ^ u) atTop atTop := by
    refine Tendsto.congr' ?_ ((tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop)
    filter_upwards [] with n
    rfl
  obtain ⟨nR, hR⟩ := Filter.eventually_atTop.mp
    (hpowTendsto.eventually_ge_atTop (Real.log (100 / 49)))
  refine ⟨max (max nL 18) nR, ?_⟩
  intro n hn
  have hnLR : max nL 18 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnR : nR ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnL : nL ≤ n := le_trans (Nat.le_max_left _ _) hnLR
  have hn18 : 18 ≤ n := le_trans (Nat.le_max_right _ _) hnLR
  have hnReal : 18 ≤ (n : ℝ) := by exact_mod_cast hn18
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hpowPos : 0 < (n : ℝ) ^ u := Real.rpow_pos_of_pos (by positivity) _
  have hnorm := hL n hnL
  have h16log : 16 * Real.log (n : ℝ) ≤ (n : ℝ) ^ u := by
    have h1 : 0 ≤ 16 * Real.log (n : ℝ) := by positivity
    have h2 : 0 ≤ (n : ℝ) ^ u := le_of_lt hpowPos
    simpa [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2] using hnorm
  have hlog18 : Real.log 18 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hnReal
  have hlogFactor : Real.log (18 * (n : ℝ) ^ 2) ≤ (n : ℝ) ^ u / 2 := by
    have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
    have hlogmul : Real.log (18 * (n : ℝ) ^ 2) = Real.log 18 + 2 * Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hn2), Real.log_pow]
      norm_num
    rw [hlogmul]
    nlinarith
  have hA : (n : ℝ) ^ u ≤ (n : ℝ) ^ (u + 8 * χ) := by
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hfactor :
      18 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (u + 8 * χ))) =
        Real.exp (Real.log (18 * (n : ℝ) ^ 2) - (n : ℝ) ^ (u + 8 * χ)) := by
    have hpos : 0 < 18 * (n : ℝ) ^ 2 := by positivity
    have hM : 18 * (n : ℝ) ^ 2 = Real.exp (Real.log (18 * (n : ℝ) ^ 2)) :=
      (Real.exp_log hpos).symm
    calc
      _ = Real.exp (Real.log (18 * (n : ℝ) ^ 2)) *
          Real.exp (-((n : ℝ) ^ (u + 8 * χ))) :=
            congrArg (fun z : ℝ => z * Real.exp (-((n : ℝ) ^ (u + 8 * χ)))) hM
      _ = Real.exp (Real.log (18 * (n : ℝ) ^ 2) + -((n : ℝ) ^ (u + 8 * χ))) := by
            exact (Real.exp_add _ _).symm
      _ = Real.exp (Real.log (18 * (n : ℝ) ^ 2) - (n : ℝ) ^ (u + 8 * χ)) := by
            congr 1 <;> ring
  constructor
  · calc
      18 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (u + 8 * χ))) =
          Real.exp (Real.log (18 * (n : ℝ) ^ 2) - (n : ℝ) ^ (u + 8 * χ)) := hfactor
      _ ≤ Real.exp (-((n : ℝ) ^ u / 2)) := by
        apply Real.exp_le_exp.mpr
        linarith
  · exact hR n hnR

private theorem mask_log_bound9 {a m : ℝ}
    (hm : (1 / 2 : ℝ) * Real.exp (-a) ≤ m) : -Real.log m ≤ a + Real.log 2 := by
  have hlow : 0 < (1 / 2 : ℝ) * Real.exp (-a) := mul_pos (by norm_num) (Real.exp_pos _)
  have hmpos : 0 < m := lt_of_lt_of_le hlow hm
  have hlog := Real.log_le_log hlow hm
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hexact : Real.log ((1 / 2 : ℝ) * Real.exp (-a)) = -Real.log 2 - a := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), hhalf, Real.log_exp]
    ring
  rw [hexact] at hlog
  linarith

private theorem prefix_log_bound9 {k : ℕ} {m : ℝ}
    (hm : (49 / 100 : ℝ) ^ k ≤ m) :
    -Real.log m ≤ (k : ℝ) * Real.log (100 / 49) := by
  have hbase : (0 : ℝ) < 49 / 100 := by norm_num
  have hpow : 0 < (49 / 100 : ℝ) ^ k := pow_pos hbase _
  have hmpos : 0 < m := lt_of_lt_of_le hpow hm
  have hlog := Real.log_le_log hpow hm
  have hratio : Real.log (49 / 100 : ℝ) = -Real.log (100 / 49) := by
    have hinv : (49 / 100 : ℝ) = (100 / 49)⁻¹ := by norm_num
    rw [hinv, Real.log_inv]
  rw [Real.log_pow, hratio] at hlog
  linarith

private theorem law_restrict_supported9 {N : ℕ} {Y A : Finset (Fin N)} {μ : Law N}
    (hμ : μ.SupportedIn Y) (hm : 0 < ∑ y ∈ A, μ.w y) :
    (μ.restrict A hm).SupportedIn Y := by
  intro y hy
  by_cases hA : y ∈ A
  · simp [Law.restrict, hA, hμ y hy]
  · simp [Law.restrict, hA]

private theorem rowDeg_lipschitz_l1_9 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (x : Fin N) (μ ν : Law N) :
    |rowDeg E G x μ - rowDeg E G x ν| ≤ ∑ y, |μ.w y - ν.w y| := by
  classical
  have hsum : rowDeg E G x μ - rowDeg E G x ν =
      ∑ y, (μ.w y - ν.w y) * (if Hits E G x y then 1 else 0) := by
    rw [rowDeg, rowDeg, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hsum]
  calc
    |∑ y, (μ.w y - ν.w y) * (if Hits E G x y then 1 else 0)| ≤
        ∑ y, |(μ.w y - ν.w y) * (if Hits E G x y then 1 else 0)| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun y => (μ.w y - ν.w y) * (if Hits E G x y then 1 else 0)) Finset.univ
    _ ≤ ∑ y, |μ.w y - ν.w y| := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases h : Hits E G x y <;> simp [h]

private theorem law_restrict_l1_bound9 {N : ℕ} (μ ν : Law N) (A : Finset (Fin N))
    (hμ : 0 < ∑ y ∈ A, μ.w y) (hν : 0 < ∑ y ∈ A, ν.w y)
    (δ : ℝ) (hL1 : ∑ y, |μ.w y - ν.w y| ≤ δ) :
    ∑ y, |(μ.restrict A hμ).w y - (ν.restrict A hν).w y| ≤
      2 * δ / (∑ y ∈ A, μ.w y) := by
  classical
  let a : ℝ := ∑ y ∈ A, μ.w y
  let b : ℝ := ∑ y ∈ A, ν.w y
  have ha : 0 < a := hμ
  have hb : 0 < b := hν
  have hmassDiff : |a - b| ≤ δ := by
    have hdiff : a - b = ∑ y ∈ A, (μ.w y - ν.w y) := by
      dsimp [a, b]
      rw [Finset.sum_sub_distrib]
    calc
      |a - b| = |∑ y ∈ A, (μ.w y - ν.w y)| := by rw [hdiff]
      _ ≤ ∑ y ∈ A, |μ.w y - ν.w y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |μ.w y - ν.w y| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        intro y hy hnot
        positivity
      _ ≤ δ := hL1
  have hpoint (y : Fin N) :
      |(μ.restrict A hμ).w y - (ν.restrict A hν).w y| ≤
        if y ∈ A then |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) else 0 := by
    by_cases hy : y ∈ A
    · simp [Law.restrict, hy, a, b]
      have hfrac : μ.w y / a - ν.w y / b =
          (μ.w y - ν.w y) / a + ν.w y * (b - a) / (a * b) := by
        field_simp [ne_of_gt ha, ne_of_gt hb]
        ring
      rw [hfrac]
      calc
        |(μ.w y - ν.w y) / a + ν.w y * (b - a) / (a * b)| ≤
            |(μ.w y - ν.w y) / a| + |ν.w y * (b - a) / (a * b)| := abs_add_le _ _
        _ = |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) := by
          simp [abs_div, abs_mul, abs_of_nonneg (ν.nonneg y), abs_of_pos ha,
            abs_of_pos hb, abs_sub_comm]
    · simp [Law.restrict, hy]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y hy => hpoint y)
  have hsumBound :
      (∑ y, if y ∈ A then |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) else 0) ≤
        δ / a + δ / a := by
    have hfirstEq : (∑ y ∈ A, |μ.w y - ν.w y| / a) =
        (∑ y ∈ A, |μ.w y - ν.w y|) / a := by rw [Finset.sum_div]
    have hsecondEq : (∑ y ∈ A, ν.w y * |a - b| / (a * b)) =
        (∑ y ∈ A, ν.w y) * |a - b| / (a * b) := by
      calc
        (∑ y ∈ A, ν.w y * |a - b| / (a * b)) =
            ∑ y ∈ A, ν.w y * (|a - b| / (a * b)) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = (∑ y ∈ A, ν.w y) * (|a - b| / (a * b)) := by
          simpa using (Finset.sum_mul (s := A) (f := fun y => ν.w y)
            (a := |a - b| / (a * b))).symm
        _ = (∑ y ∈ A, ν.w y) * |a - b| / (a * b) := by ring
    calc
      (∑ y, if y ∈ A then |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) else 0) =
          (∑ y ∈ A, |μ.w y - ν.w y| / a) +
            (∑ y ∈ A, ν.w y * |a - b| / (a * b)) := by
              simp only [Finset.sum_ite_mem]
              rw [Finset.sum_add_distrib]
              simp
      _ = (∑ y ∈ A, |μ.w y - ν.w y|) / a +
            (∑ y ∈ A, ν.w y) * |a - b| / (a * b) := by rw [hfirstEq, hsecondEq]
      _ ≤ δ / a + δ / a := by
        have hsumErr : (∑ y ∈ A, |μ.w y - ν.w y|) ≤ δ := by
          calc
            (∑ y ∈ A, |μ.w y - ν.w y|) ≤ ∑ y, |μ.w y - ν.w y| := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
              intro y hy hnot
              positivity
            _ ≤ δ := hL1
        have hfirst := div_le_div_of_nonneg_right hsumErr (le_of_lt ha)
        have hsecond : b * |a - b| / (a * b) ≤ δ / a := by
          have habs : |a - b| ≤ δ := hmassDiff
          have hmul := mul_le_mul_of_nonneg_left habs (le_of_lt hb)
          have hquot : b * |a - b| / (a * b) = |a - b| / a := by
            field_simp [ne_of_gt ha, ne_of_gt hb]
          rw [hquot]
          exact div_le_div_of_nonneg_right habs (le_of_lt ha)
        rw [show (∑ y ∈ A, ν.w y) = b by rfl]
        exact add_le_add hfirst hsecond
  calc
    (∑ y, |(μ.restrict A hμ).w y - (ν.restrict A hν).w y|) ≤
        ∑ y, if y ∈ A then |μ.w y - ν.w y| / a + ν.w y * |a - b| / (a * b) else 0 := hsum
    _ ≤ δ / a + δ / a := hsumBound
    _ = 2 * δ / (∑ y ∈ A, μ.w y) := by dsimp [a]; ring

private theorem normalize_l1_perturbation9 {N : ℕ} (Q ν : Law N) (ψ : Fin N → ℝ)
    (B δ : ℝ) (hB : 0 ≤ B) (hBhalf : B ≤ 1 / 2)
    (hψ : ∀ y, |ψ y| ≤ B)
    (herr : ∑ y, |Q.w y - (1 + ψ y) * ν.w y| ≤ δ) :
    ∃ Z > 0, ∃ R : Law N,
      (∀ y, R.w y = (1 + ψ y) * ν.w y / Z) ∧
      ∑ y, |Q.w y - R.w y| ≤ 2 * δ := by
  classical
  let Z : ℝ := ∑ y, (1 + ψ y) * ν.w y
  have hZ : 0 < Z := by
    have hterm (y : Fin N) : (1 / 2 : ℝ) * ν.w y ≤ (1 + ψ y) * ν.w y := by
      have hψlower : 1 / 2 ≤ 1 + ψ y := by
        have := (abs_le.mp (hψ y)).1
        linarith
      exact mul_le_mul_of_nonneg_right hψlower (ν.nonneg y)
    have hsum : (1 / 2 : ℝ) ≤ Z := by
      dsimp [Z]
      calc
        (1 / 2 : ℝ) = (1 / 2 : ℝ) * ∑ y, ν.w y := by rw [ν.sum_eq_one]; ring
        _ = ∑ y, (1 / 2 : ℝ) * ν.w y := by rw [Finset.mul_sum]
        _ ≤ ∑ y, (1 + ψ y) * ν.w y := Finset.sum_le_sum fun y hy => hterm y
    linarith
  let R : Law N :=
    { w := fun y => (1 + ψ y) * ν.w y / Z
      nonneg := by
        intro y
        exact div_nonneg (mul_nonneg (by linarith [(abs_le.mp (hψ y)).1]) (ν.nonneg y)) hZ.le
      sum_eq_one := by
        rw [← Finset.sum_div]
        dsimp [Z]
        exact div_self (ne_of_gt hZ) }
  have hRw (y : Fin N) : R.w y = (1 + ψ y) * ν.w y / Z := rfl
  have hraw (y : Fin N) : (1 + ψ y) * ν.w y = R.w y * Z := by
    rw [hRw]
    field_simp [ne_of_gt hZ]
  have hnormErr : ∑ y, |(1 + ψ y) * ν.w y - R.w y| = |Z - 1| := by
    calc
      (∑ y, |(1 + ψ y) * ν.w y - R.w y|) = ∑ y, R.w y * |Z - 1| := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hraw]
        have hnonneg := R.nonneg y
        rw [show R.w y * Z - R.w y = R.w y * (Z - 1) by ring,
          abs_mul, abs_of_nonneg hnonneg]
      _ = (∑ y, R.w y) * |Z - 1| := by rw [Finset.sum_mul]
      _ = |Z - 1| := by rw [R.sum_eq_one]; ring
  have hmassDiff : |Z - 1| ≤ δ := by
    have hsum : Z - 1 = ∑ y, ((1 + ψ y) * ν.w y - Q.w y) := by
      calc
        Z - 1 = (∑ y, (1 + ψ y) * ν.w y) - ∑ y, Q.w y := by simp [Z, Q.sum_eq_one]
        _ = ∑ y, ((1 + ψ y) * ν.w y - Q.w y) := by rw [Finset.sum_sub_distrib]
    rw [hsum]
    calc
      |∑ y, ((1 + ψ y) * ν.w y - Q.w y)| ≤
          ∑ y, |(1 + ψ y) * ν.w y - Q.w y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, |Q.w y - (1 + ψ y) * ν.w y| := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [abs_sub_comm]
      _ ≤ δ := herr
  have hL1 : ∑ y, |Q.w y - R.w y| ≤ 2 * δ := by
    calc
      (∑ y, |Q.w y - R.w y|) ≤
          ∑ y, (|Q.w y - (1 + ψ y) * ν.w y| + |(1 + ψ y) * ν.w y - R.w y|) := by
            apply Finset.sum_le_sum
            intro y hy
            exact abs_sub_le _ _ _
      _ = (∑ y, |Q.w y - (1 + ψ y) * ν.w y|) +
          ∑ y, |(1 + ψ y) * ν.w y - R.w y| := by rw [Finset.sum_add_distrib]
      _ ≤ δ + δ := add_le_add herr (by rw [hnormErr]; exact hmassDiff)
      _ = 2 * δ := by ring
  exact ⟨Z, hZ, R, hRw, hL1⟩

private theorem boundedRegularityTest_probability_le9 {P : Params9} (hP : P.Valid)
    {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n)
    (hCore : CoreInput9 P κ E X Y G M S I) (v : EvenSites9 n)
    (q : BoundedRegularityTestIndex9 I v) (hPoly : Real.log (100 / 49) ≤ (n : ℝ) ^ P.u) :
    (rawLaw9 S I).pr (badBoundedRegularityTest9 S I E G v q) ≤
      2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
  classical
  rcases hP with ⟨_, _, _, _, hChi, _, _⟩
  have hχpos : 0 < (P.χ : ℝ) := by exact_mod_cast hChi.1
  rcases hCore with ⟨hN, hPrep, hDeep, hTags, hMasks, hTools, hScale, hAt⟩
  rcases hPrep with ⟨_, hPrepLaw⟩
  rcases hScale with ⟨_, _, hu, _, _⟩
  rcases hAt with ⟨hn, _, _, _, hfilter, hfirst, _, _⟩
  let edge : StarOdd9 v := q.1.1
  let t : Fin 3 := q.1.2
  let ord := regularityOrder9 S I v edge.1 t
  by_cases hvalid : q.2.val < ord.length
  · let k : Fin ord.length := ⟨q.2.val, hvalid⟩
    let c : I.ID := ord[k.val]
    let w : ℝ := (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1
    have hwd : w ≤ (n : ℝ) ^ (P.xD : ℝ) := by
      dsimp [w]
      have hextra : 0 ≤ (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) := by positivity
      calc
        (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 ≤
            (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 +
              (n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)) := by linarith
        _ ≤ (n : ℝ) ^ (P.xD : ℝ) := hfirst
    have hgap : w - (n : ℝ) ^ (P.xD : ℝ) ≤ -((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))) := by
      dsimp [w]
      linarith [hfirst]
    let α : Law N := M.μ (S.tag c.slice)
    have htagC := hTags c.slice
    rcases hPrepLaw (S.tag c.slice) htagC with ⟨hαX, _, hαW, _, _⟩
    let ν : Law N := siteSecond9 S edge.1
    let tagEdge := S.tag (specialWord9 (P.m n) edge.1.1)
    have htagEdge := hTags (specialWord9 (P.m n) edge.1.1)
    rcases hPrepLaw tagEdge htagEdge with ⟨_, hνY₀, _, hνW₀, _⟩
    have hνY : ν.SupportedIn Y := by simpa [ν, siteSecond9, tagEdge] using hνY₀
    have hνW : ν.WidthLE (P.Ss (n : ℝ)) := by simpa [ν, siteSecond9, tagEdge] using hνW₀
    have htest : (FinProb.pi (inputLaw9 S I)).pr (badBoundedRegularityTest9 S I E G v q) ≤
        2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
      refine pi_pr_slice_le (inputLaw9 S I) (Sum.inl c)
        (fun ω => badBoundedRegularityTest9 S I E G v q ω)
        (2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))))) ?_
      intro ξ hξ
      let ωbase : Outcome9 I N := fun j =>
        if h : j = Sum.inl c then
          cast (congrArg (Val9 I N) h.symm)
            (Classical.choice (nonempty_of_probability (inputLaw9 S I (Sum.inl c))))
        else ξ ⟨j, h⟩
      change (inputLaw9 S I (Sum.inl c)).pr
        (fun x => badBoundedRegularityTest9 S I E G v q
          (Function.update ωbase (Sum.inl c) x)) ≤
          2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))))
      have hprod :
          ∏ j : {j // j ∉ ({Sum.inl c} : Finset (I.ID ⊕ OddSites9 n))},
              (inputLaw9 S I j.1).w (ξ ⟨j.1, by simpa using j.2⟩) ≠ 0 := by
        simpa [FinProb.pi] using hξ
      let jm : {j // j ∉ ({Sum.inl c} : Finset (I.ID ⊕ OddSites9 n))} :=
        ⟨Sum.inr edge.1, by simp⟩
      have hmaskW : (S.maskLaw edge.1).w (msk9 ωbase edge.1) ≠ 0 := by
        have hfactor := (Finset.prod_ne_zero_iff.mp hprod) jm (Finset.mem_univ jm)
        simpa [inputLaw9, msk9, ωbase, jm, Sum.inr_ne_inl] using hfactor
      have hmaskMass := hMasks.1 edge.1 (msk9 ωbase edge.1) hmaskW
      let mask := msk9 ωbase edge.1
      have hlow : 0 < (1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ P.u)) :=
        mul_pos (by norm_num) (Real.exp_pos (-((n : ℝ) ^ P.u)))
      have hmaskMass' : (1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ P.u)) ≤
          ∑ y ∈ mask, ν.w y := by simpa [ν, mask] using hmaskMass
      have hmaskPos : 0 < ∑ y ∈ mask, ν.w y := by
        exact lt_of_lt_of_le hlow hmaskMass'
      have hmaskLog := mask_log_bound9 hmaskMass'
      have hmaskEq : maskedLaw9 S ωbase edge.1 = ν.restrict mask hmaskPos := by
        unfold maskedLaw9 restrictOr9
        rw [dif_pos hmaskPos]
      let base0 := regularityBase9 S I edge.1 ωbase t
      have hbaseY : base0.SupportedIn Y := by
        intro y hy
        by_cases ht : t.val = 0
        · have hbaseEq : base0 = maskedLaw9 S ωbase edge.1 := by
            simp [base0, regularityBase9, ht]
          rw [hbaseEq, hmaskEq]
          by_cases hmem : y ∈ mask
          · simp [Law.restrict, hmem, hνY y hy]
          · simp [Law.restrict, hmem]
        · simpa [base0, regularityBase9, ht, ν] using hνY y hy
      let baseBudget := P.Ss (n : ℝ) + (n : ℝ) ^ P.u + Real.log 2
      have hbaseW : base0.WidthLE baseBudget := by
        by_cases ht : t.val = 0
        · have hbaseEq : base0 = maskedLaw9 S ωbase edge.1 := by
            simp [base0, regularityBase9, ht]
          rw [hbaseEq, hmaskEq]
          apply Law.WidthLE.mono (Law.WidthLE.restrict hνW hmaskPos)
          dsimp [baseBudget]
          linarith [hmaskLog]
        · have hbaseEq : base0 = ν := by simp [base0, regularityBase9, ht, ν]
          rw [hbaseEq]
          apply Law.WidthLE.mono hνW
          dsimp [baseBudget]
          have hnu : 0 ≤ (n : ℝ) ^ P.u := by positivity
          have hlog2 : 0 ≤ Real.log 2 := by positivity
          linarith
      let lam9 := prefixLaw9 E G ωbase base0 ord k.val
      have hnodup := regularityOrder_nodup9 S I v edge t
      have hprevEquiv (x : Fin N) :
          prefixRegularBefore9 S I E G v edge t k (Function.update ωbase (Sum.inl c) x) ↔
            prefixRegularBefore9 S I E G v edge t k ωbase := by
        exact prefixRegularBefore_update9 S I E G v edge t k ωbase hnodup x
      by_cases hgood : prefixRegularBefore9 S I E G v edge t k ωbase
      · have hprev_update (x : Fin N) :
          prefixRegularBefore9 S I E G v edge t k (Function.update ωbase (Sum.inl c) x) →
            prefixRegularBefore9 S I E G v edge t k ωbase := by
          intro hp
          exact (hprevEquiv x).mp hp
        have hmassLB : (49 / 100 : ℝ) ^ k.val ≤ prefixMass9 E G ωbase base0 ord k.val := by
          exact prefixMass_lower9 S I E G ωbase base0 ord k.val (Nat.le_of_lt k.isLt) hgood
        have hmassPos : 0 < prefixMass9 E G ωbase base0 ord k.val := by
          exact lt_of_lt_of_le (by positivity) hmassLB
        let A := hitSet9 E G ωbase (ord.take k.val).toFinset
        have hmassA : 0 < ∑ y ∈ A, base0.w y := by
          simpa [prefixMass9, A] using hmassPos
        have hprefixEq : lam9 = base0.restrict A hmassPos := by
          change restrictOr9 base0 A = base0.restrict A hmassPos
          unfold restrictOr9
          rw [dif_pos hmassA]
        have hLamY : lam9.SupportedIn Y := by
          rw [hprefixEq]
          exact law_restrict_supported9 hbaseY hmassA
        have hseenR : ((I.seen edge.1).card : ℝ) ≤ P.idBudget n + (P.m n : ℝ) := by
          simpa [IDMap9.seen] using I.odd_ids edge.1.1 edge.1.2
        have hlenOrd := regularityOrder_length_le_seen_add_one9 S I v edge t
        have hkR : (k.val : ℝ) ≤ P.idBudget n + (P.m n : ℝ) + 1 := by
          have hkN : k.val ≤ ord.length := Nat.le_of_lt k.isLt
          have hkN' : k.val ≤ (I.seen edge.1).card + 1 := le_trans hkN hlenOrd
          have hkCast : (k.val : ℝ) ≤ (I.seen edge.1).card + 1 := by exact_mod_cast hkN'
          linarith
        have hlogRatioPos : 0 < Real.log (100 / 49) := Real.log_pos (by norm_num)
        have hratioMass := prefix_log_bound9 hmassLB
        have hbudget : baseBudget - Real.log (prefixMass9 E G ωbase base0 ord k.val) ≤
            P.filterBudget n + (n : ℝ) ^ P.u := by
          have hkL := mul_le_mul_of_nonneg_right hkR hlogRatioPos.le
          have hbudgetEq : baseBudget +
              (P.idBudget n + (P.m n : ℝ) + 1) * Real.log (100 / 49) =
                P.filterBudget n + Real.log (100 / 49) := by
            simp [baseBudget, Params9.filterBudget]
            ring
          calc
            baseBudget - Real.log (prefixMass9 E G ωbase base0 ord k.val) ≤
                baseBudget + (k.val : ℝ) * Real.log (100 / 49) := by linarith
            _ ≤ baseBudget + (P.idBudget n + (P.m n : ℝ) + 1) * Real.log (100 / 49) :=
              add_le_add_right hkL baseBudget
            _ = P.filterBudget n + Real.log (100 / 49) := hbudgetEq
            _ ≤ P.filterBudget n + (n : ℝ) ^ P.u := by linarith [hPoly]
        have hLamW : lam9.WidthLE (P.Sd (n : ℝ)) := by
          rw [hprefixEq]
          apply Law.WidthLE.mono (Law.WidthLE.restrict hbaseW hmassPos)
          exact le_trans hbudget hfilter
        let outlier : Fin N → Prop := fun x =>
          2 * P.bStar n < |rowDeg E G x lam9 - 1 / 2|
        have hforward := hTools.1 G lam9 hLamY hLamW α hαX w hαW hwd
        have houtlier : α.pr outlier ≤ 2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
          simpa [outlier, FinProb.pr, Finset.sum_filter] using hforward
        have hsubset (x : Fin N) :
            badBoundedRegularityTest9 S I E G v q (Function.update ωbase (Sum.inl c) x) → outlier x := by
          intro hb
          rcases hb with ⟨k', hval, hp⟩
          have hk' : k' = k := Fin.ext (by simpa [k] using hval)
          rw [hk'] at hp
          rcases hp with ⟨hprev, hout⟩
          have hprev0 := hprev_update x hprev
          have hbaseEq : regularityBase9 S I edge.1 (Function.update ωbase (Sum.inl c) x) t = base0 :=
            regularityBase_update9 S I edge.1 ωbase c x t
          have hnot : c ∉ (ord.take k.val).toFinset := by
            change ord[k.val] ∉ (ord.take k.val).toFinset
            exact nodup_getElem_not_mem_take hnodup k
          have hprefix :
              prefixLaw9 E G (Function.update ωbase (Sum.inl c) x)
                (regularityBase9 S I edge.1 (Function.update ωbase (Sum.inl c) x) t) ord k.val = lam9 := by
            rw [hbaseEq]
            exact @prefixLaw_update_anchor9 P n N M I E G ωbase c x base0 ord k.val hnot
          have hanc : anc9 (Function.update ωbase (Sum.inl c) x) c = x := by
            simp [anc9, Function.update]
          have hout' := hout
          rw [hanc, hprefix] at hout'
          exact hout'
        have hslice := FinProb.pr_mono (inputLaw9 S I (Sum.inl c))
          (fun x => badBoundedRegularityTest9 S I E G v q
            (Function.update ωbase (Sum.inl c) x)) outlier hsubset
        calc
          (inputLaw9 S I (Sum.inl c)).pr
              (fun x => badBoundedRegularityTest9 S I E G v q
                (Function.update ωbase (Sum.inl c) x)) ≤ α.pr outlier := by
                  change (inputLaw9 S I (Sum.inl c)).pr
                    (fun x => badBoundedRegularityTest9 S I E G v q
                      (Function.update ωbase (Sum.inl c) x)) ≤
                    (inputLaw9 S I (Sum.inl c)).pr outlier
                  exact hslice
          _ ≤ 2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := houtlier
          _ ≤ 2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
                exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgap) (by norm_num)
      · have hfalse (x : Fin N) :
            ¬ badBoundedRegularityTest9 S I E G v q (Function.update ωbase (Sum.inl c) x) := by
          intro hb
          rcases hb with ⟨k', hval, hp⟩
          have hk' : k' = k := Fin.ext (by simpa [k] using hval)
          rw [hk'] at hp
          exact hgood ((hprevEquiv x).mp hp.1)
        have hzero : (inputLaw9 S I (Sum.inl c)).pr
            (fun x => badBoundedRegularityTest9 S I E G v q
              (Function.update ωbase (Sum.inl c) x)) = 0 := by
          unfold FinProb.pr
          apply Finset.sum_eq_zero
          intro x hx
          simp [hfalse x]
        rw [hzero]
        positivity
    have htestRaw : (rawLaw9 S I).pr (badBoundedRegularityTest9 S I E G v q) ≤
        2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
      change (FinProb.pi (inputLaw9 S I)).pr (badBoundedRegularityTest9 S I E G v q) ≤ _
      exact htest
    exact htestRaw
  · have hfalse : ∀ ω, ¬ badBoundedRegularityTest9 S I E G v q ω := by
      intro ω hb
      rcases (by simpa [badBoundedRegularityTest9, edge, t, ord] using hb) with ⟨k, hval, _⟩
      exact hvalid (by rw [← hval]; exact k.isLt)
    have hzero : (rawLaw9 S I).pr (badBoundedRegularityTest9 S I E G v q) = 0 := by
      simp [FinProb.pr, hfalse]
    rw [hzero]
    positivity

theorem regularity_certificate9 (P : Params9) (hP : P.Valid) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M)
      (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → RegularityCert9 S I E G c := by
  have hPvalid : P.Valid := hP
  have hxS : 0 < (P.xS : ℝ) := by exact_mod_cast hP.1.1
  rcases hP with ⟨_, _, _, _, hChi, _, _⟩
  have hχpos : 0 < (P.χ : ℝ) := by exact_mod_cast hChi.1
  have hu : 0 < P.u := by
    dsimp [Params9.u]
    exact div_pos hxS (by norm_num)
  obtain ⟨n₀, htail⟩ := regularity_polynomial_tail9 hu hχpos
  refine ⟨1 / 2, by norm_num, n₀, ?_⟩
  intro n hn N E X Y κ G M S I hCore
  have hpoly := htail n hn
  rcases hCore with ⟨hN, hPrep, hDeep, hTags, hMasks, hTools, hScale, hAt⟩
  have hCore' : CoreInput9 P κ E X Y G M S I :=
    ⟨hN, hPrep, hDeep, hTags, hMasks, hTools, hScale, hAt⟩
  intro v
  let Ev : Outcome9 I N → Prop := fun ω => ¬ starRegular9 S E G ω v
  let Test : BoundedRegularityTestIndex9 I v → Outcome9 I N → Prop :=
    fun q ω => badBoundedRegularityTest9 S I E G v q ω
  have hcover : ∀ ω, Ev ω → ∃ q, Test q ω := by
    intro ω hω
    simpa [Ev, Test] using
      exists_badBoundedRegularityTest9 S I E G ω v hScale hAt hω
  have hmono := FinProb.pr_mono (rawLaw9 S I) Ev (fun ω => ∃ q, Test q ω) hcover
  have hunion := FinProb.pr_exists_le_sum5 (rawLaw9 S I) Test
  have hcount := boundedRegularityTestIndex_card_le9 S I v hScale hAt
  have hcountR : (Fintype.card (BoundedRegularityTestIndex9 I v) : ℝ) ≤
      9 * (n : ℝ) ^ 2 := by exact_mod_cast hcount
  have hsum :
      ∑ q : BoundedRegularityTestIndex9 I v, (rawLaw9 S I).pr (Test q) ≤
        ∑ q : BoundedRegularityTestIndex9 I v,
          2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by
    apply Finset.sum_le_sum
    intro q hq
    exact boundedRegularityTest_probability_le9 hPvalid S I hCore' v q hpoly.2
  calc
    (rawLaw9 S I).pr Ev ≤ (rawLaw9 S I).pr (fun ω => ∃ q, Test q ω) := hmono
    _ ≤ ∑ q, (rawLaw9 S I).pr (Test q) := hunion
    _ ≤ ∑ q, 2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := hsum
    _ = (Fintype.card (BoundedRegularityTestIndex9 I v) : ℝ) *
          (2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))))) := by simp
    _ ≤ (9 * (n : ℝ) ^ 2) *
          (2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ))))) :=
      mul_le_mul_of_nonneg_right hcountR (by positivity)
    _ = 18 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (P.u + 8 * (P.χ : ℝ)))) := by ring
    _ ≤ Real.exp (-((n : ℝ) ^ P.u / 2)) := hpoly.1
    _ = P.tail (1 / 2) n := by
      simp [Params9.tail]
      congr 1
      ring

private theorem one_sign_mass {N : ℕ} {X : Finset (Fin N)}
    {wX err w : ℝ} (α : Law N)
    (hαX : α.SupportedIn X) (hαW : α.WidthLE w)
    (f : Fin N → ℝ)
    (hmean : ∀ ρ : Law N, ρ.SupportedIn X → ρ.WidthLE wX →
      |∑ x, ρ.w x * f x| ≤ err)
    (S : Finset (Fin N)) (hside : ∀ x ∈ S, err < f x) :
    ∑ x ∈ S, α.w x ≤ Real.exp (w - wX) := by
  classical
  by_contra hnot
  have hmass : Real.exp (w - wX) < ∑ x ∈ S, α.w x := lt_of_not_ge hnot
  have hmasspos : 0 < ∑ x ∈ S, α.w x := lt_trans (Real.exp_pos _) hmass
  let ρ : Law N := α.restrict S hmasspos
  have hlog : w - wX < Real.log (∑ x ∈ S, α.w x) := by
    have h := Real.log_lt_log (Real.exp_pos (w - wX)) hmass
    simpa only [Real.log_exp] using h
  have hρwidth : ρ.WidthLE wX := by
    apply Law.WidthLE.mono (Law.WidthLE.restrict hαW hmasspos)
    linarith
  have hρX : ρ.SupportedIn X := by
    intro x hx
    simp [ρ, Law.restrict, hαX x hx]
  have hρS : ρ.SupportedIn S := by
    intro x hx
    simp [ρ, Law.restrict, hx]
  have hρsumpos : 0 < ∑ x, ρ.w x := by
    rw [ρ.sum_eq_one]
    norm_num
  obtain ⟨x₀, hx₀, hx₀pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := ρ.w)
      (by intro x hx; exact ρ.nonneg x)).mp hρsumpos
  have hx₀S : x₀ ∈ S := by
    by_contra hx
    have hzero := hρS x₀ hx
    simp [hzero] at hx₀pos
  have havg : err < ∑ x, ρ.w x * f x := by
    have hconst : (∑ x, ρ.w x * err) = err := by
      rw [← Finset.sum_mul, ρ.sum_eq_one]
      ring
    rw [← hconst]
    apply Finset.sum_lt_sum
    · intro x hx
      by_cases hxS : x ∈ S
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hside x hxS)) (ρ.nonneg x)
      · simp [hρS x hxS]
    · exact ⟨x₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hside x₀ hx₀S) hx₀pos⟩
  have hbound := hmean ρ hρX hρwidth
  rcases abs_le.mp hbound with ⟨hlo, hhi⟩
  linarith

private theorem signed_test_row_tail9 {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hdeep : P.DeepAt n N E X Y) (G : Colour)
    (hn : 1 ≤ n)
    (α : Law N) (hαX : α.SupportedIn X) (w : ℝ) (hαW : α.WidthLE w)
    (hw : w ≤ (n : ℝ) ^ (P.xD : ℝ))
    (lamBase : Law N) (hBaseY : lamBase.SupportedIn Y) (s : ℝ)
    (hBaseW : lamBase.WidthLE (s - Real.log 4)) (hs : s ≤ P.Sd (n : ℝ))
    (f : Fin N → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    ∑ x ∈ Finset.univ.filter (fun x => 4 * P.bStar n <
      |∑ y, lamBase.w y * ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * f y|), α.w x ≤
      2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
  classical
  change DiscOne E X Y ((n : ℝ) ^ (P.xD : ℝ)) (P.Sd (n : ℝ)) (P.bStar n) at hdeep
  let g : Fin N → ℝ := fun x =>
    ∑ y, lamBase.w y * ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * f y
  have hmean (ρ : Law N) (hρX : ρ.SupportedIn X)
      (hρW : ρ.WidthLE ((n : ℝ) ^ (P.xD : ℝ))) :
      |∑ x, ρ.w x * g x| ≤ 4 * P.bStar n := by
    have hBaseW' : lamBase.WidthLE
        (P.Sd (n : ℝ) - Real.log (2 * (1 : ℝ) + 2)) := by
      have hh := Law.WidthLE.mono hBaseW (sub_le_sub_right hs _)
      have hlog4 : Real.log (2 * (1 : ℝ) + 2) = Real.log 4 := by norm_num
      simpa only [hlog4] using hh
    have hdisc := signedTest_of_discrepancy (show (0 : ℝ) ≤ 1 by norm_num)
      hdeep ρ lamBase hρX hBaseY hρW hBaseW' f hf G
    have heq : signedHitExpectation E G ρ lamBase f = ∑ x, ρ.w x * g x := by
      rfl
    calc
      |∑ x, ρ.w x * g x| = |signedHitExpectation E G ρ lamBase f| := by rw [heq]
      _ ≤ 2 * (1 + 1) * P.bStar n := hdisc
      _ = 4 * P.bStar n := by ring
  let Splus := Finset.univ.filter (fun x => 4 * P.bStar n < g x)
  let Sminus := Finset.univ.filter (fun x => 4 * P.bStar n < -g x)
  let Sbad := Finset.univ.filter (fun x => 4 * P.bStar n < |g x|)
  have hplus :
      ∑ x ∈ Finset.univ.filter (fun x => 4 * P.bStar n < g x), α.w x ≤
        Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
    apply one_sign_mass α hαX hαW (fun x => g x)
      (fun ρ hρX hρW => hmean ρ hρX hρW)
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hminus :
      ∑ x ∈ Finset.univ.filter (fun x => 4 * P.bStar n < -g x), α.w x ≤
        Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
    have hmeanNeg (ρ : Law N) (hρX : ρ.SupportedIn X)
        (hρW : ρ.WidthLE ((n : ℝ) ^ (P.xD : ℝ))) :
        |∑ x, ρ.w x * -g x| ≤ 4 * P.bStar n := by
      have hneg : (∑ x, ρ.w x * -g x) = -∑ x, ρ.w x * g x := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hneg]
      simpa only [abs_neg] using hmean ρ hρX hρW
    exact one_sign_mass α hαX hαW (fun x => -g x) hmeanNeg Sminus
      (by intro x hx; exact (Finset.mem_filter.mp hx).2)
  have hsubset : Sbad ⊆ Splus ∪ Sminus := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    by_cases hnonneg : 0 ≤ g x
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [abs_of_nonneg hnonneg] using hx'⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [abs_of_neg (lt_of_not_ge hnonneg)] at hx'
        exact hx'⟩
  have hdis : Disjoint Splus Sminus := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h₁ := (Finset.mem_filter.mp hx₁).2
    have h₂ := (Finset.mem_filter.mp hx₂).2
    have hb : 0 ≤ P.bStar n := by
      dsimp [Params9.bStar]
      have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
      exact le_of_lt (Real.rpow_pos_of_pos hnR _)
    linarith
  calc
    (∑ x ∈ Sbad, α.w x) ≤ ∑ x ∈ Splus ∪ Sminus, α.w x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun x hx _ => α.nonneg x)
    _ = (∑ x ∈ Splus, α.w x) + ∑ x ∈ Sminus, α.w x := by rw [Finset.sum_union hdis]
    _ ≤ Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) + Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) :=
      add_le_add hplus hminus
    _ = 2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by ring

private theorem dens_eq_rowDegree {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) : dens E G μ ν = ∑ x, μ.w x * rowDeg E G x ν := by
  classical
  simp only [dens, rowDeg]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

private theorem row_deviation_mean {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) :
    ∑ x, μ.w x * (rowDeg E G x ν - 1 / 2) = dens E G μ ν - 1 / 2 := by
  classical
  rw [dens_eq_rowDegree]
  calc
    (∑ x, μ.w x * (rowDeg E G x ν - 1 / 2)) =
        (∑ x, μ.w x * rowDeg E G x ν) - ∑ x, μ.w x * (1 / 2) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = (∑ x, μ.w x * rowDeg E G x ν) - 1 / 2 := by
          have hhalf : (∑ x, μ.w x * (1 / 2)) = 1 / 2 := by
            rw [← Finset.sum_mul, μ.sum_eq_one]
            ring
          rw [hhalf]

private theorem col_deviation_mean {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) :
    ∑ y, ν.w y * (colDeg E G μ y - 1 / 2) = dens E G μ ν - 1 / 2 := by
  classical
  have hdens : dens E G μ ν = ∑ y, ν.w y * colDeg E G μ y := by
    unfold dens colDeg
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hdens]
  calc
    (∑ y, ν.w y * (colDeg E G μ y - 1 / 2)) =
        (∑ y, ν.w y * colDeg E G μ y) - ∑ y, ν.w y * (1 / 2) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = (∑ y, ν.w y * colDeg E G μ y) - 1 / 2 := by
          have hhalf : (∑ y, ν.w y * (1 / 2)) = 1 / 2 := by
            rw [← Finset.sum_mul, ν.sum_eq_one]
            ring
          rw [hhalf]

/-- Degree outliers under the first law, by conditioning on either signed exceptional set. -/
theorem forward_bound {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hdeep : P.DeepAt n N E X Y) (G : Colour)
    (lam : Law N) (hlamY : lam.SupportedIn Y) (hlamW : lam.WidthLE (P.Sd (n : ℝ)))
    (α : Law N) (hαX : α.SupportedIn X) (w : ℝ) (hαW : α.WidthLE w)
    (hw : w ≤ (n : ℝ) ^ (P.xD : ℝ)) :
    ∑ x ∈ Finset.univ.filter (fun x => 2 * P.bStar n < |rowDeg E G x lam - 1 / 2|), α.w x ≤
      2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
  classical
  let err : ℝ := (n : ℝ) ^ (-(P.hMinus : ℝ))
  let W : ℝ := (n : ℝ) ^ (P.xD : ℝ)
  have hdisc : DiscOne E X Y W (P.Sd (n : ℝ)) err := by
    change DiscOne E X Y W (P.Sd (n : ℝ)) err at hdeep
    exact hdeep
  have herr_nonneg : 0 ≤ err := by
    dsimp [err]
    positivity
  have hbstar_nonneg : 0 ≤ P.bStar n := by
    dsimp [Params9.bStar]
    positivity
  let q : Fin N → ℝ := fun x => rowDeg E G x lam - 1 / 2
  let Splus : Finset (Fin N) := Finset.univ.filter (fun x => 2 * P.bStar n < q x)
  let Sminus : Finset (Fin N) := Finset.univ.filter (fun x => 2 * P.bStar n < -q x)
  have hmean (ρ : Law N) (hρX : ρ.SupportedIn X) (hρW : ρ.WidthLE W) :
      |∑ x, ρ.w x * (rowDeg E G x lam - 1 / 2)| ≤ err := by
    rw [row_deviation_mean]
    have hd := hdisc ρ lam hρX hlamY hρW hlamW G
    simpa [err] using hd
  have hplus : ∑ x ∈ Splus, α.w x ≤ Real.exp (w - W) := by
    apply one_sign_mass α hαX hαW
      (fun x => rowDeg E G x lam - 1 / 2)
    · intro ρ hρX hρW
      exact hmean ρ hρX hρW
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      dsimp [q] at hx'
      have hpow : P.bStar n = err := by
        simp [Params9.bStar, err]
      rw [hpow] at hx'
      linarith
  have hminus : ∑ x ∈ Sminus, α.w x ≤ Real.exp (w - W) := by
    apply one_sign_mass α hαX hαW
      (fun x => 1 / 2 - rowDeg E G x lam)
    · intro ρ hρX hρW
      have hm := hmean ρ hρX hρW
      have hneg : (∑ x, ρ.w x * (1 / 2 - rowDeg E G x lam)) =
          -∑ x, ρ.w x * (rowDeg E G x lam - 1 / 2) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hneg]
      simpa only [abs_neg] using hm
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      have hpow : P.bStar n = err := by
        simp [Params9.bStar, err]
      rw [hpow] at hx'
      dsimp [q] at hx'
      linarith
  let Sbad := Finset.univ.filter (fun x => 2 * P.bStar n < |q x|)
  have hsubset : Sbad ⊆ Splus ∪ Sminus := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    by_cases hqx : 0 ≤ q x
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · simpa [abs_of_nonneg hqx] using hx'
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · have habs : |q x| = -q x := abs_of_neg (lt_of_not_ge hqx)
        rw [habs] at hx'
        exact hx'
  have hdis : Disjoint Splus Sminus := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h₁ := (Finset.mem_filter.mp hx₁).2
    have h₂ := (Finset.mem_filter.mp hx₂).2
    linarith [hbstar_nonneg]
  calc
    (∑ x ∈ Sbad, α.w x) ≤ ∑ x ∈ Splus ∪ Sminus, α.w x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun x hx _ => α.nonneg x)
    _ = (∑ x ∈ Splus, α.w x) + ∑ x ∈ Sminus, α.w x := by rw [Finset.sum_union hdis]
    _ ≤ Real.exp (w - W) + Real.exp (w - W) := add_le_add hplus hminus
    _ = 2 * Real.exp (w - W) := by ring

/-- The transposed first-side estimate is the second-side degree test. -/
theorem reverse_bound {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hdeep : P.DeepAt n N E X Y) (G : Colour)
    (σ : Law N) (hσX : σ.SupportedIn X) (hσW : σ.WidthLE ((n : ℝ) ^ (P.xD : ℝ)))
    (lam : Law N) (hlamY : lam.SupportedIn Y) (s : ℝ)
    (hlamW : lam.WidthLE s) (hs : s ≤ P.Sd (n : ℝ)) :
    ∑ y ∈ Finset.univ.filter (fun y => 2 * P.bStar n < |colDeg E G σ y - 1 / 2|), lam.w y ≤
      2 * Real.exp (s - P.Sd (n : ℝ)) := by
  classical
  let err : ℝ := (n : ℝ) ^ (-(P.hMinus : ℝ))
  have hdisc : DiscOne (transposeRel E) Y X (P.Sd (n : ℝ)) ((n : ℝ) ^ (P.xD : ℝ)) err := by
    change DiscOne E X Y ((n : ℝ) ^ (P.xD : ℝ)) (P.Sd (n : ℝ)) err at hdeep
    exact (DiscOne.transpose_iff E X Y ((n : ℝ) ^ (P.xD : ℝ)) (P.Sd (n : ℝ)) err).mpr hdeep
  have herr_nonneg : 0 ≤ err := by
    dsimp [err]
    positivity
  have hbstar_nonneg : 0 ≤ P.bStar n := by
    dsimp [Params9.bStar]
    positivity
  let q : Fin N → ℝ := fun y => colDeg E G σ y - 1 / 2
  let Splus : Finset (Fin N) := Finset.univ.filter (fun y => 2 * P.bStar n < q y)
  let Sminus : Finset (Fin N) := Finset.univ.filter (fun y => 2 * P.bStar n < -q y)
  have hmean (ρ : Law N) (hρY : ρ.SupportedIn Y) (hρW : ρ.WidthLE (P.Sd (n : ℝ))) :
      |∑ y, ρ.w y * (rowDeg (transposeRel E) G y σ - 1 / 2)| ≤ err := by
    rw [row_deviation_mean]
    have hd := hdisc ρ σ hρY hσX hρW hσW G
    simpa [err] using hd
  have hrowEq (y : Fin N) : rowDeg (transposeRel E) G y σ = colDeg E G σ y := by
    exact (colDeg_transpose (transposeRel E) G σ y).symm.trans (by rfl)
  have hplus : ∑ y ∈ Splus, lam.w y ≤ Real.exp (s - P.Sd (n : ℝ)) := by
    apply one_sign_mass lam hlamY hlamW
      (fun y => rowDeg (transposeRel E) G y σ - 1 / 2)
    · intro ρ hρY hρW
      exact hmean ρ hρY hρW
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp [q] at hy'
      rw [← hrowEq] at hy'
      have hpow : P.bStar n = err := by simp [Params9.bStar, err]
      rw [hpow] at hy'
      linarith
  have hminus : ∑ y ∈ Sminus, lam.w y ≤ Real.exp (s - P.Sd (n : ℝ)) := by
    apply one_sign_mass lam hlamY hlamW
      (fun y => 1 / 2 - rowDeg (transposeRel E) G y σ)
    · intro ρ hρY hρW
      have hm := hmean ρ hρY hρW
      have hneg : (∑ y, ρ.w y * (1 / 2 - rowDeg (transposeRel E) G y σ)) =
          -∑ y, ρ.w y * (rowDeg (transposeRel E) G y σ - 1 / 2) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      rw [hneg]
      simpa only [abs_neg] using hm
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp [q] at hy'
      rw [← hrowEq] at hy'
      have hpow : P.bStar n = err := by simp [Params9.bStar, err]
      rw [hpow] at hy'
      linarith
  let Sbad := Finset.univ.filter (fun y => 2 * P.bStar n < |q y|)
  have hsubset : Sbad ⊆ Splus ∪ Sminus := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    by_cases hqy : 0 ≤ q y
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · simpa [abs_of_nonneg hqy] using hy'
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · have habs : |q y| = -q y := abs_of_neg (lt_of_not_ge hqy)
        rw [habs] at hy'
        exact hy'
  have hdis : Disjoint Splus Sminus := by
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    have h₁ := (Finset.mem_filter.mp hy₁).2
    have h₂ := (Finset.mem_filter.mp hy₂).2
    linarith [hbstar_nonneg]
  calc
    (∑ y ∈ Sbad, lam.w y) ≤ ∑ y ∈ Splus ∪ Sminus, lam.w y :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun y hy _ => lam.nonneg y)
    _ = (∑ y ∈ Splus, lam.w y) + ∑ y ∈ Sminus, lam.w y := by rw [Finset.sum_union hdis]
    _ ≤ Real.exp (s - P.Sd (n : ℝ)) + Real.exp (s - P.Sd (n : ℝ)) := add_le_add hplus hminus
    _ = 2 * Real.exp (s - P.Sd (n : ℝ)) := by ring

end HypercubeRamsey.Lane_q_s09_gain1
