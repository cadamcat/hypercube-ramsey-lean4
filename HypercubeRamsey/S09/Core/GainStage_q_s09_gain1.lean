import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.S03.Clock.Steps_p_clock_r4
import HypercubeRamsey.S05.Clock_q_s05_even

namespace HypercubeRamsey.Lane_q_s09_gain1

open HypercubeRamsey Classical
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
