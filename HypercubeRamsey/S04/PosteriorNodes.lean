import HypercubeRamsey.S04.CoreLemmas

/-!
# D4.6 caps and L4.1g: the posterior tuple and even common neighbourhoods

Source: `sections/04-…tex`, lines 340–432; blueprint D4.6, L4.1g.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- D4.6 (04:349–351): an odd row is zero or `ν^{M'}(y) 1[hits]/R_u(D)` with `ν^{M'} ≤ 2ν_i ≤ 2e^{sY+1}/N` and
`R_u(D) ≥ exp(-LkT|Z_u|)`, `LkT|Z_u| = o(n^γ)` (`KeyNbrCard`); so `N p_u(y) ≤ exp(2n^γ)` for large `n`. -/
theorem odd_cap (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyNbrCard β γ n →
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), OddCap M tag := by
  have hω := omega4_pos hβ hγ
  have hγpos : 0 < γ := lt_of_lt_of_le hβ hβγ
  let δ : ℝ := 8 * omega4 β γ / 15 - h4 β γ
  have hδ : 0 < δ := by
    dsimp [δ, h4]
    nlinarith [hω]
  have htδ : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ δ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have htγ : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ γ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hγpos).comp tendsto_natCast_atTop_atTop
  obtain ⟨nδ, hnδ⟩ := Filter.eventually_atTop.1 (htδ.eventually_ge_atTop (32 : ℝ))
  obtain ⟨nγ, hnγ⟩ := Filter.eventually_atTop.1 (htγ.eventually_ge_atTop (8 : ℝ))
  refine ⟨max 1 (max nδ nγ), ?_⟩
  intro n hn hkey N E G X Y M tag ω u y
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 (max nδ nγ)) hn
  have hsub : max nδ nγ ≤ n := (le_max_right 1 (max nδ nγ)).trans hn
  have hnδ' : nδ ≤ n := (le_max_left nδ nγ).trans hsub
  have hnγ' : nγ ≤ n := (le_max_right nδ nγ).trans hsub
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hδn : 32 ≤ (n : ℝ) ^ δ := hnδ n hnδ'
  have hγn : 8 ≤ (n : ℝ) ^ γ := hnγ n hnγ'
  by_cases hOK : OddOK M tag ω u
  · let D : Finset (Loc β γ n) := selSet M tag ω u
    let S : Mask (M.ν (tag (key β γ n u.1))) := aym (paux ω) u
    let i : M.ι := tag (key β γ n u.1)
    let R : ℝ := (maskLaw S).pr (HitsAll E G (aW (paux ω)) D (Zset β γ u))
    let B : ℝ := capL β γ n * (tupLen β γ n : ℝ) * (D.card : ℝ) * ((Zset β γ u).card : ℝ)
    have hvalid : Valid M tag u (paux ω) D := by simpa [D] using hOK.2
    have hmass : Real.exp (-B) ≤ R := by simpa [R, B, D] using hvalid.mass
    have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hmass
    have hfactor : 1 ≤ Real.exp B * R := by
      dsimp [R] at hmass ⊢
      have hm := mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg B)
      calc
        1 = Real.exp (-B) * Real.exp B := by rw [← Real.exp_add]; simp
        _ ≤ R * Real.exp B := hm
        _ = Real.exp B * R := by ring
    have hcond : (maskLaw S).w y / R ≤ (maskLaw S).w y * Real.exp B := by
      apply (div_le_iff₀ hRpos).2
      have hmul := mul_le_mul_of_nonneg_left hfactor ((maskLaw S).nonneg y)
      calc
        (maskLaw S).w y = (maskLaw S).w y * 1 := by ring
        _ ≤ (maskLaw S).w y * (Real.exp B * R) := hmul
        _ = ((maskLaw S).w y * Real.exp B) * R := by ring
    have hN : 0 < N := by
      by_contra hnN
      have hz : N = 0 := Nat.eq_zero_of_not_pos hnN
      subst N
      have hs := (M.ν i).sum_eq_one
      simp at hs
    rcases M.prep i with ⟨_, _, _, hsY, _, hν, _, _, _⟩
    have hwidth : (N : ℝ) * (M.ν i).w y ≤ Real.exp (M.sY i + 1) := by
      calc
        (N : ℝ) * (M.ν i).w y ≤ (N : ℝ) * (Real.exp (M.sY i + 1) / N) :=
          mul_le_mul_of_nonneg_left (hν y) (by positivity)
        _ = Real.exp (M.sY i + 1) := by
          field_simp [ne_of_gt (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hN)]
    have hmask : (maskLaw S).w y ≤ 2 * (M.ν i).w y := by
      by_cases hy : y ∈ S.1
      · rw [maskLaw, Law.restrict]
        simp only [if_pos hy]
        apply (div_le_iff₀ (mask_mass_pos S)).2
        have hmul : (2 * (M.ν i).w y) * (1 / 2) ≤
            (2 * (M.ν i).w y) * (∑ x ∈ S.1, (M.ν i).w x) :=
          mul_le_mul_of_nonneg_left S.2.2
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((M.ν i).nonneg y))
        nlinarith [hmul]
      · rw [maskLaw, Law.restrict]
        simp [hy, (M.ν i).nonneg y]
    have hmaskwidth : (N : ℝ) * (maskLaw S).w y ≤ 2 * Real.exp (M.sY i + 1) := by
      calc
        (N : ℝ) * (maskLaw S).w y ≤ (N : ℝ) * (2 * (M.ν i).w y) :=
          mul_le_mul_of_nonneg_left hmask (by positivity)
        _ = 2 * ((N : ℝ) * (M.ν i).w y) := by ring
        _ ≤ 2 * Real.exp (M.sY i + 1) := by nlinarith [hwidth]
    have hb : B ≤ (n : ℝ) ^ γ / 4 := by
      have he : 0 < omega4 β γ / 3 := by positivity
      have hb0 : 0 < bH β γ := by unfold bH; positivity
      have hpowe : 1 ≤ (n : ℝ) ^ (omega4 β γ / 3) := Real.one_le_rpow hnreal (by linarith)
      have hpowb : 1 ≤ (n : ℝ) ^ bH β γ := Real.one_le_rpow hnreal hb0.le
      have hKceil : (tupLen β γ n : ℝ) < (n : ℝ) ^ (omega4 β γ / 3) + 1 := by
        simpa [tupLen] using Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ (omega4 β γ / 3) by positivity)
      have hK : (tupLen β γ n : ℝ) ≤ 2 * (n : ℝ) ^ (omega4 β γ / 3) := by
        dsimp [tupLen] at hKceil ⊢
        linarith
      have hTceil : (setBd β γ n : ℝ) < 3 * (n : ℝ) ^ bH β γ + 1 := by
        simpa [setBd] using Nat.ceil_lt_add_one (show 0 ≤ 3 * (n : ℝ) ^ bH β γ by positivity)
      have hT : (setBd β γ n : ℝ) ≤ 4 * (n : ℝ) ^ bH β γ := by
        dsimp [setBd] at hTceil ⊢
        linarith
      have hD : (D.card : ℝ) ≤ 4 * (n : ℝ) ^ bH β γ := by
        have hD' : (D.card : ℝ) ≤ (setBd β γ n : ℝ) := by exact_mod_cast hvalid.card_le
        exact hD'.trans hT
      have hZ : ((Zset β γ u).card : ℝ) ≤ (n : ℝ) ^ (γ - 9 / 10 * omega4 β γ) := hkey u
      have hpowprod : (n : ℝ) ^ h4 β γ * (n : ℝ) ^ (omega4 β γ / 3) *
          (n : ℝ) ^ bH β γ * (n : ℝ) ^ (γ - 9 / 10 * omega4 β γ) =
            (n : ℝ) ^ (γ - δ) := by
        rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
        congr 1
        dsimp [δ, bH, h4]
        ring
      have hterm : 8 * (n : ℝ) ^ (γ - δ) ≤ (n : ℝ) ^ γ / 4 := by
        have hmul : 32 * (n : ℝ) ^ (γ - δ) ≤ (n : ℝ) ^ γ := by
          calc
            32 * (n : ℝ) ^ (γ - δ) ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (γ - δ) :=
              mul_le_mul_of_nonneg_right hδn (by positivity)
            _ = (n : ℝ) ^ γ := by
              rw [← Real.rpow_add hnpos]
              congr 1
              ring
        linarith [hmul]
      calc
        B = (n : ℝ) ^ h4 β γ * (tupLen β γ n : ℝ) * (D.card : ℝ) *
              ((Zset β γ u).card : ℝ) := rfl
        _ ≤ (n : ℝ) ^ h4 β γ * (2 * (n : ℝ) ^ (omega4 β γ / 3)) *
              (4 * (n : ℝ) ^ bH β γ) * (n : ℝ) ^ (γ - 9 / 10 * omega4 β γ) := by
          gcongr
        _ = 8 * (n : ℝ) ^ (γ - δ) := by
          calc
            _ = 8 * ((n : ℝ) ^ h4 β γ * (n : ℝ) ^ (omega4 β γ / 3) *
                  (n : ℝ) ^ bH β γ * (n : ℝ) ^ (γ - 9 / 10 * omega4 β γ)) := by ring
            _ = 8 * (n : ℝ) ^ (γ - δ) := by rw [hpowprod]
        _ ≤ (n : ℝ) ^ γ / 4 := by nlinarith [hterm]
    have hsYbound : M.sY i ≤ 3 / 2 * (n : ℝ) ^ γ := hsY
    have hexp : (Real.log 2 + (M.sY i + 1) + B) ≤ 2 * (n : ℝ) ^ γ := by
      have hlog2 : Real.log 2 ≤ 1 := by nlinarith [Real.log_two_lt_d9]
      have hpowγ : 0 ≤ (n : ℝ) ^ γ := by positivity
      linarith [hγn]
    by_cases hy : HitsAll E G (aW (paux ω)) D (Zset β γ u) y
    · have hrow : oddRow M tag ω u y = (maskLaw S).w y / R := by
        simp [oddRow, oddDraw, hOK, D, S, R, hy, FinProb.cond]
      rw [hrow]
      have hfinal : (N : ℝ) * ((maskLaw S).w y / R) ≤ Real.exp (Real.log 2 + (M.sY i + 1) + B) := by
        calc
          (N : ℝ) * ((maskLaw S).w y / R) ≤ (N : ℝ) * ((maskLaw S).w y * Real.exp B) :=
            mul_le_mul_of_nonneg_left hcond (by positivity)
          _ = ((N : ℝ) * (maskLaw S).w y) * Real.exp B := by ring
          _ ≤ (2 * Real.exp (M.sY i + 1)) * Real.exp B :=
            mul_le_mul_of_nonneg_right hmaskwidth (Real.exp_nonneg B)
          _ = Real.exp (Real.log 2 + (M.sY i + 1) + B) := by
            calc
              _ = Real.exp (Real.log 2) * Real.exp (M.sY i + 1) * Real.exp B := by
                exact congrArg (fun t : ℝ => t * Real.exp (M.sY i + 1) * Real.exp B)
                  (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
              _ = Real.exp (Real.log 2 + (M.sY i + 1)) * Real.exp B := by
                rw [← Real.exp_add]
              _ = Real.exp ((Real.log 2 + (M.sY i + 1)) + B) := by
                rw [← Real.exp_add]
              _ = Real.exp (Real.log 2 + (M.sY i + 1) + B) := by congr 1 <;> ring
      exact hfinal.trans (Real.exp_le_exp.mpr hexp)
    · simp [oddRow, oddDraw, hOK, D, S, R, hy, FinProb.cond]
      exact (Real.exp_pos _).le
  · simp [oddRow, hOK]
    exact (Real.exp_pos _).le

/-- L4.1g(1) (04:386–389): the reference laws use positions, odd masks and the tuples other than `W_{c,g(a)}`
(every requirement from that tuple is deleted), so `Q` does not read it; `M_c` integrates it out. -/
theorem ref_indep {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) : RefIndep M tag := by
  classical
  intro ω a c z y
  let κ : Key β γ n := key β γ n a.1
  let ck : Loc β γ n × Key β γ n := (c, κ)
  have lawExt {P Q : Law N} (h : ∀ x, P.w x = Q.w x) : P = Q := by
    cases P with
    | mk pw hp hs =>
      cases Q with
      | mk qw hq hsum =>
        have hw : pw = qw := funext h
        subst qw
        rfl
  have hbut (u : OddRole n) (D : Finset (Loc β γ n)) (v : Fin N) :
      HitsBut E G (aW (paux (updW ω ck z))) D (Zset β γ u) c κ v =
        HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ v := by
    apply propext
    constructor <;> intro h c' hc' κ' hκ' hne j
    · have h' := h c' hc' κ' hκ' hne j
      simpa [updW, paux, aW, ck, κ, Function.update_of_ne hne] using h'
    · have h' := h c' hc' κ' hκ' hne j
      simpa [updW, paux, aW, ck, κ, Function.update_of_ne hne] using h'
  have hpred (u : OddRole n) (D : Finset (Loc β γ n)) :
      (fun v => HitsBut E G (aW (paux (updW ω ck z))) D (Zset β γ u) c κ v) =
        fun v => HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ v :=
    funext (hbut u D)
  have hdel (u : OddRole n) (D : Finset (Loc β γ n)) :
      delLaw M tag (updW ω ck z) u D c κ = delLaw M tag ω u D c κ := by
    apply lawExt
    intro v
    have hmask : aym (paux (updW ω ck z)) u = aym (paux ω) u := rfl
    have hmass :
        (maskLaw (aym (paux (updW ω ck z)) u)).pr
            (fun v => HitsBut E G (aW (paux (updW ω ck z))) D (Zset β γ u) c κ v) =
          (maskLaw (aym (paux ω) u)).pr
            (fun v => HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ v) := by
      rw [hmask, hpred u D]
    simp [delLaw, hmask, hmass, hpred]
  have hrow (u : OddRole n) :
      refRow M tag (updW ω ck z) u c κ = refRow M tag ω u c κ := by
    apply lawExt
    intro v
    have hpos : ppos (updW ω ck z) = ppos ω := rfl
    have hOK : RefOK M tag (updW ω ck z) u c = RefOK M tag ω u c := rfl
    by_cases h : RefOK M tag ω u c
    · have h' : RefOK M tag (updW ω ck z) u c := by simpa [hOK] using h
      simp only [refRow, dif_pos h', dif_pos h, Law.mix, hpos]
      apply Finset.sum_congr rfl
      intro D hD
      rw [hdel u D]
    · have h' : ¬ RefOK M tag (updW ω ck z) u c := by simpa [hOK] using h
      simp [refRow, h, h']
  constructor
  · unfold refProd
    apply Finset.prod_congr rfl
    intro j hj
    exact congrArg (fun Q : Law N => Q.w (y j)) (hrow (oddNbr a j))
  · have hdouble (z' : Fin (tupLen β γ n) → Fin N) :
        updW (updW ω ck z) ck z' = updW ω ck z' := by
      simp only [updW, ppos, paux, axm, aym, aW, pact, pties]
      apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · rfl
          · apply Prod.ext
            · apply Prod.ext <;> rfl
            · funext q
              by_cases hq : q = ck
              · subst q
                simp [Function.update]
              · simp [Function.update, hq]
        · rfl
      · rfl
    have hdouble' (z' : Fin (tupLen β γ n) → Fin N) :
        updW (updW ω ck z) (c, key β γ n a.1) z' =
          updW ω (c, key β γ n a.1) z' := by
      simpa [ck, κ] using hdouble z'
    have hprior :
        prior M tag (updW ω ck z) c κ = prior M tag ω c κ := rfl
    unfold marg
    apply Finset.sum_congr rfl
    intro z' hz'
    rw [hprior]
    congr 1
    unfold lik
    rw [hdouble' z']

set_option maxHeartbeats 1000000

/-- L4.1g(2) (04:392–404): on `E` (recomputed at `z`), each neighbouring kernel `p_u` is at most
`R_u^{-(c,g(a))}(D_u)/R_u(D_u)` times its own deleted-tuple law, which is one of the at most `exp(O(T log n))` terms
of the mixture `Q_u` (count condition in `E`); the validity ratios give `exp(k(log 2 - c₁ a_*))` for the own-key
neighbours and `exp(Lk)` for the at most `n^{γ+14ω}` others (`KeyLocal`).  Since `T log n = o(k a_*)` and
`n^{γ+14ω} L = o(a_* n)`, the product is at most `exp((log 2 - c₂ a_*) k n) Q(y)` for large `n`. -/
theorem lik_bound (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyLocal β γ n →
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), LikBound M tag := by
  classical
  have selection_mem {n N : ℕ} {β γ : ℝ} {G : Colour} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
      (ω : Prep M tag) (v : CubeVertex n) (d : Loc β γ n)
      (hs : sel M tag ω v = some d) : d ∈ elig M tag (ppos ω) (paux ω) v d.2 := by
    classical
    unfold sel at hs
    let p : HDParams := hd β γ n
    let j := p.height (evenSites n) (ppos ω) (pact ω)
      (elig M tag (ppos ω) (paux ω)) p.Rlong v
    have hj : j < p.H := by
      by_contra hnot
      have hnone : p.selection (evenSites n) (ppos ω) (pact ω)
          (elig M tag (ppos ω) (paux ω)) (pties ω) v = none := by
        simp [HDParams.selection, HDParams.selectionAt, p, j, hnot]
      rw [hnone] at hs
      cases hs
    let lev : Fin (p.H + 1) := ⟨j, by omega⟩
    have hbad : ¬ p.Bad (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) v lev := by
      by_contra hb
      have hnone : p.selection (evenSites n) (ppos ω) (pact ω)
          (elig M tag (ppos ω) (paux ω)) (pties ω) v = none := by
        simp [HDParams.selection, HDParams.selectionAt, p, j, hj, lev, hb]
      rw [hnone] at hs
      cases hs
    let active : Finset (Loc β γ n) :=
      (elig M tag (ppos ω) (paux ω) v lev).filter (fun x => pact ω x = true)
    let pri := active.image (p.priority (pties ω) (v, lev))
    have hne : pri.Nonempty := by
      by_contra h
      have hnone : p.selection (evenSites n) (ppos ω) (pact ω)
          (elig M tag (ppos ω) (paux ω)) (pties ω) v = none := by
        simp [HDParams.selection, HDParams.selectionAt, p, j, hj, lev, hbad, active, pri, h]
      rw [hnone] at hs
      cases hs
    let q := pri.min' hne
    have hmem : ∃ x, x ∈ active ∧ p.priority (pties ω) (v, lev) x = q :=
      Finset.mem_image.mp (Finset.min'_mem pri hne)
    have hchoose : Classical.choose hmem = d := by
      simpa [HDParams.selection, HDParams.selectionAt, p, j, hj, lev, hbad, active, pri, q, hne, hmem]
        using hs
    have hactive : d ∈ active := by
      rw [← hchoose]
      exact (Classical.choose_spec hmem).1
    have hbase := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hactive).1).1
    have hlevel : d.2 = lev := (Finset.mem_filter.mp hbase).2.2.1
    rw [hlevel]
    exact (Finset.mem_filter.mp hactive).1
  have selection_pool {n N : ℕ} {β γ : ℝ} {G : Colour} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
      (ω : Prep M tag) (u : OddRole n) (v : CubeVertex n) (d : Loc β γ n)
      (hv : v ∈ oddAdj u) (hs : sel M tag ω v = some d) :
      d ∈ refPool (ppos ω) u := by
    have hE := selection_mem M tag ω v d hs
    rcases Finset.mem_sdiff.mp hE with ⟨hbase, _⟩
    rcases Finset.mem_filter.mp hbase with ⟨_, ⟨hP, ⟨_, hdist⟩⟩⟩
    unfold refPool
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hP, v, hv, hdist⟩
  have selectedSet_pool {n N : ℕ} {β γ : ℝ} {G : Colour} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
      (ω : Prep M tag) (u : OddRole n) (d : Loc β γ n)
      (hd : d ∈ selSet M tag ω u) : d ∈ refPool (ppos ω) u := by
    classical
    rcases Finset.mem_biUnion.mp hd with ⟨v, hv, hmem⟩
    cases hs : sel M tag ω v with
    | none => simp [hs] at hmem
    | some e =>
      have heq : d = e := by simpa [hs] using hmem
      subst d
      exact selection_pool M tag ω u v e hv hs
  have even_mem_oddAdj {n : ℕ} (a : EvenRole n) (j : Fin n) :
      a.1 ∈ oddAdj (oddNbr a j) := by
    unfold oddAdj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (cube n).Adj (cubeFlip a.1 j) a.1
    exact (cubeFlip_adj a.1 j).symm
  have oddAdj_card_le {n : ℕ} (u : OddRole n) : (oddAdj u).card ≤ n := by
    classical
    let flips : Finset (CubeVertex n) := Finset.univ.image (fun j : Fin n => cubeFlip u.1 j)
    have hsub : oddAdj u ⊆ flips := by
      intro v hv
      have hadj : (cube n).Adj u.1 v := (Finset.mem_filter.mp hv).2
      have hone : (Finset.univ.filter fun i : Fin n => u.1 i ≠ v i).card = 1 := hadj
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
      refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
      funext i
      by_cases hij : i = j
      · subst i
        have hmem : j ∈ Finset.univ.filter fun i : Fin n => u.1 i ≠ v i := by
          rw [hj]
          simp
        have hne := (Finset.mem_filter.mp hmem).2
        cases hu : u.1 j <;> cases hvj : v j <;> simp [cubeFlip, hu, hvj] at hne ⊢
      · have hmem : i ∉ Finset.univ.filter fun i : Fin n => u.1 i ≠ v i := by
          rw [hj]
          simpa using hij
        have heq : u.1 i = v i := by
          by_contra hne
          exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        simp [cubeFlip, hij, heq]
    calc
      (oddAdj u).card ≤ flips.card := Finset.card_le_card hsub
      _ ≤ n := by
        dsimp [flips]
        calc
          _ ≤ Finset.univ.card := Finset.card_image_le
          _ = n := by simp
  have refPool_card_le {n : ℕ} {N : ℕ} {β γ : ℝ} (P : Pos β γ n)
      (u : OddRole n)
      (hc : ∀ v ∈ oddAdj u, ∀ l, (countAt P v l : ℝ) ≤ 2 * lamH n) :
      ((refPool P u).card : ℝ) ≤ (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) := by
    classical
    let B : CubeVertex n → Fin (topH β γ n + 1) → Finset (Loc β γ n) := fun v l =>
      Finset.univ.filter fun c => P c = true ∧ c.2 = l ∧ _root_.hammingDist c.1 v ≤ radius β γ n
    let U : Finset (Loc β γ n) := (oddAdj u).biUnion fun v =>
      Finset.univ.biUnion fun l : Fin (topH β γ n + 1) => B v l
    have hsub : refPool P u ⊆ U := by
      intro c hc'
      rcases Finset.mem_filter.mp hc' with ⟨_, ⟨hP, v, hv, hd⟩⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨v, hv, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨c.2, Finset.mem_univ _, ?_⟩
      simp [B, hP, hd]
    have hball (v : CubeVertex n) (l : Fin (topH β γ n + 1)) :
        (B v l).card = countAt P v l := by
      let V : Finset (CubeVertex n) := Finset.univ.filter fun x =>
        P (x, l) = true ∧ _root_.hammingDist x v ≤ radius β γ n
      have himage : B v l = V.image (fun x => (x, l)) := by
        ext c
        constructor
        · intro hc'
          rcases Finset.mem_filter.mp hc' with ⟨_, ⟨hP, hl, hd⟩⟩
          rcases c with ⟨x, lev⟩
          simp at hl
          subst lev
          refine Finset.mem_image.mpr ⟨x, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro hP hd⟩
          · rfl
        · intro hc'
          rcases Finset.mem_image.mp hc' with ⟨x, hx, rfl⟩
          have hx' := (Finset.mem_filter.mp hx).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hx'.1, rfl, hx'.2⟩⟩
      rw [himage, Finset.card_image_of_injective]
      · simp [countAt, V]
      · intro x y h
        exact congrArg Prod.fst h
    have hU : (U.card : ℝ) ≤
        ((∑ v ∈ oddAdj u, ∑ l : Fin (topH β γ n + 1), (B v l).card : ℕ) : ℝ) := by
      have h1 : U.card ≤ ∑ v ∈ oddAdj u,
          (Finset.univ.biUnion fun l : Fin (topH β γ n + 1) => B v l).card :=
        Finset.card_biUnion_le
      have h2 : (∑ v ∈ oddAdj u,
          (Finset.univ.biUnion fun l : Fin (topH β γ n + 1) => B v l).card) ≤
            ∑ v ∈ oddAdj u, ∑ l : Fin (topH β γ n + 1), (B v l).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact Finset.card_biUnion_le
      exact_mod_cast h1.trans h2
    have hnbr : ((oddAdj u).card : ℝ) ≤ n := by exact_mod_cast oddAdj_card_le u
    calc
      ((refPool P u).card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((∑ v ∈ oddAdj u, ∑ l : Fin (topH β γ n + 1), (B v l).card : ℕ) : ℝ) := hU
      _ = ∑ v ∈ oddAdj u, ∑ l : Fin (topH β γ n + 1), ((B v l).card : ℝ) := by
        simp only [Nat.cast_sum]
      _ ≤ ∑ v ∈ oddAdj u, ∑ l : Fin (topH β γ n + 1), (countAt P v l : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        apply Finset.sum_le_sum
        intro l hl
        rw [hball v l]
      _ ≤ (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) := by
        calc
          _ ≤ ∑ v ∈ oddAdj u, ∑ l : Fin (topH β γ n + 1), (2 * lamH n) := by
            apply Finset.sum_le_sum
            intro v hv
            apply Finset.sum_le_sum
            intro l hl
            exact hc v hv l
          _ = ((oddAdj u).card : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
          _ ≤ (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) := by
            have hlev : 0 ≤ ((topH β γ n + 1 : ℕ) : ℝ) := by positivity
            have hlam : 0 ≤ lamH n := by dsimp [lamH]; positivity
            have hfac : 0 ≤ ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) :=
              mul_nonneg hlev (mul_nonneg (by norm_num) hlam)
            have hm := mul_le_mul_of_nonneg_right hnbr hfac
            nlinarith [hm]
  have topH_poly (n : ℕ) (hn : 2 ≤ n) :
      (topH β γ n : ℝ) ≤
        (2 : ℝ) ^ (⌈(2 - zetaH β γ) / sigmaH β γ⌉₊ + 1) *
          (n : ℝ) ^ (sigmaH β γ * (⌈(2 - zetaH β γ) / sigmaH β γ⌉₊ : ℝ) + 2) := by
    let σ : ℝ := sigmaH β γ
    let ζ : ℝ := zetaH β γ
    let I : ℕ := ⌈(2 - ζ) / σ⌉₊
    have hω := omega4_pos hβ hγ
    have hσ : 0 < σ := by dsimp [σ, sigmaH, zetaH, b0H, bH]; positivity
    have hζpos : 0 < ζ := by dsimp [ζ, zetaH, b0H, bH]; positivity
    have hζlt : ζ < 1 := by
      have hωlt := omega4_lt hβ hβγ
      dsimp [ζ, zetaH, b0H, bH]
      linarith
    have hI : 2 - ζ ≤ σ * (I : ℝ) := by
      have hceil : (2 - ζ) / σ ≤ I := by dsimp [I]; exact Nat.le_ceil _
      have := (div_le_iff₀ hσ).mp hceil
      nlinarith
    have hnreal : (1 : ℝ) ≤ n := by
      have hn1 : 1 ≤ n := by omega
      exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    let R0 : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
    let M0 : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
    let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
    have hR0pos : 1 ≤ R0 := by dsimp [R0]; omega
    have hMlow : (n : ℝ) ^ σ ≤ (M0 : ℝ) := by
      dsimp [M0]
      rw [Nat.cast_max]
      calc
        (n : ℝ) ^ σ ≤ (⌈(n : ℝ) ^ σ⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ max 2 (⌈(n : ℝ) ^ σ⌉₊ : ℝ) := le_max_right _ _
    have hMpow : 1 ≤ (n : ℝ) ^ σ := Real.one_le_rpow hnreal hσ.le
    have hMup : (M0 : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
      dsimp [M0]
      rw [Nat.cast_max]
      apply max_le
      · calc
          (2 : ℝ) = 2 * 1 := by ring
          _ ≤ 2 * (n : ℝ) ^ σ :=
            mul_le_mul_of_nonneg_left hMpow (by norm_num : (0 : ℝ) ≤ 2)
      · have hceil : (⌈(n : ℝ) ^ σ⌉₊ : ℝ) < (n : ℝ) ^ σ + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        linarith
    have hlognonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
    have hlogle : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self (by positivity)
    have hlogsq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have hgap : 0 ≤ (n : ℝ) - Real.log (n : ℝ) := by linarith
      have hsum : 0 ≤ (n : ℝ) + Real.log (n : ℝ) := by linarith
      have hprod := mul_nonneg hgap hsum
      nlinarith [hprod]
    have hR0up : (R0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
      dsimp [R0]
      rw [Nat.cast_max]
      apply max_le
      · have hnposN : 0 < n := by omega
        have hn2N : 0 < n ^ 2 := by positivity
        have hn2Nat : 1 ≤ 2 * n ^ 2 := by
          calc
            1 ≤ 2 := by norm_num
            _ ≤ 2 * n ^ 2 := Nat.mul_le_mul_left 2
              (Nat.one_le_iff_ne_zero.mpr hn2N.ne')
        exact_mod_cast hn2Nat
      · have hceil : (⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) < Real.log (n : ℝ) ^ 2 + 1 :=
          Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))
        have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((n : ℝ) - 1)]
        have hdouble : (n : ℝ) ^ 2 + 1 ≤ (n : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
          nlinarith [hn2]
        have hceilBound : Real.log (n : ℝ) ^ 2 + 1 ≤ (n : ℝ) ^ 2 + 1 := by
          calc
            Real.log (n : ℝ) ^ 2 + 1 = 1 + Real.log (n : ℝ) ^ 2 := by ring
            _ ≤ 1 + (n : ℝ) ^ 2 := add_le_add_right hlogsq 1
            _ = (n : ℝ) ^ 2 + 1 := by ring
        calc
          (⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) ≤ Real.log (n : ℝ) ^ 2 + 1 := hceil.le
          _ ≤ (n : ℝ) ^ 2 + 1 := hceilBound
          _ = 1 + (n : ℝ) ^ 2 := by ring
          _ = (n : ℝ) ^ 2 + 1 := by ring
          _ ≤ (n : ℝ) ^ 2 + (n : ℝ) ^ 2 := hdouble
          _ = 2 * (n : ℝ) ^ 2 := by ring
    have hpowBeta : 1 ≤ (n : ℝ) ^ (1 - ζ) := Real.one_le_rpow hnreal (by linarith)
    have htargetCeil : (target : ℝ) < (n : ℝ) ^ (1 - ζ) + 1 := by
      simpa [target] using Nat.ceil_lt_add_one
        (show 0 ≤ (n : ℝ) ^ (1 - ζ) by positivity)
    have hpowerAdd : (n : ℝ) ^ (2 - ζ) = (n : ℝ) * (n : ℝ) ^ (1 - ζ) := by
      rw [show (2 : ℝ) - ζ = 1 + (1 - ζ) by ring, Real.rpow_add hnpos, Real.rpow_one]
    have htargetSmall : (target : ℝ) ≤ (n : ℝ) ^ (2 - ζ) := by
      have hlin : 2 * (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) ^ (2 - ζ) := by
        rw [hpowerAdd]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn)
          (by positivity : 0 ≤ (n : ℝ) ^ (1 - ζ))
      linarith [htargetCeil, hlin, hpowBeta]
    have hpowExp : (n : ℝ) ^ (2 - ζ) ≤ (n : ℝ) ^ (σ * I) :=
      Real.rpow_le_rpow_of_exponent_le hnreal hI
    have hpowM : (n : ℝ) ^ (σ * I) ≤ (M0 : ℝ) ^ I := by
      have hmul : ((n : ℝ) ^ σ) ^ I ≤ (M0 : ℝ) ^ I :=
        pow_le_pow_left₀ (by positivity) hMlow I
      have hpow : ((n : ℝ) ^ σ) ^ I = (n : ℝ) ^ (σ * (I : ℝ)) := by
        rw [← Real.rpow_natCast, (Real.rpow_mul hnpos.le σ (I : ℝ)).symm]
      simpa [hpow] using hmul
    have htargetReal : (target : ℝ) ≤ (M0 : ℝ) ^ I * (R0 : ℝ) := by
      calc
        (target : ℝ) ≤ (n : ℝ) ^ (2 - ζ) := htargetSmall
        _ ≤ (n : ℝ) ^ (σ * I) := hpowExp
        _ ≤ (M0 : ℝ) ^ I := hpowM
        _ ≤ (M0 : ℝ) ^ I * (R0 : ℝ) := by
          have hr0 : (1 : ℝ) ≤ (R0 : ℝ) := by exact_mod_cast hR0pos
          have hm0 : 0 ≤ (M0 : ℝ) ^ I := by positivity
          calc
            (M0 : ℝ) ^ I = (M0 : ℝ) ^ I * 1 := by ring
            _ ≤ (M0 : ℝ) ^ I * (R0 : ℝ) := mul_le_mul_of_nonneg_left hr0 hm0
    have htargetNat : target ≤ M0 ^ I * R0 := by exact_mod_cast htargetReal
    have hscale : ∃ i, target ≤ M0 ^ i * R0 := ⟨I, htargetNat⟩
    have hfind : Nat.find hscale ≤ I := Nat.find_min' hscale htargetNat
    have htopEq : topH β γ n = M0 ^ Nat.find hscale * R0 := by
      simp [topH, topScale, M0, R0, target, hscale, σ, ζ, I]
    have htopNat : M0 ^ Nat.find hscale * R0 ≤ M0 ^ I * R0 := by
      exact Nat.mul_le_mul_right R0 (pow_le_pow_right' (a := M0) (by dsimp [M0]; omega) hfind)
    have hmain : (2 * (n : ℝ) ^ σ) ^ I * (2 * (n : ℝ) ^ 2) =
        (2 : ℝ) ^ (I + 1) * (n : ℝ) ^ (σ * I + 2) := by
      rw [mul_pow]
      have hpowSI : ((n : ℝ) ^ σ) ^ I = (n : ℝ) ^ (σ * (I : ℝ)) := by
        rw [← Real.rpow_natCast, (Real.rpow_mul hnpos.le σ (I : ℝ)).symm]
      rw [hpowSI]
      have hn2 : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (n : ℝ) 2).symm
      rw [hn2]
      calc
        (2 : ℝ) ^ I * (n : ℝ) ^ (σ * (I : ℝ)) *
            (2 * (n : ℝ) ^ (2 : ℝ)) =
          ((2 : ℝ) ^ I * 2) * ((n : ℝ) ^ (σ * (I : ℝ)) * (n : ℝ) ^ (2 : ℝ)) := by ring
        _ = ((2 : ℝ) ^ I * 2) * (n : ℝ) ^ (σ * (I : ℝ) + 2) := by
          rw [← Real.rpow_add hnpos]
        _ = (2 : ℝ) ^ (I + 1) * (n : ℝ) ^ (σ * (I : ℝ) + 2) := by rw [pow_succ]
    calc
      (topH β γ n : ℝ) = (M0 ^ Nat.find hscale * R0 : ℕ) := by rw [htopEq]
      _ ≤ (M0 ^ I * R0 : ℕ) := by exact_mod_cast htopNat
      _ ≤ (2 * (n : ℝ) ^ σ) ^ I * (2 * (n : ℝ) ^ 2) := by
        have hm := pow_le_pow_left₀ (by positivity) hMup I
        have hr := hR0up
        calc
          (M0 ^ I * R0 : ℕ) = (M0 : ℝ) ^ I * (R0 : ℝ) := by simp
          _ ≤ (2 * (n : ℝ) ^ σ) ^ I * (2 * (n : ℝ) ^ 2) :=
            mul_le_mul hm hr (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (I + 1) * (n : ℝ) ^ (σ * I + 2) := hmain
  have refSets_card_le {n : ℕ} (P : Pos β γ n) (u : OddRole n) (c : Loc β γ n) :
      (refSets P u c).card ≤ ((refPool P u).card + 1) ^ (2 * setBd β γ n) := by
    classical
    have bounded_powerset_card (s : Finset (Loc β γ n)) (T : ℕ) :
        ((s.powerset.filter fun D => D.card ≤ T).card) ≤ (s.card + 1) ^ (2 * T) := by
      let U : Finset (Finset (Loc β γ n)) :=
        (Finset.range (T + 1)).biUnion fun i => s.powersetCard i
      have hpowersetSub : s.powerset.filter (fun D => D.card ≤ T) ⊆ U := by
        intro D hD
        rcases Finset.mem_filter.mp hD with ⟨hDs, hDT⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨D.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hDT), ?_⟩
        exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hDs, rfl⟩
      by_cases hs : s.card = 0
      · have hsempty : s = ∅ := Finset.card_eq_zero.mp hs
        have hpowerset : s.powerset = {∅} := by simp [hsempty]
        have hfilter : ({∅} : Finset (Finset (Loc β γ n))).filter
            (fun D => D.card ≤ T) = {∅} := by
          ext D
          by_cases hD : D = ∅ <;> simp [hD]
        rw [hpowerset, hfilter]
        simp [hsempty]
      have hq : 2 ≤ s.card + 1 := by omega
      have hTpow : T + 1 ≤ 2 ^ T := T.lt_two_pow_self.succ_le
      have hTbase : T + 1 ≤ (s.card + 1) ^ T := by
        exact hTpow.trans (pow_le_pow_left' hq T)
      have hsum : (∑ i ∈ Finset.range (T + 1), (s.powersetCard i).card) ≤
          (T + 1) * (s.card + 1) ^ T := by
        calc
          _ ≤ ∑ i ∈ Finset.range (T + 1), (s.card + 1) ^ T := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.card_powersetCard]
            have hiT : i ≤ T := by simp only [Finset.mem_range] at hi; omega
            calc
              Nat.choose s.card i ≤ s.card ^ i := Nat.choose_le_pow _ _
              _ ≤ (s.card + 1) ^ i := pow_le_pow_left' (Nat.le_succ _) _
              _ ≤ (s.card + 1) ^ T := pow_le_pow_right' (by omega) hiT
          _ = (T + 1) * (s.card + 1) ^ T := by simp [Finset.sum_const, nsmul_eq_mul]
      calc
        (s.powerset.filter fun D => D.card ≤ T).card ≤ U.card := Finset.card_le_card hpowersetSub
        _ ≤ ∑ i ∈ Finset.range (T + 1), (s.powersetCard i).card := Finset.card_biUnion_le
        _ ≤ (T + 1) * (s.card + 1) ^ T := hsum
        _ ≤ (s.card + 1) ^ T * (s.card + 1) ^ T := Nat.mul_le_mul_right _ hTbase
        _ = (s.card + 1) ^ (2 * T) := by rw [← pow_add]; congr 1 <;> omega
    have hsub : refSets P u c ⊆
        (refPool P u).powerset.filter (fun D => D.card ≤ setBd β γ n) := by
      intro D hD
      change D ∈ (refPool P u).powerset.filter
        (fun D => c ∈ D ∧ D.card ≤ setBd β γ n) at hD
      rcases Finset.mem_filter.mp hD with ⟨hDsub, ⟨_, hDcard⟩⟩
      exact Finset.mem_filter.mpr ⟨hDsub, hDcard⟩
    calc
      (refSets P u c).card ≤ ((refPool P u).powerset.filter fun D => D.card ≤ setBd β γ n).card :=
        Finset.card_le_card hsub
      _ ≤ ((refPool P u).card + 1) ^ (2 * setBd β γ n) :=
        bounded_powerset_card (refPool P u) (setBd β γ n)
  have row_deleted_bound {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
      {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
      (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n)
      (z : Fin (tupLen β γ n) → Fin N) (y : Fin n → Fin N) (j : Fin n)
      (hEv : EvLocal M tag (updW ω (c, key β γ n a.1) z) a c) :
      oddRow M tag (updW ω (c, key β γ n a.1) z) (oddNbr a j) (y j) ≤
        (refSets (ppos ω) (oddNbr a j) c).card *
          (ratioThr β γ (oddNbr a j) (key β γ n a.1))⁻¹ *
            (refRow M tag ω (oddNbr a j) c (key β γ n a.1)).w (y j) := by
    classical
    let ω' := updW ω (c, key β γ n a.1) z
    let u := oddNbr a j
    let κ := key β γ n a.1
    let D := selSet M tag ω' u
    have hOdd : OddOK M tag ω' u := hEv.odd_ok j
    have hValid : Valid M tag u (paux ω') D := hOdd.2
    have hneigh : a.1 ∈ oddAdj u := by simpa [u] using even_mem_oddAdj a j
    have hcD : c ∈ D := by
      dsimp [D, selSet]
      apply Finset.mem_biUnion.mpr
      refine ⟨a.1, hneigh, ?_⟩
      simp [ω', hEv.sel_eq]
    have hDsub : D ⊆ refPool (ppos ω) u := by
      intro d hd
      have hd' := selectedSet_pool M tag ω' u d hd
      simpa [D, ω', updW, ppos] using hd'
    have hDcard : D.card ≤ setBd β γ n := hValid.card_le
    have hDmem : D ∈ refSets (ppos ω) u c := by
      change D ∈ (refPool (ppos ω) u).powerset.filter
        (fun D => c ∈ D ∧ D.card ≤ setBd β γ n)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hDsub, ⟨hcD, hDcard⟩⟩
    have hcount : ∀ v ∈ oddAdj u, ∀ l,
        (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n := by
      intro v hv l
      simpa [u, ω', updW, ppos] using hEv.counts j v hv l
    have hRef : RefOK M tag ω u c := ⟨hcount, ⟨D, hDmem⟩⟩
    have hκZ : κ ∈ Zset β γ u := by
      dsimp [κ, Zset]
      exact Finset.mem_image.mpr ⟨a.1, hneigh, rfl⟩
    have hW {d : Loc β γ n} {κ' : Key β γ n}
        (hne : (d, κ') ≠ (c, κ)) :
        Function.update (aW (paux ω)) (c, κ) z (d, κ') = aW (paux ω) (d, κ') :=
      Function.update_of_ne hne z (aW (paux ω))
    have hbut (x : Fin N) :
        HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ x =
          HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ x := by
      apply propext
      constructor <;> intro hh d hd κ' hκ' hne l
      · have hh' := hh d hd κ' hκ' hne l
        change Hits E G (Function.update (aW (paux ω)) (c, κ) z (d, κ') l) x at hh'
        rw [hW hne] at hh'
        exact hh'
      · have hh' := hh d hd κ' hκ' hne l
        change Hits E G (aW (paux ω) (d, κ') l) x at hh'
        rw [← hW hne] at hh'
        exact hh'
    have hbutFun :
        (fun x => HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ x) =
          fun x => HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ x := funext hbut
    have hmask : aym (paux ω') u = aym (paux ω) u := rfl
    let Pbut : ℝ :=
      (maskLaw (aym (paux ω) u)).pr (HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ)
    let Rall : ℝ :=
      (maskLaw (aym (paux ω') u)).pr (HitsAll E G (aW (paux ω')) D (Zset β γ u))
    have hPbutEq :
        (maskLaw (aym (paux ω') u)).pr (HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ) = Pbut := by
      dsimp [Pbut]
      rw [hmask]
      exact congrArg (fun Q : Fin N → Prop => (maskLaw (aym (paux ω) u)).pr Q) hbutFun
    have hRpos : 0 < Rall := lt_of_lt_of_le (Real.exp_pos _) hValid.mass
    have hAllToBut (x : Fin N) :
        HitsAll E G (aW (paux ω')) D (Zset β γ u) x →
          HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ x := by
      intro h d hd κ' hκ' _ l
      exact h d hd κ' hκ' l
    have hRle : Rall ≤
        (maskLaw (aym (paux ω') u)).pr
          (HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ) := by
      exact pr_mono (maskLaw (aym (paux ω') u)) hAllToBut
    have hPbutPos : 0 < Pbut := by
      rw [← hPbutEq]
      exact lt_of_lt_of_le hRpos hRle
    have hratio :
        ratioThr β γ u κ * Pbut ≤ Rall := by
      have hratio' : ratioThr β γ u κ *
          (maskLaw (aym (paux ω') u)).pr
            (HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ) ≤ Rall := by
        simpa [Rall] using hValid.ratio c hcD κ hκZ
      rw [hPbutEq] at hratio'
      exact hratio'
    have hratioPos : 0 < ratioThr β γ u κ := by
      unfold ratioThr
      split_ifs <;> exact Real.exp_pos _
    have hfrac : Pbut / Rall ≤ (ratioThr β γ u κ)⁻¹ := by
      apply (div_le_iff₀ hRpos).2
      calc
        Pbut = (ratioThr β γ u κ)⁻¹ * (ratioThr β γ u κ * Pbut) := by
          rw [← mul_assoc, inv_mul_cancel₀ hratioPos.ne']
          ring
        _ ≤ (ratioThr β γ u κ)⁻¹ * Rall :=
          mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr hratioPos.le)
    have hrowEq : oddRow M tag ω' u (y j) =
        (if HitsAll E G (aW (paux ω')) D (Zset β γ u) (y j) then
          (maskLaw (aym (paux ω') u)).w (y j) / Rall else 0) := by
      by_cases hhit : HitsAll E G (aW (paux ω')) D (Zset β γ u) (y j)
      · simp [oddRow, oddDraw, ω', u, D, hOdd, Rall, FinProb.cond, hhit]
      · simp [oddRow, oddDraw, ω', u, D, hOdd, Rall, FinProb.cond, hhit]
    have hcardPos : 0 < ((refSets (ppos ω) u c).card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr hRef.2)
    have hdelMix :
        (delLaw M tag ω u D c κ).w (y j) / ((refSets (ppos ω) u c).card : ℝ) ≤
          (refRow M tag ω u c κ).w (y j) := by
      have hunif :
          (FinProb.uniform (refSets (ppos ω) u c) hRef.2).w D =
            ((refSets (ppos ω) u c).card : ℝ)⁻¹ := by
        simp [FinProb.uniform, hDmem]
      have hmix : ((refSets (ppos ω) u c).card : ℝ)⁻¹ * (delLaw M tag ω u D c κ).w (y j) ≤
          (refRow M tag ω u c κ).w (y j) := by
        unfold refRow
        rw [dif_pos hRef]
        change _ ≤ ∑ D' ∈ Finset.univ,
          (FinProb.uniform (refSets (ppos ω) u c) hRef.2).w D' *
            (delLaw M tag ω u D' c κ).w (y j)
        rw [← hunif]
        have hsingle := Finset.single_le_sum
          (fun D' hD' => mul_nonneg
            ((FinProb.uniform (refSets (ppos ω) u c) hRef.2).nonneg D')
            ((delLaw M tag ω u D' c κ).nonneg (y j))) (Finset.mem_univ D)
        simpa using hsingle
      simpa [div_eq_mul_inv, mul_comm] using hmix
    by_cases hHit : HitsAll E G (aW (paux ω')) D (Zset β γ u) (y j)
    · have hHitBut : HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ (y j) :=
        hAllToBut (y j) hHit
      have hHitOld : HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ (y j) := by
        simpa [hbut (y j)] using hHitBut
      have hdelEq : (delLaw M tag ω u D c κ).w (y j) =
          (maskLaw (aym (paux ω) u)).w (y j) / Pbut := by
        simp [delLaw, Pbut, hPbutPos, hHitOld, FinProb.cond]
      have hquot :
          (maskLaw (aym (paux ω') u)).w (y j) / Rall ≤
            (ratioThr β γ u κ)⁻¹ * (delLaw M tag ω u D c κ).w (y j) := by
        calc
          (maskLaw (aym (paux ω') u)).w (y j) / Rall =
              ((maskLaw (aym (paux ω') u)).w (y j) / Pbut) * (Pbut / Rall) := by
            field_simp [ne_of_gt hPbutPos, ne_of_gt hRpos]
            <;> ring
          _ ≤ ((maskLaw (aym (paux ω') u)).w (y j) / Pbut) *
              (ratioThr β γ u κ)⁻¹ :=
            mul_le_mul_of_nonneg_left hfrac
              (div_nonneg ((maskLaw (aym (paux ω') u)).nonneg _) hPbutPos.le)
          _ = (ratioThr β γ u κ)⁻¹ * (delLaw M tag ω u D c κ).w (y j) := by
            rw [hmask, hdelEq]
            ring
      rw [hrowEq, if_pos hHit]
      calc
        (maskLaw (aym (paux ω') u)).w (y j) / Rall ≤
            (ratioThr β γ u κ)⁻¹ * (delLaw M tag ω u D c κ).w (y j) := hquot
        _ ≤ (ratioThr β γ u κ)⁻¹ *
            ((refSets (ppos ω) u c).card * (refRow M tag ω u c κ).w (y j)) := by
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left
              ((div_le_iff₀ hcardPos).mp hdelMix)
              (inv_nonneg.mpr hratioPos.le)
        _ = (refSets (ppos ω) u c).card * (ratioThr β γ u κ)⁻¹ *
            (refRow M tag ω u c κ).w (y j) := by ring
    · rw [hrowEq, if_neg hHit]
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (inv_nonneg.mpr hratioPos.le))
        ((refRow M tag ω u c κ).nonneg (y j))
  have exp_neg_inv (x : ℝ) : (Real.exp (-x))⁻¹ = Real.exp x := by
    rw [Real.exp_neg]
    simp
  have hωpos : 0 < omega4 β γ := omega4_pos hβ hγ
  have hωlt : omega4 β γ < 1 / 1000 := omega4_lt hβ hβγ
  have hωsmall : omega4 β γ ≤ (1 - γ) / 1000 := by
    dsimp [omega4]
    have := min_le_right β (1 - γ)
    nlinarith
  have heta : 0 < omega4 β γ / 10 := by positivity
  let ε : ℝ := (c1 - c2) / 4
  have hε : 0 < ε := by dsimp [ε, c1, c2]; norm_num
  have hδcross : 0 < 1 - γ - 14 * omega4 β γ - 2 * h4 β γ := by
    dsimp [h4]
    nlinarith [hωsmall]
  have hδmix : 0 < omega4 β γ / 3 - h4 β γ - bH β γ - omega4 β γ / 10 := by
    dsimp [h4, bH]
    nlinarith [hωpos]
  let η : ℝ := omega4 β γ / 10
  let I₀ : ℕ := ⌈(2 - zetaH β γ) / sigmaH β γ⌉₊
  let A₀ : ℝ := (2 : ℝ) ^ (I₀ + 1)
  let K₀ : ℝ := 2 * (A₀ + 1) + 1
  let Cmix : ℝ := 8 * (K₀ + 16 / η)
  have hK₀pos : 0 < K₀ := by dsimp [K₀]; positivity
  have poolLogBound (n : ℕ) (hn2 : 2 ≤ n) :
      Real.log (((n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1) ^
        (2 * setBd β γ n)) ≤ Cmix * (n : ℝ) ^ (bH β γ + η) := by
    let σ : ℝ := sigmaH β γ
    let ζ : ℝ := zetaH β γ
    let I : ℕ := I₀
    have hσpos : 0 < σ := by dsimp [σ, sigmaH, zetaH, b0H, bH]; positivity
    have hζpos : 0 < ζ := by dsimp [ζ, zetaH, b0H, bH]; positivity
    have hζlt : ζ < 1 := by
      have hω' := omega4_lt hβ hβγ
      dsimp [ζ, zetaH, b0H, bH]
      linarith
    have hσlt : σ < 1 := by
      have hω' := omega4_lt hβ hβγ
      dsimp [σ, sigmaH, zetaH, b0H, bH]
      linarith
    have hIceil : (I : ℝ) < (2 - ζ) / σ + 1 := by
      dsimp [I, I₀]
      apply Nat.ceil_lt_add_one
      exact div_nonneg (by linarith [hζlt]) hσpos.le
    have hσI : σ * (I : ℝ) < 2 - ζ + σ := by
      calc
        σ * (I : ℝ) < σ * ((2 - ζ) / σ + 1) := mul_lt_mul_of_pos_left hIceil hσpos
        _ = 2 - ζ + σ := by field_simp [ne_of_gt hσpos]
    have hExp : σ * (I : ℝ) + 2 ≤ 5 := by linarith [hζpos, hσlt, hσI]
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hnpos : (0 : ℝ) < n := by linarith
    have hHexp : (n : ℝ) ^ (σ * (I : ℝ) + 2) ≤ (n : ℝ) ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnreal hExp
    have hH : (topH β γ n : ℝ) ≤ A₀ * (n : ℝ) ^ (5 : ℝ) := by
      calc
        (topH β γ n : ℝ) ≤
            (2 : ℝ) ^ (I + 1) * (n : ℝ) ^ (σ * (I : ℝ) + 2) := by
              simpa [I, I₀, σ, sigmaH] using topH_poly n hn2
        _ ≤ A₀ * (n : ℝ) ^ (5 : ℝ) := by
              dsimp [A₀]
              exact mul_le_mul_of_nonneg_left hHexp (by positivity)
    have hn5 : (1 : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
      exact Real.one_le_rpow hnreal (by norm_num)
    have hn5Nat : (1 : ℝ) ≤ (n : ℝ) ^ 5 := one_le_pow₀ hnreal
    have hHplus : ((topH β γ n + 1 : ℕ) : ℝ) ≤ (A₀ + 1) * (n : ℝ) ^ 5 := by
      rw [Nat.cast_add, Nat.cast_one]
      have hn5' : (n : ℝ) ^ (5 : ℝ) = (n : ℝ) ^ 5 :=
        Real.rpow_natCast (n : ℝ) 5
      rw [hn5'] at hH
      calc
        (topH β γ n : ℝ) + 1 ≤ A₀ * (n : ℝ) ^ 5 + 1 := by
          simpa [add_comm] using add_le_add_right hH 1
        _ ≤ A₀ * (n : ℝ) ^ 5 + (n : ℝ) ^ 5 := by
          calc
            A₀ * (n : ℝ) ^ 5 + 1 = 1 + A₀ * (n : ℝ) ^ 5 := by ring
            _ ≤ (n : ℝ) ^ 5 + A₀ * (n : ℝ) ^ 5 :=
              add_le_add_left hn5Nat (A₀ * (n : ℝ) ^ 5)
            _ = A₀ * (n : ℝ) ^ 5 + (n : ℝ) ^ 5 := by ac_rfl
        _ = (A₀ + 1) * (n : ℝ) ^ 5 := by ring_nf
    have hpow16 : (n : ℝ) * (n : ℝ) ^ 5 * (n : ℝ) ^ 10 = (n : ℝ) ^ 16 := by
      calc
        (n : ℝ) * (n : ℝ) ^ 5 * (n : ℝ) ^ 10 =
            ((n : ℝ) ^ 1) * (n : ℝ) ^ 5 * (n : ℝ) ^ 10 := by rw [pow_one]
        _ = (n : ℝ) ^ (1 + 5) * (n : ℝ) ^ 10 := by rw [← pow_add]
        _ = (n : ℝ) ^ (1 + 5 + 10) := by rw [← pow_add]
        _ = (n : ℝ) ^ 16 := by norm_num
    have hn10' : (n : ℝ) ^ (10 : ℝ) = (n : ℝ) ^ 10 :=
      Real.rpow_natCast (n : ℝ) 10
    have hPB :
        (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) ≤
          2 * (A₀ + 1) * (n : ℝ) ^ 16 := by
      calc
        (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) ≤
            (n : ℝ) * ((A₀ + 1) * (n : ℝ) ^ 5) * (2 * (n : ℝ) ^ 10) := by
              dsimp [lamH]
              rw [hn10']
              gcongr <;> rfl
        _ = 2 * (A₀ + 1) * ((n : ℝ) * (n : ℝ) ^ 5 * (n : ℝ) ^ 10) := by ring
        _ = 2 * (A₀ + 1) * (n : ℝ) ^ 16 := by rw [hpow16]
    have hn16 : (1 : ℝ) ≤ (n : ℝ) ^ 16 := by
      exact one_le_pow₀ hnreal
    have hPBplus :
        (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1 ≤
          K₀ * (n : ℝ) ^ 16 := by
      have hsum :
          (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1 ≤
            2 * (A₀ + 1) * (n : ℝ) ^ 16 + 1 := by
          simpa [add_comm] using add_le_add_right hPB 1
      have hPBstep :
          2 * (A₀ + 1) * (n : ℝ) ^ 16 + 1 ≤
            (2 * (A₀ + 1) + 1) * (n : ℝ) ^ 16 := by
        calc
          2 * (A₀ + 1) * (n : ℝ) ^ 16 + 1 = 1 + 2 * (A₀ + 1) * (n : ℝ) ^ 16 := by ring
          _ ≤ (n : ℝ) ^ 16 + 2 * (A₀ + 1) * (n : ℝ) ^ 16 :=
            add_le_add_left hn16 (2 * (A₀ + 1) * (n : ℝ) ^ 16)
          _ = (2 * (A₀ + 1) + 1) * (n : ℝ) ^ 16 := by ring
      calc
        (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1 ≤
            2 * (A₀ + 1) * (n : ℝ) ^ 16 + 1 := hsum
        _ ≤ (2 * (A₀ + 1) + 1) * (n : ℝ) ^ 16 := hPBstep
        _ = K₀ * (n : ℝ) ^ 16 := by rfl
    have hPBpos : 0 ≤ (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hH0 : 0 ≤ ((topH β γ n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hLamNonneg : 0 ≤ lamH n := by dsimp [lamH]; positivity
      exact mul_nonneg (mul_nonneg hn0 hH0) (mul_nonneg (by norm_num) hLamNonneg)
    have hnpos : (0 : ℝ) < n := by positivity
    have hlogBase :
        Real.log ((n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1) ≤
          (K₀ + 16 / η) * (n : ℝ) ^ η := by
      have hlogmul : Real.log (K₀ * (n : ℝ) ^ 16) = Real.log K₀ + 16 * Real.log (n : ℝ) := by
        rw [Real.log_mul (ne_of_gt hK₀pos) (ne_of_gt (pow_pos hnpos 16)), Real.log_pow]
        push_cast <;> ring
      have hlogn := Real.log_natCast_le_rpow_div n heta
      have hnη : (1 : ℝ) ≤ (n : ℝ) ^ η := Real.one_le_rpow hnreal heta.le
      have hKterm : K₀ ≤ K₀ * (n : ℝ) ^ η := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left hnη hK₀pos.le
      calc
        Real.log ((n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1) ≤
            Real.log (K₀ * (n : ℝ) ^ 16) :=
          Real.log_le_log (by linarith [hPBpos]) hPBplus
        _ = Real.log K₀ + 16 * Real.log (n : ℝ) := hlogmul
        _ ≤ K₀ + 16 * ((n : ℝ) ^ η / η) := by
          exact add_le_add (Real.log_le_self hK₀pos.le)
            (mul_le_mul_of_nonneg_left hlogn (by norm_num))
        _ ≤ (K₀ + 16 / η) * (n : ℝ) ^ η := by
          have hsum : K₀ + 16 * ((n : ℝ) ^ η / η) ≤
              K₀ * (n : ℝ) ^ η + 16 * ((n : ℝ) ^ η / η) := by nlinarith [hKterm]
          calc
            _ ≤ K₀ * (n : ℝ) ^ η + 16 * ((n : ℝ) ^ η / η) := hsum
            _ = (K₀ + 16 / η) * (n : ℝ) ^ η := by ring
    have hbpos : 0 < bH β γ := by dsimp [bH]; positivity
    have hnpowb : (1 : ℝ) ≤ (n : ℝ) ^ bH β γ := Real.one_le_rpow hnreal hbpos.le
    have hTceil : (setBd β γ n : ℝ) < 3 * (n : ℝ) ^ bH β γ + 1 := by
      simpa [setBd] using Nat.ceil_lt_add_one (show 0 ≤ 3 * (n : ℝ) ^ bH β γ by positivity)
    have hT : (setBd β γ n : ℝ) ≤ 4 * (n : ℝ) ^ bH β γ := by nlinarith [hTceil, hnpowb]
    have hT2 : ((2 * setBd β γ n : ℕ) : ℝ) ≤ 8 * (n : ℝ) ^ bH β γ := by
      push_cast
      linarith
    have hlogbase0 :
        0 ≤ Real.log ((n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1) :=
      Real.log_nonneg (by linarith [hPBpos])
    have hpowprod : (n : ℝ) ^ bH β γ * (n : ℝ) ^ η =
        (n : ℝ) ^ (bH β γ + η) := by
      rw [← Real.rpow_add hnpos]
    have hlogM :
        Real.log (((n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1) ^
          (2 * setBd β γ n)) ≤ Cmix * (n : ℝ) ^ (bH β γ + η) := by
      rw [Real.log_pow]
      calc
        ((2 * setBd β γ n : ℕ) : ℝ) *
            Real.log ((n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1) ≤
          8 * (n : ℝ) ^ bH β γ *
            Real.log ((n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1) :=
          mul_le_mul_of_nonneg_right hT2 hlogbase0
        _ ≤ 8 * (n : ℝ) ^ bH β γ * ((K₀ + 16 / η) * (n : ℝ) ^ η) :=
          mul_le_mul_of_nonneg_left hlogBase (by positivity)
        _ = Cmix * (n : ℝ) ^ (bH β γ + η) := by
          dsimp [Cmix]
          calc
            _ = 8 * (K₀ + 16 / η) * ((n : ℝ) ^ bH β γ * (n : ℝ) ^ η) := by ring
            _ = 8 * (K₀ + 16 / η) * (n : ℝ) ^ (bH β γ + η) := by rw [hpowprod]
    exact hlogM
  have hδcross_tendsto :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - γ - 14 * omega4 β γ - 2 * h4 β γ))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδcross).comp tendsto_natCast_atTop_atTop
  have hδmix_tendsto :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) ^ (omega4 β γ / 3 - h4 β γ - bH β γ - η))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδmix).comp tendsto_natCast_atTop_atTop
  obtain ⟨nCross, hnCross⟩ :=
    Filter.eventually_atTop.1 (hδcross_tendsto.eventually_ge_atTop (ε⁻¹))
  obtain ⟨nMix, hnMix⟩ :=
    Filter.eventually_atTop.1
      (hδmix_tendsto.eventually_ge_atTop (Cmix / ε))
  have errorBounds {n : ℕ} (hn : max 2 (max nCross nMix) ≤ n) :
      (n : ℝ) ^ (γ + 14 * omega4 β γ) * capL β γ n ≤
          ε * aStar β γ n * (n : ℝ) ∧
        Real.log (((n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1) ^
          (2 * setBd β γ n)) ≤
            ε * aStar β γ n * (tupLen β γ n : ℝ) := by
    have hn2 : 2 ≤ n := le_trans (le_max_left 2 (max nCross nMix)) hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnpos : (0 : ℝ) < n := by linarith
    have hmax : max nCross nMix ≤ n := (le_max_right 2 (max nCross nMix)).trans hn
    have hCrossNat : nCross ≤ n := (le_max_left nCross nMix).trans hmax
    have hMixNat : nMix ≤ n := (le_max_right nCross nMix).trans hmax
    have hCrossPow : ε⁻¹ ≤ (n : ℝ) ^ (1 - γ - 14 * omega4 β γ - 2 * h4 β γ) :=
      hnCross n hCrossNat
    have hCrossExp :
        γ + 14 * omega4 β γ + h4 β γ +
          (1 - γ - 14 * omega4 β γ - 2 * h4 β γ) = 1 - h4 β γ := by ring
    have hAstarn : aStar β γ n * (n : ℝ) = (n : ℝ) ^ (1 - h4 β γ) := by
      calc
        aStar β γ n * (n : ℝ) = (n : ℝ) ^ (-h4 β γ) * (n : ℝ) ^ (1 : ℝ) := by
          simp [aStar, Real.rpow_one]
        _ = (n : ℝ) ^ (1 - h4 β γ) := by
          rw [← Real.rpow_add hnpos]
          congr 1
          ring
    have hCrossLow :
        (n : ℝ) ^ (γ + 14 * omega4 β γ) * capL β γ n ≤
          ε * (n : ℝ) ^ (1 - h4 β γ) := by
      have hpow : (n : ℝ) ^ (γ + 14 * omega4 β γ + h4 β γ) ≤
          (n : ℝ) ^ (1 - h4 β γ - (1 - γ - 14 * omega4 β γ - 2 * h4 β γ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hnreal
        rw [show 1 - h4 β γ - (1 - γ - 14 * omega4 β γ - 2 * h4 β γ) =
          γ + 14 * omega4 β γ + h4 β γ by ring]
      have hdiv :
          (n : ℝ) ^ (1 - h4 β γ - (1 - γ - 14 * omega4 β γ - 2 * h4 β γ)) / ε ≤
            (n : ℝ) ^ (1 - h4 β γ) := by
        calc
          _ = ε⁻¹ * (n : ℝ) ^
              (1 - h4 β γ - (1 - γ - 14 * omega4 β γ - 2 * h4 β γ)) := by ring
          _ ≤ (n : ℝ) ^ (1 - γ - 14 * omega4 β γ - 2 * h4 β γ) *
                (n : ℝ) ^
                  (1 - h4 β γ - (1 - γ - 14 * omega4 β γ - 2 * h4 β γ)) :=
              mul_le_mul_of_nonneg_right hCrossPow (Real.rpow_nonneg hnpos.le _)
          _ = (n : ℝ) ^ (1 - h4 β γ) := by
              rw [← Real.rpow_add hnpos]
              congr 1
              ring
      have hmul := (div_le_iff₀ hε).1 hdiv
      have hmul' : (n : ℝ) ^ (γ + 14 * omega4 β γ + h4 β γ) ≤
          ε * (n : ℝ) ^ (1 - h4 β γ) := by
        calc
          _ ≤ (n : ℝ) ^ (1 - h4 β γ - (1 - γ - 14 * omega4 β γ - 2 * h4 β γ)) := hpow
          _ ≤ ε * (n : ℝ) ^ (1 - h4 β γ) := by nlinarith [hmul]
      calc
        (n : ℝ) ^ (γ + 14 * omega4 β γ) * capL β γ n =
            (n : ℝ) ^ (γ + 14 * omega4 β γ + h4 β γ) := by
          rw [capL]
          rw [← Real.rpow_add hnpos]
        _ ≤ ε * (n : ℝ) ^ (1 - h4 β γ) := hmul'
    have hMixPow : Cmix / ε ≤ (n : ℝ) ^ (omega4 β γ / 3 - h4 β γ - bH β γ - η) :=
      hnMix n hMixNat
    have htup : (n : ℝ) ^ (omega4 β γ / 3) ≤ (tupLen β γ n : ℝ) := by
      dsimp [tupLen]
      exact Nat.le_ceil _
    have hAstark : (n : ℝ) ^ (omega4 β γ / 3 - h4 β γ) ≤
        aStar β γ n * (tupLen β γ n : ℝ) := by
      calc
        (n : ℝ) ^ (omega4 β γ / 3 - h4 β γ) =
            (n : ℝ) ^ (-h4 β γ) * (n : ℝ) ^ (omega4 β γ / 3) := by
          rw [← Real.rpow_add hnpos]
          congr 1
          ring
        _ ≤ aStar β γ n * (tupLen β γ n : ℝ) :=
          mul_le_mul_of_nonneg_left htup (Real.rpow_nonneg hnpos.le _)
    have hMixDiv :
        Cmix * (n : ℝ) ^ (bH β γ + η) / ε ≤
          (n : ℝ) ^ (omega4 β γ / 3 - h4 β γ) := by
      calc
        _ = (Cmix / ε) * (n : ℝ) ^ (bH β γ + η) := by ring
        _ ≤ (n : ℝ) ^ (omega4 β γ / 3 - h4 β γ - bH β γ - η) *
              (n : ℝ) ^ (bH β γ + η) :=
            mul_le_mul_of_nonneg_right hMixPow (Real.rpow_nonneg hnpos.le _)
        _ = (n : ℝ) ^ (omega4 β γ / 3 - h4 β γ) := by
          rw [← Real.rpow_add hnpos]
          congr 1
          ring
    have hMixSmall :
        Cmix * (n : ℝ) ^ (bH β γ + η) ≤
          ε * aStar β γ n * (tupLen β γ n : ℝ) := by
      have hmul := (div_le_iff₀ hε).1 hMixDiv
      calc
        Cmix * (n : ℝ) ^ (bH β γ + η) ≤ ε * (n : ℝ) ^ (omega4 β γ / 3 - h4 β γ) := by
          nlinarith [hmul]
        _ ≤ ε * (aStar β γ n * (tupLen β γ n : ℝ)) :=
          mul_le_mul_of_nonneg_left hAstark hε.le
        _ = ε * aStar β γ n * (tupLen β γ n : ℝ) := by ring
    refine ⟨?_, ?_⟩
    · rw [← hAstarn] at hCrossLow
      simpa [mul_assoc] using hCrossLow
    · calc
        Real.log (((n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n) + 1) ^
            (2 * setBd β γ n)) ≤ Cmix * (n : ℝ) ^ (bH β γ + η) := poolLogBound n hn2
        _ ≤ ε * aStar β γ n * (tupLen β γ n : ℝ) := hMixSmall
  refine ⟨max 2 (max nCross nMix), ?_⟩
  intro n hn hlocal N E G X Y M tag
  have hnlarge : max 2 (max nCross nMix) ≤ n := hn
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 (max nCross nMix)) hnlarge
  have hcost := errorBounds hnlarge
  intro ω a c z y
  let ω' := updW ω (c, key β γ n a.1) z
  have hrefProdNonneg : 0 ≤ refProd M tag ω a c y := by
    unfold refProd
    apply Finset.prod_nonneg
    intro j hj
    exact (refRow M tag ω (oddNbr a j) c (key β γ n a.1)).nonneg (y j)
  by_cases hEv : EvLocal M tag ω' a c
  · let Jdiff : Finset (Fin n) := Finset.univ.filter fun j =>
      key β γ n (oddNbr a j).1 ≠ key β γ n a.1
    let κ : Key β γ n := key β γ n a.1
    let k : ℝ := (tupLen β γ n : ℝ)
    let ownExp : ℝ := k * (Real.log 2 - c1 * aStar β γ n)
    let diffExp : ℝ := capL β γ n * k
    let poolBound : ℝ :=
      (n : ℝ) * ((topH β γ n + 1 : ℕ) : ℝ) * (2 * lamH n)
    let Cref : ℝ := (poolBound + 1) ^ (2 * setBd β γ n)
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnpos : (0 : ℝ) < n := by linarith
    have hstarle : aStar β γ n ≤ 1 := by
      unfold aStar
      have hh4 : 0 ≤ h4 β γ := by unfold h4; positivity
      exact Real.rpow_le_one_of_one_le_of_nonpos hnreal (neg_nonpos.mpr hh4)
    have hloggap : 0 ≤ Real.log 2 - c1 * aStar β γ n := by
      have hlog2 := Real.log_two_gt_d9
      dsimp [c1]
      nlinarith [hstarle]
    have hownNonneg : 0 ≤ ownExp := by
      dsimp [ownExp, k]
      exact mul_nonneg (Nat.cast_nonneg _) hloggap
    have hJdiff : ∀ j, j ∈ Jdiff ↔ κ ≠ key β γ n (oddNbr a j).1 := by
      intro j
      simp [Jdiff, κ, oddNbr, ne_comm]
    have hJcard : (Jdiff.card : ℝ) ≤ (n : ℝ) ^ (γ + 14 * omega4 β γ) := by
      have hlocal' := hlocal a.1
      have heq : Jdiff = Finset.univ.filter fun j : Fin n =>
          key β γ n (cubeFlip a.1 j) ≠ key β γ n a.1 := by
        ext j
        simp [Jdiff, oddNbr, ne_comm]
      rw [heq]
      exact hlocal'
    have hRatioEach (j : Fin n) :
        (ratioThr β γ (oddNbr a j) κ)⁻¹ ≤
          Real.exp (ownExp + if j ∈ Jdiff then diffExp else 0) := by
      by_cases hj : j ∈ Jdiff
      · have hneq : κ ≠ key β γ n (oddNbr a j).1 := (hJdiff j).mp hj
        have hratioEq : ratioThr β γ (oddNbr a j) κ = Real.exp (-diffExp) := by
          rw [ratioThr, if_neg hneq]
        rw [hratioEq]
        simpa [hj] using (exp_neg_inv diffExp).le.trans
          (Real.exp_le_exp.mpr (by nlinarith [hownNonneg]))
      · have hsame : κ = key β γ n (oddNbr a j).1 := by
          by_contra hneq
          exact hj ((hJdiff j).mpr hneq)
        have hratioEq : ratioThr β γ (oddNbr a j) κ = Real.exp (-ownExp) := by
          rw [ratioThr, if_pos hsame]
          apply congrArg Real.exp
          dsimp [ownExp, k, c1]
          ring
        rw [hratioEq, if_neg hj]
        simpa [add_zero] using (exp_neg_inv ownExp).le
    have hExpSum :
        (∑ j : Fin n, (ownExp + if j ∈ Jdiff then diffExp else 0)) =
          (n : ℝ) * ownExp + (Jdiff.card : ℝ) * diffExp := by
      have hOwnSum : (∑ j : Fin n, ownExp) = (n : ℝ) * ownExp := by simp
      have hDiffSum :
          (∑ j : Fin n, (if j ∈ Jdiff then diffExp else 0)) =
            (Jdiff.card : ℝ) * diffExp := by
        simpa [Finset.sum_const, nsmul_eq_mul] using
          (Finset.sum_ite_mem_eq (s := Jdiff) (f := fun _ : Fin n => diffExp))
      calc
        _ = (∑ j : Fin n, ownExp) + (∑ j : Fin n, (if j ∈ Jdiff then diffExp else 0)) :=
          Finset.sum_add_distrib
        _ = (n : ℝ) * ownExp + (Jdiff.card : ℝ) * diffExp := by rw [hOwnSum, hDiffSum]
    have hRatioProduct :
        (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) ≤
          Real.exp (ownExp * (n : ℝ) + diffExp * (Jdiff.card : ℝ)) := by
      have hratioNonneg (j : Fin n) :
          0 ≤ (ratioThr β γ (oddNbr a j) κ)⁻¹ := by
        have hpos : 0 < ratioThr β γ (oddNbr a j) κ := by
          unfold ratioThr
          split_ifs <;> exact Real.exp_pos _
        exact inv_nonneg.mpr hpos.le
      calc
        (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) ≤
            ∏ j : Fin n, Real.exp (ownExp + if j ∈ Jdiff then diffExp else 0) := by
          apply Finset.prod_le_prod₀
          · intro j hj
            exact hratioNonneg j
          · intro j hj
            exact hRatioEach j
        _ = Real.exp (∑ j : Fin n, (ownExp + if j ∈ Jdiff then diffExp else 0)) := by
          rw [← Real.exp_sum]
        _ = Real.exp (ownExp * (n : ℝ) + diffExp * (Jdiff.card : ℝ)) := by
          rw [hExpSum]
          ring_nf
    have hpoolBoundNonneg : 0 ≤ poolBound := by
      dsimp [poolBound, lamH]
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg n) (by positivity))
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    have hCrefPos : 0 < Cref := by
      dsimp [Cref]
      exact pow_pos (by linarith [hpoolBoundNonneg]) _
    have hCrefLog : Real.log Cref ≤ Cmix * (n : ℝ) ^ (bH β γ + η) := by
      simpa [Cref, poolBound] using poolLogBound n hn2
    have hCrefPow : Cref ^ n = Real.exp ((n : ℝ) * Real.log Cref) := by
      calc
        Cref ^ n = (Real.exp (Real.log Cref)) ^ n := by rw [Real.exp_log hCrefPos]
        _ = Real.exp ((n : ℝ) * Real.log Cref) := by
          rw [← Real.exp_nat_mul]
    have hpoolCard (j : Fin n) :
        ((refPool (ppos ω) (oddNbr a j)).card : ℝ) ≤ poolBound := by
      have hpos : ppos ω' = ppos ω := rfl
      have hcounts : ∀ v ∈ oddAdj (oddNbr a j), ∀ l,
          (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n := by
        intro v hv l
        rw [← hpos]
        exact hEv.counts j v hv l
      simpa [poolBound] using
        (refPool_card_le (N := N) (ppos ω) (oddNbr a j) hcounts)
    have hsetCard (j : Fin n) :
        ((refSets (ppos ω) (oddNbr a j) c).card : ℝ) ≤ Cref := by
      have hsetNat := refSets_card_le (ppos ω) (oddNbr a j) c
      have hsetReal : ((refSets (ppos ω) (oddNbr a j) c).card : ℝ) ≤
          (((refPool (ppos ω) (oddNbr a j)).card : ℝ) + 1) ^ (2 * setBd β γ n) := by
        exact_mod_cast hsetNat
      have hpoolPlus : ((refPool (ppos ω) (oddNbr a j)).card : ℝ) + 1 ≤ poolBound + 1 := by
        nlinarith [hpoolCard j]
      calc
        ((refSets (ppos ω) (oddNbr a j) c).card : ℝ) ≤
            (((refPool (ppos ω) (oddNbr a j)).card : ℝ) + 1) ^ (2 * setBd β γ n) := hsetReal
        _ ≤ Cref := by
          dsimp [Cref]
          exact pow_le_pow_left₀ (by positivity) hpoolPlus _
    have hrowNonneg : ∀ j, 0 ≤ oddRow M tag ω' (oddNbr a j) (y j) := by
      intro j
      by_cases ho : OddOK M tag ω' (oddNbr a j)
      · simp [oddRow, ho]
        exact (oddDraw M tag ω' (oddNbr a j)).nonneg _
      · simp [oddRow, ho]
    have hrowCap (j : Fin n) :
        oddRow M tag ω' (oddNbr a j) (y j) ≤
          Cref * (ratioThr β γ (oddNbr a j) κ)⁻¹ *
            (refRow M tag ω (oddNbr a j) c κ).w (y j) := by
      have hrow := row_deleted_bound M tag ω a c z y j hEv
      have hratioPos : 0 < ratioThr β γ (oddNbr a j) κ := by
        unfold ratioThr
        split_ifs <;> exact Real.exp_pos _
      have hfactor : 0 ≤ (ratioThr β γ (oddNbr a j) κ)⁻¹ *
          (refRow M tag ω (oddNbr a j) c κ).w (y j) :=
        mul_nonneg (inv_nonneg.mpr hratioPos.le)
          ((refRow M tag ω (oddNbr a j) c κ).nonneg (y j))
      calc
        oddRow M tag ω' (oddNbr a j) (y j) ≤
            (refSets (ppos ω) (oddNbr a j) c).card *
              (ratioThr β γ (oddNbr a j) κ)⁻¹ *
                (refRow M tag ω (oddNbr a j) c κ).w (y j) := hrow
        _ ≤ Cref * (ratioThr β γ (oddNbr a j) κ)⁻¹ *
              (refRow M tag ω (oddNbr a j) c κ).w (y j) := by
          calc
            _ = ((refSets (ppos ω) (oddNbr a j) c).card : ℝ) *
                ((ratioThr β γ (oddNbr a j) κ)⁻¹ *
                  (refRow M tag ω (oddNbr a j) c κ).w (y j)) := by ring
            _ ≤ Cref *
                ((ratioThr β γ (oddNbr a j) κ)⁻¹ *
                  (refRow M tag ω (oddNbr a j) c κ).w (y j)) :=
              mul_le_mul_of_nonneg_right (hsetCard j) hfactor
            _ = Cref * (ratioThr β γ (oddNbr a j) κ)⁻¹ *
                (refRow M tag ω (oddNbr a j) c κ).w (y j) := by ring
    have hprodRefNonneg : 0 ≤ refProd M tag ω a c y := by
      unfold refProd
      apply Finset.prod_nonneg
      intro j hj
      exact (refRow M tag ω (oddNbr a j) c κ).nonneg (y j)
    have hprodRows :
        (∏ j : Fin n, oddRow M tag ω' (oddNbr a j) (y j)) ≤
          Cref ^ n * (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) *
            refProd M tag ω a c y := by
      calc
        (∏ j : Fin n, oddRow M tag ω' (oddNbr a j) (y j)) ≤
            ∏ j : Fin n,
              (Cref * (ratioThr β γ (oddNbr a j) κ)⁻¹ *
                (refRow M tag ω (oddNbr a j) c κ).w (y j)) := by
          apply Finset.prod_le_prod₀
          · intro j hj
            exact hrowNonneg j
          · intro j hj
            exact hrowCap j
        _ = Cref ^ n * (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) *
              refProd M tag ω a c y := by
          have hprodC : (∏ j : Fin n, Cref) = Cref ^ n := by
            rw [Finset.prod_const]
            simp
          have hprodRow :
              (∏ j : Fin n, (refRow M tag ω (oddNbr a j) c κ).w (y j)) =
                refProd M tag ω a c y := rfl
          have hfactor :
              (∏ j : Fin n,
                Cref * (ratioThr β γ (oddNbr a j) κ)⁻¹ *
                  (refRow M tag ω (oddNbr a j) c κ).w (y j)) =
                (∏ j : Fin n, Cref) *
                  (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) *
                    (∏ j : Fin n, (refRow M tag ω (oddNbr a j) c κ).w (y j)) := by
            simp_rw [mul_assoc]
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          calc
            _ = (∏ j : Fin n, Cref) *
                (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) *
                  (∏ j : Fin n, (refRow M tag ω (oddNbr a j) c κ).w (y j)) := hfactor
            _ = Cref ^ n * (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) *
                  refProd M tag ω a c y := by rw [hprodC, hprodRow]
    have hRatioCost :
        (n : ℝ) * Real.log Cref + ownExp * (n : ℝ) + diffExp * (Jdiff.card : ℝ) ≤
          (Real.log 2 - c2 * aStar β γ n) * k * (n : ℝ) := by
      have hErr := hcost
      have hCrossCount :
          capL β γ n * (Jdiff.card : ℝ) ≤ ε * aStar β γ n * (n : ℝ) := by
        have hcapNonneg : 0 ≤ capL β γ n := by
          dsimp [capL]
          exact Real.rpow_nonneg (Nat.cast_nonneg n) _
        calc
          capL β γ n * (Jdiff.card : ℝ) ≤
              capL β γ n * (n : ℝ) ^ (γ + 14 * omega4 β γ) :=
            mul_le_mul_of_nonneg_left hJcard hcapNonneg
          _ = (n : ℝ) ^ (γ + 14 * omega4 β γ) * capL β γ n := by ring
          _ ≤ ε * aStar β γ n * (n : ℝ) := hErr.1
      have hCrossExp : diffExp * (Jdiff.card : ℝ) ≤
          ε * aStar β γ n * k * (n : ℝ) := by
        dsimp [diffExp]
        calc
          capL β γ n * k * (Jdiff.card : ℝ) =
              k * (capL β γ n * (Jdiff.card : ℝ)) := by ring
          _ ≤ k * (ε * aStar β γ n * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hCrossCount (by positivity)
          _ = ε * aStar β γ n * k * (n : ℝ) := by ring
      have hMixExp : (n : ℝ) * Real.log Cref ≤
          ε * aStar β γ n * k * (n : ℝ) := by
        calc
          (n : ℝ) * Real.log Cref ≤
              (n : ℝ) * (ε * aStar β γ n * k) :=
            mul_le_mul_of_nonneg_left hErr.2 (by positivity)
          _ = ε * aStar β γ n * k * (n : ℝ) := by ring
      have hAstarnonneg : 0 ≤ aStar β γ n := by
        unfold aStar
        exact Real.rpow_nonneg (by positivity) _
      have hkNonneg : 0 ≤ k := by dsimp [k]; positivity
      have hnNonneg : 0 ≤ (n : ℝ) := by positivity
      have hcoef :
          Real.log 2 - c1 * aStar β γ n + 2 * ε * aStar β γ n ≤
            Real.log 2 - c2 * aStar β γ n := by
        have hepsCoeff : 2 * ε ≤ c1 - c2 := by dsimp [ε]; ring_nf; norm_num [c1, c2]
        have hmulCoeff := mul_le_mul_of_nonneg_right hepsCoeff hAstarnonneg
        dsimp [c1, c2] at hmulCoeff ⊢
        linarith [hmulCoeff]
      have hOwn : ownExp * (n : ℝ) +
          2 * (ε * aStar β γ n * k * (n : ℝ)) ≤
            (Real.log 2 - c2 * aStar β γ n) * k * (n : ℝ) := by
        dsimp [ownExp]
        calc
          k * (Real.log 2 - c1 * aStar β γ n) * (n : ℝ) +
              2 * (ε * aStar β γ n * k * (n : ℝ)) =
                k * (n : ℝ) *
                  (Real.log 2 - c1 * aStar β γ n + 2 * ε * aStar β γ n) := by ring
          _ ≤ k * (n : ℝ) * (Real.log 2 - c2 * aStar β γ n) :=
            mul_le_mul_of_nonneg_left hcoef (mul_nonneg hkNonneg hnNonneg)
          _ = (Real.log 2 - c2 * aStar β γ n) * k * (n : ℝ) := by ring
      calc
        (n : ℝ) * Real.log Cref + ownExp * (n : ℝ) + diffExp * (Jdiff.card : ℝ) ≤
            ownExp * (n : ℝ) +
              2 * (ε * aStar β γ n * k * (n : ℝ)) := by
          nlinarith [hMixExp, hCrossExp]
        _ ≤ (Real.log 2 - c2 * aStar β γ n) * k * (n : ℝ) := hOwn
    have hratioProductBound :
        Cref ^ n *
          (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) ≤
            Real.exp ((Real.log 2 - c2 * aStar β γ n) * k * (n : ℝ)) := by
      calc
        Cref ^ n *
            (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) =
          Real.exp ((n : ℝ) * Real.log Cref) *
            (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) := by rw [hCrefPow]
        _ ≤ Real.exp ((n : ℝ) * Real.log Cref) *
            Real.exp (ownExp * (n : ℝ) + diffExp * (Jdiff.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hRatioProduct (Real.exp_nonneg _)
        _ = Real.exp ((n : ℝ) * Real.log Cref + ownExp * (n : ℝ) +
              diffExp * (Jdiff.card : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp ((Real.log 2 - c2 * aStar β γ n) * k * (n : ℝ)) :=
          Real.exp_le_exp.mpr hRatioCost
    have hlik : lik M tag ω a c z y =
        ∏ j : Fin n, oddRow M tag ω' (oddNbr a j) (y j) := by
      simp [lik, ω', hEv]
    rw [hlik]
    calc
      (∏ j : Fin n, oddRow M tag ω' (oddNbr a j) (y j)) ≤
          Cref ^ n * (∏ j : Fin n, (ratioThr β γ (oddNbr a j) κ)⁻¹) *
            refProd M tag ω a c y := hprodRows
      _ ≤ Real.exp ((Real.log 2 - c2 * aStar β γ n) * k * (n : ℝ)) *
            refProd M tag ω a c y :=
          mul_le_mul_of_nonneg_right hratioProductBound hprodRefNonneg
      _ = Real.exp ((Real.log 2 - c2 * aStar β γ n) *
            (tupLen β γ n : ℝ) * (n : ℝ)) * refProd M tag ω a c y := by
          simp [k]
  · have hrefProdNonneg : 0 ≤ refProd M tag ω a c y := by
      unfold refProd
      apply Finset.prod_nonneg
      intro j hj
      exact (refRow M tag ω (oddNbr a j) c (key β γ n a.1)).nonneg (y j)
    simp [lik, ω', hEv]
    exact mul_nonneg (Real.exp_nonneg _) hrefProdNonneg
set_option maxHeartbeats 1000000

/-- L4.1g(3) (04:409–427): by `LikBound` and Lemma 3.7(2) (`gated_posterior`) the posterior `π(z) F_z(y)/M_c(y)`
is at most `exp((log 2 - c₂ a_*)kn) ε₄⁻¹ π(z)`, and `π(z) ≤ (2e^{sX}/N)^k`; it is supported on `S^k` (a positive
`F_z(y)` makes every `y_u` hit every entry of `z`, as `c ∈ D_u` and `g(a) ∈ Z_u`, and `π(z) > 0` puts the entries in
the mask).  So `1 ≤ |S|^k exp((log 2 - c₂ a_*)kn + c₂ a_* kn/4 + k(sX + log 2)) N^{-k}`, and `sX + log 2 ≤
c₂ a_* n/4` for large `n`. -/
theorem comm_large (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), LikBound M tag → CommLarge M tag := by
  classical
  have hc₂ : 0 < c2 := by dsimp [c2, c1]; norm_num
  have hgap : 0 < 1 - β - h4 β γ := by
    have hmin : min β (1 - γ) ≤ 1 - γ := min_le_right _ _
    have hω : omega4 β γ ≤ (1 - γ) / 1000 := by
      dsimp [omega4]
      exact div_le_div_of_nonneg_right hmin (by norm_num)
    have hh : h4 β γ ≤ (1 - γ) / 1000000000 := by
      dsimp [h4]
      dsimp [omega4] at hω ⊢
      norm_num at hω ⊢
      nlinarith
    have hγgap : 0 < 1 - γ := by linarith
    dsimp [h4]
    nlinarith [hh]
  have htgap : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ (1 - β - h4 β γ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (htgap.eventually_ge_atTop (20 / c2))
  refine ⟨max 2 n₀, ?_⟩
  intro n hn N E G X Y M tag hLB ω a c y hp
  have hnlarge : 2 ≤ n := le_trans (le_max_left 2 n₀) hn
  have hn₀' : n₀ ≤ n := (le_max_right 2 n₀).trans hn
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hnlarge)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hgapPow : 20 / c2 ≤ (n : ℝ) ^ (1 - β - h4 β γ) := hn₀ n hn₀'
  have hsmall : Real.log 2 + M.sX (tag (key β γ n a.1)) ≤
      c2 * aStar β γ n * (n : ℝ) / 8 := by
    have hpowβ : 1 ≤ (n : ℝ) ^ β := Real.one_le_rpow hnreal hβ.le
    have hlog2 : Real.log 2 ≤ 1 := by nlinarith [Real.log_two_lt_d9]
    have hsX := (M.prep (tag (key β γ n a.1))).2.1
    have htop : Real.log 2 + M.sX (tag (key β γ n a.1)) ≤ (5 / 2 : ℝ) * (n : ℝ) ^ β := by
      nlinarith [hsX, hpowβ, hlog2]
    have hpower : (n : ℝ) ^ β * (n : ℝ) ^ (1 - β - h4 β γ) =
        (n : ℝ) ^ (1 - h4 β γ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    have hAstarpower : aStar β γ n * (n : ℝ) = (n : ℝ) ^ (1 - h4 β γ) := by
      dsimp [aStar]
      calc
        (n : ℝ) ^ (-h4 β γ) * (n : ℝ) =
            (n : ℝ) ^ (-h4 β γ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (n : ℝ) ^ (1 - h4 β γ) := by
          rw [← Real.rpow_add hnpos]
          congr 1
          ring
    have hscaled := mul_le_mul_of_nonneg_left hgapPow
      (mul_nonneg (by positivity : (0 : ℝ) ≤ c2 / 8)
        (Real.rpow_nonneg hnpos.le β))
    have hscaled' : (5 / 2 : ℝ) * (n : ℝ) ^ β ≤
        (c2 / 8) * ((n : ℝ) ^ β * (n : ℝ) ^ (1 - β - h4 β γ)) := by
      dsimp [c2, c1] at hscaled ⊢
      nlinarith [hscaled]
    calc
      Real.log 2 + M.sX (tag (key β γ n a.1)) ≤ (5 / 2 : ℝ) * (n : ℝ) ^ β := htop
      _ ≤ (c2 / 8) * ((n : ℝ) ^ β * (n : ℝ) ^ (1 - β - h4 β γ)) := hscaled'
      _ = c2 * aStar β γ n * (n : ℝ) / 8 := by
        rw [hpower, ← hAstarpower]
        ring_nf
  have hN : 0 < N := by
    by_contra hN
    have hzero : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    have hsum := (M.μ (tag (key β γ n a.1))).sum_eq_one
    simp at hsum
  let κ : Key β γ n := key β γ n a.1
  let k : ℕ := tupLen β γ n
  let S : Finset (Fin N) := (comm M tag ω a c y)
  let Smask : Mask (M.μ (tag κ)) := axm (paux ω) (c, κ)
  let Q : Finset (Fin k → Fin N) := Finset.univ.filter fun z => ∀ t, z t ∈ S
  let A : ℝ := Real.log 2 - c2 * aStar β γ n
  let capX : ℝ := 2 * Real.exp (M.sX (tag κ)) / (N : ℝ)
  let L : ℝ := Real.exp (A * (k : ℝ) * (n : ℝ))
  have hμwidth : (M.μ (tag κ)).WidthLE (M.sX (tag κ)) :=
    (M.prep (tag κ)).2.2.2.2.1
  have hmaskCap (x : Fin N) : (maskLaw Smask).w x ≤ 2 * (M.μ (tag κ)).w x := by
    by_cases hx : x ∈ Smask.1
    · rw [maskLaw, Law.restrict]
      simp only [if_pos hx]
      apply (div_le_iff₀ (mask_mass_pos Smask)).2
      have hmul : (2 * (M.μ (tag κ)).w x) * (1 / 2) ≤
          (2 * (M.μ (tag κ)).w x) * (∑ x ∈ Smask.1, (M.μ (tag κ)).w x) :=
        mul_le_mul_of_nonneg_left Smask.2.2
          (mul_nonneg (by norm_num) ((M.μ (tag κ)).nonneg x))
      nlinarith [hmul]
    · rw [maskLaw, Law.restrict]
      simp only [if_neg hx]
      exact mul_nonneg (by norm_num) ((M.μ (tag κ)).nonneg x)
  have hcapXnonneg : 0 ≤ capX := by dsimp [capX]; positivity
  have hcoordCap (x : Fin N) : (maskLaw Smask).w x ≤ capX := by
    calc
      (maskLaw Smask).w x ≤ 2 * (M.μ (tag κ)).w x := hmaskCap x
      _ ≤ 2 * (Real.exp (M.sX (tag κ)) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (hμwidth x) (by norm_num)
      _ = capX := by dsimp [capX]; ring
  have hpriorCap (z : Fin k → Fin N) : (prior M tag ω c κ).w z ≤ capX ^ k := by
    simp only [prior, FinProb.pi]
    calc
      (∏ t : Fin k, (maskLaw Smask).w (z t)) ≤ ∏ _ : Fin k, capX := by
        apply Finset.prod_le_prod₀
        · intro t ht
          exact (maskLaw Smask).nonneg (z t)
        · intro t ht
          exact hcoordCap (z t)
      _ = capX ^ k := by simp
  have hQcard : Q.card = S.card ^ k := by
    let predSet : {z : Fin k → Fin N // z ∈ Q} ≃
        {z : Fin k → Fin N // ∀ t, z t ∈ S} :=
      { toFun := fun z => ⟨z.1, (Finset.mem_filter.mp z.2).2⟩
        invFun := fun z => ⟨z.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩⟩
        left_inv := by intro z; apply Subtype.ext; rfl
        right_inv := by intro z; apply Subtype.ext; rfl }
    let tupleEquiv : {z : Fin k → Fin N // ∀ t, z t ∈ S} ≃
        (Fin k → {x : Fin N // x ∈ S}) :=
      { toFun := fun z t => ⟨z.1 t, z.2 t⟩
        invFun := fun f => ⟨fun t => (f t).1, fun t => (f t).2⟩
        left_inv := by intro z; apply Subtype.ext; rfl
        right_inv := by intro f; funext t; apply Subtype.ext; rfl }
    calc
      Q.card = Fintype.card {z : Fin k → Fin N // z ∈ Q} := (Fintype.card_coe Q).symm
      _ = Fintype.card {z : Fin k → Fin N // ∀ t, z t ∈ S} := Fintype.card_congr predSet
      _ = Fintype.card (Fin k → {x : Fin N // x ∈ S}) := Fintype.card_congr tupleEquiv
      _ = S.card ^ k := by simp [Fintype.card_fun]
  have hrowNonneg (ω₀ : Prep M tag) (u : OddRole n) (v : Fin N) :
      0 ≤ oddRow M tag ω₀ u v := by
    unfold oddRow
    split_ifs
    · exact (oddDraw M tag ω₀ u).nonneg v
    · exact le_rfl
  have hlikNonneg (z : Fin k → Fin N) : 0 ≤ lik M tag ω a c z y := by
    unfold lik
    by_cases he : EvLocal M tag (updW ω (c, κ) z) a c
    · have he' : EvLocal M tag (updW ω (c, key β γ n a.1) z) a c := by
        simpa [κ] using he
      simp only [if_pos he', one_mul]
      apply Finset.prod_nonneg
      intro j hj
      exact hrowNonneg _ _ _
    · have he' : ¬ EvLocal M tag (updW ω (c, key β γ n a.1) z) a c := by
        simpa [κ] using he
      simp [he']
  have hrefProdNonneg : 0 ≤ refProd M tag ω a c y := by
    unfold refProd
    apply Finset.prod_nonneg
    intro j hj
    exact (refRow M tag ω (oddNbr a j) c κ).nonneg (y j)
  have hlikSupport (z : Fin k → Fin N) (hpriorPos : 0 < (prior M tag ω c κ).w z)
      (hlikPos : 0 < lik M tag ω a c z y) : z ∈ Q := by
    let ω' := updW ω (c, κ) z
    have hev : EvLocal M tag ω' a c := by
      by_contra h
      simp [lik, ω', κ, h] at hlikPos
    have hprod : 0 < ∏ j : Fin n, oddRow M tag ω' (oddNbr a j) (y j) := by
      simpa [lik, ω', κ, hev] using hlikPos
    have hpriorProd : 0 < ∏ t : Fin k, (maskLaw Smask).w (z t) := by
      simpa [prior, FinProb.pi] using hpriorPos
    have haOdd (j : Fin n) : a.1 ∈ oddAdj (oddNbr a j) := by
      unfold oddAdj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (cube n).Adj (cubeFlip a.1 j) a.1
      exact (cubeFlip_adj a.1 j).symm
    have hselD (j : Fin n) : c ∈ selSet M tag ω' (oddNbr a j) := by
      unfold selSet
      apply Finset.mem_biUnion.mpr
      refine ⟨a.1, haOdd j, ?_⟩
      simp [hev.sel_eq]
    have hkeyZ (j : Fin n) : κ ∈ Zset β γ (oddNbr a j) := by
      unfold Zset
      exact Finset.mem_image.mpr ⟨a.1, haOdd j, rfl⟩
    have hrowPos (j : Fin n) : 0 < oddRow M tag ω' (oddNbr a j) (y j) := by
      have hne : oddRow M tag ω' (oddNbr a j) (y j) ≠ 0 := by
        intro hz
        have hzero := Finset.prod_eq_zero (s := Finset.univ)
          (f := fun j : Fin n => oddRow M tag ω' (oddNbr a j) (y j)) (by simp) hz
        rw [hzero] at hprod
        exact (lt_irrefl 0) hprod
      exact lt_of_le_of_ne (hrowNonneg ω' (oddNbr a j) (y j)) (Ne.symm hne)
    have htupleMem (t : Fin k) : z t ∈ S := by
      have hcoordPos : 0 < (maskLaw Smask).w (z t) := by
        have hne : (maskLaw Smask).w (z t) ≠ 0 := by
          intro hz
          have hzero := Finset.prod_eq_zero (s := Finset.univ)
            (f := fun t : Fin k => (maskLaw Smask).w (z t)) (by simp) hz
          rw [hzero] at hpriorProd
          exact (lt_irrefl 0) hpriorProd
        exact lt_of_le_of_ne ((maskLaw Smask).nonneg (z t)) (Ne.symm hne)
      have hmask : z t ∈ Smask.1 := by
        by_contra hx
        have hz : (maskLaw Smask).w (z t) = 0 := by
          simp [maskLaw, Law.restrict, hx]
        exact hcoordPos.ne' hz
      change z t ∈ (axm (paux ω) (c, κ)).1.filter
        (fun x => ∀ j, Hits E G x (y j))
      rw [Finset.mem_filter]
      refine ⟨hmask, ?_⟩
      intro j
      have hoddOK : OddOK M tag ω' (oddNbr a j) := by
        by_contra h
        have hz : oddRow M tag ω' (oddNbr a j) (y j) = 0 := by simp [oddRow, h]
        linarith [hrowPos j]
      have hdrawPos : 0 < (oddDraw M tag ω' (oddNbr a j)).w (y j) := by
        simpa [oddRow, hoddOK] using hrowPos j
      have hhit : HitsAll E G (aW (paux ω')) (selSet M tag ω' (oddNbr a j))
          (Zset β γ (oddNbr a j)) (y j) := by
        by_contra h
        simp [oddDraw, hoddOK, FinProb.cond, h] at hdrawPos
      have h := hhit c (hselD j) κ (hkeyZ j) t
      simpa [ω', updW, paux, aW] using h
    simpa [Q] using htupleMem
  have hsumPos : 0 < marg M tag ω a c y := hp.1
  have htermPos : ∃ z, 0 < (prior M tag ω c κ).w z * lik M tag ω a c z y := by
    have hsum : 0 < ∑ z, (prior M tag ω c κ).w z * lik M tag ω a c z y := by
      simpa [marg] using hsumPos
    obtain ⟨z, hz, hzpos⟩ := (Finset.sum_pos_iff_of_nonneg fun z hz =>
      mul_nonneg ((prior M tag ω c κ).nonneg z) (hlikNonneg z)).mp hsum
    exact ⟨z, hzpos⟩
  obtain ⟨z₀, hz₀⟩ := htermPos
  have hpriorPos₀ : 0 < (prior M tag ω c κ).w z₀ := by
    by_contra h
    have hz : (prior M tag ω c κ).w z₀ = 0 := le_antisymm (le_of_not_gt h)
      ((prior M tag ω c κ).nonneg z₀)
    rw [hz, zero_mul] at hz₀
    exact (lt_irrefl 0) hz₀
  have hlikPos₀ : 0 < lik M tag ω a c z₀ y := by
    by_contra h
    have hz : lik M tag ω a c z₀ y = 0 := le_antisymm (le_of_not_gt h) (hlikNonneg z₀)
    rw [hz, mul_zero] at hz₀
    exact (lt_irrefl 0) hz₀
  have hQnonempty : Q.Nonempty := ⟨z₀, hlikSupport z₀ hpriorPos₀ hlikPos₀⟩
  have hrefProdPos : 0 < refProd M tag ω a c y := by
    by_contra h
    have hz : refProd M tag ω a c y = 0 := le_antisymm (le_of_not_gt h) hrefProdNonneg
    have hbound := hLB ω a c z₀ y
    rw [hz, mul_zero] at hbound
    linarith [hbound]
  have htermBound (z : Fin k → Fin N) :
      (prior M tag ω c κ).w z * lik M tag ω a c z y ≤
        if z ∈ Q then capX ^ k * L * refProd M tag ω a c y else 0 := by
    by_cases hzQ : z ∈ Q
    · have hLBz := hLB ω a c z y
      have hbound : (prior M tag ω c κ).w z * lik M tag ω a c z y ≤
          capX ^ k * L * refProd M tag ω a c y := by
        calc
          _ ≤ capX ^ k * lik M tag ω a c z y :=
            mul_le_mul_of_nonneg_right (hpriorCap z) (hlikNonneg z)
          _ ≤ capX ^ k * (L * refProd M tag ω a c y) :=
            mul_le_mul_of_nonneg_left (by simpa [L] using hLBz) (by positivity)
          _ = capX ^ k * L * refProd M tag ω a c y := by ring
      simpa [hzQ] using hbound
    · have htermNonneg : 0 ≤ (prior M tag ω c κ).w z * lik M tag ω a c z y :=
        mul_nonneg ((prior M tag ω c κ).nonneg z) (hlikNonneg z)
      have hzero : (prior M tag ω c κ).w z * lik M tag ω a c z y = 0 := by
        by_contra hne
        have hpos : 0 < (prior M tag ω c κ).w z * lik M tag ω a c z y :=
          lt_of_le_of_ne htermNonneg (Ne.symm hne)
        have hpz : 0 < (prior M tag ω c κ).w z := by
          by_contra hh
          have heq : (prior M tag ω c κ).w z = 0 := le_antisymm (le_of_not_gt hh)
            ((prior M tag ω c κ).nonneg z)
          rw [heq, zero_mul] at hpos
          exact (lt_irrefl 0) hpos
        have hlz : 0 < lik M tag ω a c z y := by
          by_contra hh
          have heq : lik M tag ω a c z y = 0 := le_antisymm (le_of_not_gt hh) (hlikNonneg z)
          rw [heq, mul_zero] at hpos
          exact (lt_irrefl 0) hpos
        exact hzQ (hlikSupport z hpz hlz)
      simp [hzQ, hzero]
  have hMargUpper : marg M tag ω a c y ≤
      (Q.card : ℝ) * (capX ^ k * L * refProd M tag ω a c y) := by
    calc
      marg M tag ω a c y = ∑ z, (prior M tag ω c κ).w z * lik M tag ω a c z y := by rfl
      _ ≤ ∑ z, if z ∈ Q then capX ^ k * L * refProd M tag ω a c y else 0 :=
        Finset.sum_le_sum fun z hz => htermBound z
      _ = (Q.card : ℝ) * (capX ^ k * L * refProd M tag ω a c y) := by
        simpa [Finset.sum_const, nsmul_eq_mul] using
          (Finset.sum_ite_mem_eq (s := Q) (f := fun _ : Fin k → Fin N =>
            capX ^ k * L * refProd M tag ω a c y))
  have hscaleMul : eps4 β γ n * refProd M tag ω a c y ≤
      ((Q.card : ℝ) * capX ^ k * L) * refProd M tag ω a c y := by
    calc
      eps4 β γ n * refProd M tag ω a c y ≤ marg M tag ω a c y := hp.2
      _ ≤ (Q.card : ℝ) * (capX ^ k * L * refProd M tag ω a c y) := hMargUpper
      _ = ((Q.card : ℝ) * capX ^ k * L) * refProd M tag ω a c y := by ring
  have hscale : eps4 β γ n ≤ (Q.card : ℝ) * capX ^ k * L :=
    le_of_mul_le_mul_right hscaleMul hrefProdPos
  have hcost : eps4 β γ n ≤ (S.card : ℝ) ^ k * capX ^ k *
      Real.exp ((Real.log 2 - c2 * aStar β γ n) * (k : ℝ) * (n : ℝ)) := by
    simpa [L, hQcard] using hscale
  have hcomm : (N : ℝ) * Real.exp
      (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ))) ≤ (S.card : ℝ) := by
    by_contra hnot
    have hSle : (S.card : ℝ) ≤ (N : ℝ) *
        Real.exp (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ))) :=
      (lt_of_not_ge hnot).le
    have hNnonzero : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
    have hTwoExp : 2 * Real.exp (M.sX (tag κ)) =
        Real.exp (Real.log 2 + M.sX (tag κ)) := by
      calc
        2 * Real.exp (M.sX (tag κ)) =
            Real.exp (Real.log 2) * Real.exp (M.sX (tag κ)) := by
              rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        _ = Real.exp (Real.log 2 + M.sX (tag κ)) := by rw [← Real.exp_add]
    have hcapExact : (N : ℝ) * Real.exp
        (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ))) * capX *
        Real.exp ((Real.log 2 - c2 * aStar β γ n) * (n : ℝ)) =
        Real.exp (Real.log 2 + M.sX (tag κ) - c2 * aStar β γ n * (n : ℝ) / 2) := by
      calc
        _ = Real.exp (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ))) *
              (2 * Real.exp (M.sX (tag κ))) *
                Real.exp ((Real.log 2 - c2 * aStar β γ n) * (n : ℝ)) := by
          dsimp [capX]
          field_simp [hNnonzero]
        _ = Real.exp (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ))) *
              Real.exp (Real.log 2 + M.sX (tag κ)) *
                Real.exp ((Real.log 2 - c2 * aStar β γ n) * (n : ℝ)) := by rw [hTwoExp]
        _ = Real.exp (Real.log 2 + M.sX (tag κ) -
              c2 * aStar β γ n * (n : ℝ) / 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring_nf
    have hAstarnonneg : 0 ≤ aStar β γ n := by
      unfold aStar
      exact Real.rpow_nonneg hnpos.le _
    have hDpos : 0 < c2 * aStar β γ n * (n : ℝ) := by
      have ha : 0 < aStar β γ n := by
        unfold aStar
        exact Real.rpow_pos_of_pos hnpos _
      positivity
    have hbase : Real.exp (Real.log 2 + M.sX (tag κ) -
        c2 * aStar β γ n * (n : ℝ) / 2) <
        Real.exp (-(c2 * aStar β γ n * (n : ℝ)) / 4) := by
      apply Real.exp_lt_exp.mpr
      nlinarith [hsmall, hAstarnonneg, hDpos]
    have hcostUpper : (S.card : ℝ) ^ k * capX ^ k *
        Real.exp ((Real.log 2 - c2 * aStar β γ n) * (k : ℝ) * (n : ℝ)) <
        Real.exp (-(c2 * aStar β γ n * (n : ℝ)) / 4) ^ k := by
      have hpowExp : Real.exp ((Real.log 2 - c2 * aStar β γ n) * (k : ℝ) * (n : ℝ)) =
          Real.exp ((Real.log 2 - c2 * aStar β γ n) * (n : ℝ)) ^ k := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc
        _ ≤ ((N : ℝ) * Real.exp
              (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ)))) ^ k * capX ^ k *
              Real.exp ((Real.log 2 - c2 * aStar β γ n) * (k : ℝ) * (n : ℝ)) := by
          gcongr
        _ = ((N : ℝ) * Real.exp
              (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ))) * capX *
                Real.exp ((Real.log 2 - c2 * aStar β γ n) * (n : ℝ))) ^ k := by
          rw [hpowExp, ← mul_pow, ← mul_pow]
        _ = Real.exp (Real.log 2 + M.sX (tag κ) -
              c2 * aStar β γ n * (n : ℝ) / 2) ^ k := by
          rw [hcapExact]
        _ < Real.exp (-(c2 * aStar β γ n * (n : ℝ)) / 4) ^ k :=
          pow_lt_pow_left₀ hbase (Real.exp_nonneg _) (by
            have hkpos : 0 < k := by
              dsimp [k, tupLen]
              exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos (omega4 β γ / 3))
            exact hkpos.ne')
    have hepsPow : Real.exp (-(c2 * aStar β γ n * (n : ℝ)) / 4) ^ k = eps4 β γ n := by
      dsimp [eps4]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hcostStrict : (S.card : ℝ) ^ k * capX ^ k *
        Real.exp ((Real.log 2 - c2 * aStar β γ n) * (k : ℝ) * (n : ℝ)) < eps4 β γ n := by
      simpa [hepsPow] using hcostUpper
    exact (not_lt_of_ge hcost) hcostStrict
  exact hcomm

/-- L4.1g (04:428–432): by definition an even row is zero or uniform on `S_{a,c}(y)` inside the mask of the
selected reference, on `E` and the predictive requirement; by `CommLarge` the set is nonempty there and
`N p_a ≤ N/|S| ≤ exp((log 2 - c₂ a_*/2) n)`. -/
theorem even_row_facts {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (_hcomm : CommLarge M tag) :
    EvenRowFacts M tag := by
  classical
  intro ω a y
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := Nat.eq_zero_of_not_pos hn
    subst N
    have hs := (M.μ (tag (key β γ n a.1))).sum_eq_one
    simp at hs
  have hcomm_pos (c : Loc β γ n) (hp : PredOK M tag ω a c y) :
      0 < (comm M tag ω a c y).card := by
    have hlower := _hcomm ω a c y hp
    have hpos : 0 < (N : ℝ) * Real.exp
        (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ))) :=
      mul_pos (by exact_mod_cast hN) (Real.exp_pos _)
    have hpos' : 0 < ((comm M tag ω a c y).card : ℝ) :=
      lt_of_lt_of_le hpos hlower
    exact_mod_cast hpos'
  have hsum_uniform (S : Finset (Fin N)) (hS : S.Nonempty) :
      (∑ x, if x ∈ S then (S.card : ℝ)⁻¹ else 0) = 1 := by
    rw [Finset.sum_ite_mem_eq]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard : (S.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hS).ne'
    field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold evenRowAt
    cases hs : sel M tag ω a.1 with
    | none => simp [hs]
    | some c =>
      simp only [hs, Option.elim_some]
      by_cases hg : EvLocal M tag ω a c ∧ PredOK M tag ω a c y ∧
          x ∈ comm M tag ω a c y
      · simp [hg]
      · simp [hg]
  · cases hs : sel M tag ω a.1 with
    | none => simp [evenRowAt, hs]
    | some c =>
      by_cases hg : EvLocal M tag ω a c ∧ PredOK M tag ω a c y
      · have hS : (comm M tag ω a c y).Nonempty := by
          exact Finset.card_pos.mp (hcomm_pos c hg.2)
        have := hsum_uniform (comm M tag ω a c y) hS
        simpa [evenRowAt, hs, hg] using this.le
      · have hzero : ∀ x, evenRowAt M tag ω a y x = 0 := by
          intro x
          simp only [evenRowAt, hs, Option.elim_some]
          by_cases hgate : EvLocal M tag ω a c ∧ PredOK M tag ω a c y ∧
              x ∈ comm M tag ω a c y
          · exact False.elim (hg ⟨hgate.1, hgate.2.1⟩)
          · simp [hgate]
        simp [hzero]
  · intro c hev hp
    have hc : sel M tag ω a.1 = some c := hev.sel_eq
    have hS : (comm M tag ω a c y).Nonempty := by
      exact Finset.card_pos.mp (hcomm_pos c hp)
    have hsum := hsum_uniform (comm M tag ω a c y) hS
    simpa [evenRowAt, hc, hev, hp, and_assoc] using hsum
  · intro x hx
    unfold evenRowAt at hx
    cases hs : sel M tag ω a.1 with
    | none => simp [hs] at hx
    | some c =>
      have hg : EvLocal M tag ω a c ∧ PredOK M tag ω a c y ∧
          x ∈ comm M tag ω a c y := by
        by_contra hnot
        simp [hs, hnot] at hx
      rcases hg with ⟨hev, hp, hmem⟩
      refine ⟨?_, ⟨c, rfl, hev, ?_⟩⟩
      · intro j
        exact (Finset.mem_filter.mp hmem).2 j
      · exact (Finset.mem_filter.mp hmem).1
  · intro x
    by_cases hz : evenRowAt M tag ω a y x = 0
    · simp [hz]
      exact (Real.exp_pos _).le
    · unfold evenRowAt at hz
      cases hs : sel M tag ω a.1 with
      | none => simp [hs] at hz
      | some c =>
        have hg : EvLocal M tag ω a c ∧ PredOK M tag ω a c y ∧
            x ∈ comm M tag ω a c y := by
          by_contra hnot
          simp [hs, hnot] at hz
        rcases hg with ⟨hev, hp, hmem⟩
        have hcard : 0 < ((comm M tag ω a c y).card : ℝ) := by
          exact_mod_cast (Finset.card_pos.mpr ⟨x, hmem⟩)
        have hlarge := _hcomm ω a c y hp
        let A : ℝ := (Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ)
        have hbound : (N : ℝ) ≤ (comm M tag ω a c y).card * Real.exp A := by
          have ht := mul_le_mul_of_nonneg_right hlarge (Real.exp_nonneg A)
          dsimp [A] at ht ⊢
          have he : Real.exp (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ))) *
                Real.exp ((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ)) = 1 := by
            rw [← Real.exp_add]
            simp
          calc
            (N : ℝ) = ((N : ℝ) * Real.exp
                (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ)))) *
                  Real.exp ((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ)) := by
                    rw [mul_assoc, he, mul_one]
            _ ≤ (comm M tag ω a c y).card * Real.exp
                  ((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ)) := ht
        have hratio : (N : ℝ) / (comm M tag ω a c y).card ≤ Real.exp A :=
          (div_le_iff₀ hcard).2 (by simpa [A, mul_comm] using hbound)
        have hrow : evenRowAt M tag ω a y x = ((comm M tag ω a c y).card : ℝ)⁻¹ := by
          simp [evenRowAt, hs, hev, hp, hmem]
        rw [hrow]
        simpa [A, div_eq_mul_inv] using hratio

end HypercubeRamsey.S04
