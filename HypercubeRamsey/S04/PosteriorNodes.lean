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
  sorry
set_option maxHeartbeats 200000

/-- L4.1g(3) (04:409–427): by `LikBound` and Lemma 3.7(2) (`gated_posterior`) the posterior `π(z) F_z(y)/M_c(y)`
is at most `exp((log 2 - c₂ a_*)kn) ε₄⁻¹ π(z)`, and `π(z) ≤ (2e^{sX}/N)^k`; it is supported on `S^k` (a positive
`F_z(y)` makes every `y_u` hit every entry of `z`, as `c ∈ D_u` and `g(a) ∈ Z_u`, and `π(z) > 0` puts the entries in
the mask).  So `1 ≤ |S|^k exp((log 2 - c₂ a_*)kn + c₂ a_* kn/4 + k(sX + log 2)) N^{-k}`, and `sX + log 2 ≤
c₂ a_* n/4` for large `n`. -/
theorem comm_large (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), LikBound M tag → CommLarge M tag := by
  sorry

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
