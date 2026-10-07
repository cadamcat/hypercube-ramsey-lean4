import HypercubeRamsey.S04.CoreLemmas
import HypercubeRamsey.S04.ProfileNodes_q_s04_prof
import HypercubeRamsey.Framework.Minimax
import HypercubeRamsey.S03.Mixtures

/-!
# L4.1h: mask profiles balancing the rows

Source: `sections/04-…tex`, lines 437–496; blueprint L4.1h.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- L4.1h, selection probability (04:469–477): `E` at `(a, c)` needs `c` present (probability `λ/V`), legal
eligibility on `a`'s consultation ball and `sel a = c`.  At level zero, given positions and masks/tuples,
L3.8i bounds `Pr(height 0 ∧ sel = c) ≤ 3/λ`; at a positive level, L3.8g with `c` forced present bounds
`Pr(legal ∧ height > 0) ≤ exp(-n^{c₃})`.  Both bounds are uniform over the eligibility selector, hence over all mask
profiles (`Aux` = masks × tuples). -/
theorem select_prob (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ c₃ > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), SelectBound M tag c₃ := by
  classical
  obtain ⟨c₃, hc₃, nHeight, hheight⟩ :=
    HypercubeRamsey.height_selection_positive 10 (b0H β γ) (bH β γ) (sigmaH β γ)
      (zetaH β γ) (thetaH β γ) (aH β γ) 1 1 2
      (hd_admissible hβ hβγ hγ) (hdRegime hβ hβγ hγ)
  let n₀ := max nHeight 1
  refine ⟨c₃, hc₃, n₀, ?_⟩
  intro n hn N E G X Y M tag q q' a c
  let p := hd β γ n
  let aux := auxLaw M tag q q'
  let base := p.posLaw.prod aux
  let forced := (p.posLawForced (some c)).prod aux
  let actTie := p.actLaw.prod p.tieLaw
  let w := p.lam / (p.V : ℝ)
  have hnHeight : nHeight ≤ n := le_trans (le_max_left _ _) hn
  have hnPos : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hLam : 0 < p.lam := by
    dsimp [p, hd, lamH]
    positivity
  have hV : 0 < p.V := by
    change 0 < ∑ i ∈ Finset.range (radius β γ n + 1), n.choose i
    have hmem : 0 ∈ Finset.range (radius β γ n + 1) := by simp
    have hsum : 1 ≤ ∑ i ∈ Finset.range ((radius β γ n) + 1), n.choose i := by
      calc
        1 = n.choose 0 := by simp
        _ ≤ ∑ i ∈ Finset.range ((radius β γ n) + 1), n.choose i :=
          Finset.single_le_sum (s := Finset.range ((radius β γ n) + 1))
            (f := fun i => n.choose i) (fun i hi => Nat.zero_le _) hmem
    exact lt_of_lt_of_le (by norm_num) hsum
  have hw : 0 ≤ w := div_nonneg hLam.le (Nat.cast_nonneg _)
  have hheightAt := hheight p rfl rfl rfl rfl rfl hnHeight
    (by simp [p, hd]) (by simp [p, hd]) (hdRegime_ok hβ hβγ hγ n)
  have ha : a.1 ∈ evenSites n := by simpa [evenSites] using a.2
  have haDom : a.1 ∈ p.domBall (evenSites n) a.1 p.Rlong := by
    simp [HDParams.domBall, evenSites, a.2]
  let ev : Prep M tag → Prop := fun ω => EvLocal M tag ω a c
  let assocEv : (Pos β γ n × Aux M tag) × ((p.Loc → Bool) × p.Ties) → Prop :=
    fun z => ev ((z.1, z.2.1), z.2.2)
  have hassoc : (prepLaw M tag q q').pr ev = (base.prod actTie).pr assocEv := by
    change ((base.prod p.actLaw).prod p.tieLaw).pr ev = (base.prod actTie).pr assocEv
    exact HypercubeRamsey.Lane_q_s04_prof.pr_prod_assoc base p.actLaw p.tieLaw ev
  have hweight : ∀ x : Pos β γ n × Aux M tag,
      (∃ y : (p.Loc → Bool) × p.Ties, assocEv (x, y)) →
        base.w x ≤ w * forced.w x := by
    intro x hx
    rcases x with ⟨P, auxVal⟩
    rcases hx with ⟨y, hEv⟩
    rcases y with ⟨A, τ⟩
    let ω : Prep M tag := (((P, auxVal), A), τ)
    have hEvent : EvLocal M tag ω a c := by simpa [assocEv, ev, ω] using hEv
    have hsel : p.selection (evenSites n) P A (elig M tag P auxVal) τ a.1 = some c := by
      simpa [sel, p, ω, ppos, paux, pact, pties] using hEvent.sel_eq
    obtain ⟨l, _, hmem, _⟩ :=
      HypercubeRamsey.Lane_q_s04_prof.selection_mem_height
        (p := p) (evenSites n) P A (elig M tag P auxVal) τ a.1 c hsel
    have hlegal := hEvent.legal a.1 haDom l
    have hPresent : P c = true := (hlegal.1 c hmem).1
    have hposWeight := HypercubeRamsey.Lane_q_s04_prof.pos_weight_le_forced c P hPresent
    have hprod : base.w (P, auxVal) ≤ w * forced.w (P, auxVal) := by
      change p.posLaw.w P * aux.w auxVal ≤
        w * ((p.posLawForced (some c)).w P * aux.w auxVal)
      calc
        p.posLaw.w P * aux.w auxVal ≤
            (w * (p.posLawForced (some c)).w P) * aux.w auxVal :=
          mul_le_mul_of_nonneg_right (by simpa [p, w] using hposWeight) (aux.nonneg auxVal)
        _ = w * ((p.posLawForced (some c)).w P * aux.w auxVal) := by ring
    simpa [base, forced, FinProb.prod] using hprod
  by_cases hc0 : c.2.val = 0
  · let zeroEv : (Pos β γ n × Aux M tag) × ((p.Loc → Bool) × p.Ties) → Prop :=
      fun z =>
        p.LegalAt z.1.1 (elig M tag z.1.1 z.1.2) a.1 ⟨0, by omega⟩ ∧
        c ∈ elig M tag z.1.1 z.1.2 a.1 ⟨0, by omega⟩ ∧
        p.height (evenSites n) z.1.1 z.2.1 (elig M tag z.1.1 z.1.2) p.Rlong a.1 = 0 ∧
        p.selection (evenSites n) z.1.1 z.2.1 (elig M tag z.1.1 z.1.2) z.2.2 a.1 = some c
    have hsub : ∀ z, assocEv z → zeroEv z := by
      intro z hz
      rcases z with ⟨⟨P, auxVal⟩, ⟨A, τ⟩⟩
      have hEvent : EvLocal M tag (((P, auxVal), A), τ) a c := by
        simpa [assocEv, ev] using hz
      have hsel : p.selection (evenSites n) P A (elig M tag P auxVal) τ a.1 = some c := by
        simpa [sel, p, ppos, paux, pact, pties] using hEvent.sel_eq
      obtain ⟨l, hlval, hmem, _⟩ :=
        HypercubeRamsey.Lane_q_s04_prof.selection_mem_height
          (p := p) (evenSites n) P A (elig M tag P auxVal) τ a.1 c hsel
      have hlegal := hEvent.legal a.1 haDom l
      have hlev : l.val = 0 := by
        have heq := congrArg Fin.val (hlegal.1 c hmem).2.1
        omega
      have hlzero : l = ⟨0, by omega⟩ := Fin.ext hlev
      have hheightzero : p.height (evenSites n) P A (elig M tag P auxVal) p.Rlong a.1 = 0 := by
        omega
      refine ⟨hEvent.legal a.1 haDom ⟨0, by omega⟩, ?_, hheightzero, ?_⟩
      · simpa [hlzero] using hmem
      · simpa [sel, p, ppos, paux, pact, pties] using hEvent.sel_eq
    have hscale : (base.prod actTie).pr assocEv ≤ w * (forced.prod actTie).pr zeroEv :=
      HypercubeRamsey.Lane_q_s04_prof.pr_prod_scale base forced actTie w hw
        assocEv zeroEv hsub hweight
    have hforcedZero : (forced.prod actTie).pr zeroEv ≤ 3 / p.lam := by
      rw [HypercubeRamsey.Lane_q_s04_prof.pr_prod_cond forced actTie
        (fun x y => zeroEv (x, y))]
      calc
        (∑ x, forced.w x * actTie.pr (fun t => zeroEv (x, t))) ≤
            ∑ x, forced.w x * (3 / p.lam) := by
              apply Finset.sum_le_sum
              intro x hx
              have hconditional : actTie.pr (fun t => zeroEv (x, t)) ≤ 3 / p.lam := by
                rcases x with ⟨P, auxVal⟩
                by_cases hlegal : p.LegalAt P (elig M tag P auxVal) a.1 ⟨0, by omega⟩
                · by_cases hmem : c ∈ elig M tag P auxVal a.1 ⟨0, by omega⟩
                  · have hmono := HypercubeRamsey.S04.pr_mono actTie
                      (A := fun t => zeroEv ((P, auxVal), t))
                      (B := fun t => p.height (evenSites n) P t.1 (elig M tag P auxVal) p.Rlong a.1 = 0 ∧
                        p.selection (evenSites n) P t.1 (elig M tag P auxVal) t.2 a.1 = some c)
                      (by intro t ht; exact ⟨ht.2.2.1, ht.2.2.2⟩)
                    have htie := HypercubeRamsey.height_selection_tie p hLam P
                      (elig M tag P auxVal) (evenSites n) a.1 c hlegal hmem
                    have hmono' : (p.actLaw.prod p.tieLaw).pr
                        (fun t => zeroEv ((P, auxVal), t)) ≤
                        (p.actLaw.prod p.tieLaw).pr (fun t =>
                          p.height (evenSites n) P t.1 (elig M tag P auxVal) p.Rlong a.1 = 0 ∧
                            p.selection (evenSites n) P t.1 (elig M tag P auxVal) t.2 a.1 = some c) := by
                      simpa [actTie] using hmono
                    exact hmono'.trans htie
                  · have hzero : actTie.pr (fun t => zeroEv ((P, auxVal), t)) = 0 := by
                      unfold FinProb.pr
                      apply Finset.sum_eq_zero
                      intro t ht
                      have hnot : ¬ zeroEv ((P, auxVal), t) := by
                        intro hz
                        exact hmem hz.2.1
                      simp [hnot]
                    rw [hzero]
                    positivity
                · have hzero : actTie.pr (fun t => zeroEv ((P, auxVal), t)) = 0 := by
                    unfold FinProb.pr
                    apply Finset.sum_eq_zero
                    intro t ht
                    have hnot : ¬ zeroEv ((P, auxVal), t) := by
                      intro hz
                      exact hlegal hz.1
                    simp [hnot]
                  rw [hzero]
                  positivity
              exact mul_le_mul_of_nonneg_left hconditional (forced.nonneg x)
        _ = 3 / p.lam := by
              rw [← Finset.sum_mul, forced.sum_eq_one]
              ring
    have hstart : (prepLaw M tag q q').pr ev = (base.prod actTie).pr assocEv := hassoc
    calc
      (prepLaw M tag q q').pr ev = (base.prod actTie).pr assocEv := hstart
      _ ≤ w * (forced.prod actTie).pr zeroEv := hscale
      _ ≤ w * (3 / p.lam) := mul_le_mul_of_nonneg_left hforcedZero hw
      _ = 3 / ((hd β γ n).V : ℝ) := by
        have hLamN : lamH n ≠ 0 := by simpa [p, hd] using hLam.ne'
        dsimp [w, p, hd]
        field_simp [hLamN] <;> ring
      _ = wc β γ n c₃ c := by simp [wc, hc0]
  · let posEv : (Pos β γ n × Aux M tag) × ((p.Loc → Bool) × p.Ties) → Prop :=
      fun z =>
        p.Legal z.1.1 (elig M tag z.1.1 z.1.2)
          (p.domBall (evenSites n) a.1 p.Rlong) ∧
        0 < p.height (evenSites n) z.1.1 z.2.1
          (elig M tag z.1.1 z.1.2) p.Rlong a.1
    have hsub : ∀ z, assocEv z → posEv z := by
      intro z hz
      rcases z with ⟨⟨P, auxVal⟩, ⟨A, τ⟩⟩
      have hEvent : EvLocal M tag (((P, auxVal), A), τ) a c := by
        simpa [assocEv, ev] using hz
      have hsel : p.selection (evenSites n) P A (elig M tag P auxVal) τ a.1 = some c := by
        simpa [sel, p, ppos, paux, pact, pties] using hEvent.sel_eq
      obtain ⟨l, hlval, hmem, _⟩ :=
        HypercubeRamsey.Lane_q_s04_prof.selection_mem_height
          (p := p) (evenSites n) P A (elig M tag P auxVal) τ a.1 c hsel
      have hlegal := hEvent.legal a.1 haDom l
      have hheightpos : 0 < p.height (evenSites n) P A (elig M tag P auxVal) p.Rlong a.1 := by
        have heq := congrArg Fin.val (hlegal.1 c hmem).2.1
        omega
      exact ⟨hEvent.legal, hheightpos⟩
    have hscale : (base.prod actTie).pr assocEv ≤ w * (forced.prod actTie).pr posEv :=
      HypercubeRamsey.Lane_q_s04_prof.pr_prod_scale base forced actTie w hw
        assocEv posEv hsub hweight
    have hforcedPos : (forced.prod actTie).pr posEv ≤ Real.exp (-(n : ℝ) ^ c₃) := by
      have hbound := hheightAt (evenSites n) a.1 ha (some c)
        (πAux := aux) (Esel := fun P auxVal => elig M tag P auxVal)
      have hdrop : (forced.prod actTie).pr posEv =
          ((forced.prod p.actLaw).prod p.tieLaw).pr
            (fun z => posEv (z.1.1, (z.1.2, z.2))) := by
        symm
        exact HypercubeRamsey.Lane_q_s04_prof.pr_prod_assoc forced p.actLaw p.tieLaw
          (fun z => posEv (z.1.1, (z.1.2, z.2)))
      let posTrip : (Pos β γ n × Aux M tag) × (p.Loc → Bool) → Prop := fun z =>
        p.Legal z.1.1 (elig M tag z.1.1 z.1.2)
          (p.domBall (evenSites n) a.1 p.Rlong) ∧
        0 < p.height (evenSites n) z.1.1 z.2 (elig M tag z.1.1 z.1.2) p.Rlong a.1
      have hdropTie : ((forced.prod p.actLaw).prod p.tieLaw).pr
          (fun z => posEv (z.1.1, (z.1.2, z.2))) =
          (forced.prod p.actLaw).pr posTrip := by
        have h := HypercubeRamsey.Lane_q_s04_prof.pr_prod_fst
          (forced.prod p.actLaw) p.tieLaw posTrip
        simpa [posEv, posTrip] using h
      rw [hdrop, hdropTie]
      simpa [posTrip, forced, aux, FinProb.prod, HDParams.domBall] using hbound
    calc
      (prepLaw M tag q q').pr ev = (base.prod actTie).pr assocEv := hassoc
      _ ≤ w * (forced.prod actTie).pr posEv := hscale
      _ ≤ w * Real.exp (-(n : ℝ) ^ c₃) := mul_le_mul_of_nonneg_left hforcedPos hw
      _ = wc β γ n c₃ c := by simp [wc, hc0, w, p, hd]

set_option maxHeartbeats 10000000 in
/-- L4.1h (04:449–496): Lemma 3.3(2) (`simultaneous_profiles`) with players the odd roles `u` (output `E p_u`,
bound `2ν_{i_{g(u)}}`) and the pairs `(c, κ)` (output: the expected even rows of the roles with key `κ` selecting
`c`, bound `2 n_{c,κ} w_c μ_{i_κ}`, `n_{c,κ}` = number of even roles with key `κ` within distance `r` of `c`).  Against
prices `π ≥ 0` the pure mask `{π ≤ 2⟨π, law⟩}` (mass `≥ 1/2` by Markov) answers every profile of the others: odd rows
and even rows are supported in their masks with mass at most one (`EvenRowFacts`), and the even output needs `E`,
of probability at most `w_c` (`SelectBound`); separation (`finite_minimax`) turns price responses into mixed
responses.  Summing, `∑_{c ∈ range a} w_c ≤ 3 + Hλe^{-n^{c₃}} ≤ 4` gives the even bound with `8`. -/
theorem mask_profiles (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) (c₃ : ℝ) (hc₃ : 0 < c₃) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι),
      SelectBound M tag c₃ → EvenRowFacts M tag →
      ∃ (q : XProf M tag) (q' : YProf M tag), ProfOK M tag q q' := by
  classical
  have hparams := hd_admissible hβ hβγ hγ
  have hσ : 0 < sigmaH β γ := hparams.hsz.1
  have hσζ : sigmaH β γ < zetaH β γ := hparams.hsz.2.1
  have hζ : zetaH β γ < 1 := hparams.hsz.2.2.1
  have hpowTendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ c₃)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hc₃).comp tendsto_natCast_atTop_atTop
  have htailTendsto :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ) ^ c₃) ^ (14 / c₃) *
        Real.exp (-((n : ℝ) ^ c₃))) Filter.atTop (nhds 0) :=
    by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (14 / c₃) 1
        (by norm_num)).comp hpowTendsto
      simpa [Function.comp_def, neg_one_mul] using h
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      ((n : ℝ) ^ c₃) ^ (14 / c₃) * Real.exp (-((n : ℝ) ^ c₃)) < 1 / 8 :=
    htailTendsto.eventually
      (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Iio (1 / 8)))
  obtain ⟨nTail₀, hnTail₀⟩ := Filter.eventually_atTop.1 hsmall
  let nTail := max 1 nTail₀
  have hnTail (b : ℕ) (hb : nTail ≤ b) :
      ((b : ℝ) ^ c₃) ^ (14 / c₃) * Real.exp (-((b : ℝ) ^ c₃)) < 1 / 8 :=
    hnTail₀ b (le_trans (le_max_right 1 nTail₀) hb)
  have hnTailBound :
      ∀ n ≥ nTail, (n : ℝ) ^ 14 * Real.exp (-(n : ℝ) ^ c₃) < 1 / 8 := by
    intro n hn
    have hnpos : 0 < n := by
      have h : 1 ≤ n := le_trans (le_max_left 1 nTail₀) hn
      omega
    have hpow : ((n : ℝ) ^ c₃) ^ (14 / c₃) = (n : ℝ) ^ 14 := by
      have hmul : c₃ * (14 / c₃) = 14 := by field_simp [hc₃.ne']
      calc
        ((n : ℝ) ^ c₃) ^ (14 / c₃) = (n : ℝ) ^ (c₃ * (14 / c₃)) :=
          (Real.rpow_mul (by positivity) c₃ (14 / c₃)).symm
        _ = (n : ℝ) ^ (14 : ℝ) := by rw [hmul]
        _ = (n : ℝ) ^ 14 := Real.rpow_natCast _ _
    simpa [hpow] using hnTail n hn
  let n₀ := max 2 nTail
  refine ⟨n₀, ?_⟩
  intro n hn N E G X Y M tag hselect hfacts
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnTail' : nTail ≤ n := le_trans (le_max_right _ _) hn
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hσle1 : sigmaH β γ ≤ 1 := by linarith [hσζ, hζ]
  have hpowσ : (n : ℝ) ^ (sigmaH β γ) ≤ n := by
    calc
      (n : ℝ) ^ (sigmaH β γ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR1 hσle1
      _ = n := by simp
  have hpowT : (n : ℝ) ^ (1 - zetaH β γ) ≤ n := by
    calc
      (n : ℝ) ^ (1 - zetaH β γ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith [hζ])
      _ = n := by simp
  have hceilσ : ⌈(n : ℝ) ^ (sigmaH β γ)⌉₊ ≤ n := by
    have hceilReal : (⌈(n : ℝ) ^ (sigmaH β γ)⌉₊ : ℝ) < (n : ℝ) + 1 := by
      calc
        _ < (n : ℝ) ^ (sigmaH β γ) + 1 := Nat.ceil_lt_add_one (by positivity)
        _ ≤ (n : ℝ) + 1 := by linarith [hpowσ]
    have hceilNat : ⌈(n : ℝ) ^ (sigmaH β γ)⌉₊ < n + 1 := by exact_mod_cast hceilReal
    omega
  have hceilT : ⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊ ≤ n := by
    have hceilReal : (⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊ : ℝ) < (n : ℝ) + 1 := by
      calc
        _ < (n : ℝ) ^ (1 - zetaH β γ) + 1 := Nat.ceil_lt_add_one (by positivity)
        _ ≤ (n : ℝ) + 1 := by linarith [hpowT]
    have hceilNat : ⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊ < n + 1 := by exact_mod_cast hceilReal
    omega
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR1
  have hlogle : Real.log (n : ℝ) ≤ n := Real.log_le_self (by positivity)
  have hlogsq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hceilLog : ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ n ^ 2 := by
    have hceilReal : (⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) < (n : ℝ) ^ 2 + 1 := by
      calc
        _ < Real.log (n : ℝ) ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))
        _ ≤ (n : ℝ) ^ 2 + 1 := by linarith [hlogsq]
    have hceilNat : ⌈Real.log (n : ℝ) ^ 2⌉₊ < n ^ 2 + 1 := by exact_mod_cast hceilReal
    omega
  have hscaleT : HypercubeRamsey.topScale n (sigmaH β γ) (zetaH β γ) ≤
      (max 2 ⌈(n : ℝ) ^ (sigmaH β γ)⌉₊) *
        ⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊ *
          (max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊) :=
    HypercubeRamsey.Lane_q_s04_prof.topScale_le_product n
      (sigmaH β γ) (zetaH β γ) (by
        have hpow : 1 ≤ (n : ℝ) ^ (1 - zetaH β γ) :=
          Real.one_le_rpow hnR1 (by linarith [hζ])
        have hceilReal : (1 : ℝ) ≤ (⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊ : ℝ) :=
          hpow.trans (Nat.le_ceil _)
        exact_mod_cast hceilReal)
  have htop : (topH β γ n : ℝ) ≤ 8 * (n : ℝ) ^ 4 := by
    have hscaleR : (topH β γ n : ℝ) ≤
        (max 2 ⌈(n : ℝ) ^ (sigmaH β γ)⌉₊ : ℝ) *
          (⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊ : ℝ) *
            (max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) := by
      dsimp [topH]
      exact_mod_cast hscaleT
    have hMnat : max 2 ⌈(n : ℝ) ^ (sigmaH β γ)⌉₊ ≤ 2 * n := by
      apply max_le
      · omega
      · exact le_trans hceilσ (by omega)
    have hM : (max 2 ⌈(n : ℝ) ^ (sigmaH β γ)⌉₊ : ℝ) ≤ 2 * n := by exact_mod_cast hMnat
    have hT : (⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊ : ℝ) ≤ 2 * n := by
      have hTnat : ⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊ ≤ 2 * n :=
        le_trans hceilT (by omega)
      exact_mod_cast hTnat
    have hR : (max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
      have hRnat : max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ 2 * n ^ 2 := by
        apply max_le
        · have hnposNat : 0 < n := by omega
          have hpowpos : 0 < n ^ 2 := pow_pos hnposNat _
          have hpowge : 1 ≤ n ^ 2 := by omega
          omega
        · exact le_trans hceilLog (by omega)
      exact_mod_cast hRnat
    calc
      (topH β γ n : ℝ) ≤
          (max 2 ⌈(n : ℝ) ^ (sigmaH β γ)⌉₊ : ℝ) *
            (⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊ : ℝ) *
              (max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) := hscaleR
      _ ≤ (2 * n) * (2 * n) * (2 * (n : ℝ) ^ 2) := by gcongr
      _ = 8 * (n : ℝ) ^ 4 := by ring
  have htailBound :
      (topH β γ n : ℝ) * lamH n * Real.exp (-(n : ℝ) ^ c₃) ≤ 1 := by
    have hlam : lamH n = (n : ℝ) ^ 10 := by simp [lamH]
    have hsmall8 : 8 * (n : ℝ) ^ 14 * Real.exp (-(n : ℝ) ^ c₃) ≤ 1 := by
      have hsmallN := hnTailBound n hnTail'
      nlinarith [hsmallN]
    calc
      (topH β γ n : ℝ) * lamH n * Real.exp (-(n : ℝ) ^ c₃) ≤
          8 * (n : ℝ) ^ 14 * Real.exp (-(n : ℝ) ^ c₃) := by
            rw [hlam]
            calc
              (topH β γ n : ℝ) * (n : ℝ) ^ 10 * Real.exp (-(n : ℝ) ^ c₃) ≤
                  (8 * (n : ℝ) ^ 4) * (n : ℝ) ^ 10 * Real.exp (-(n : ℝ) ^ c₃) := by
                    apply mul_le_mul_of_nonneg_right
                    · exact mul_le_mul_of_nonneg_right htop (by positivity)
                    · positivity
              _ = 8 * (n : ℝ) ^ 14 * Real.exp (-(n : ℝ) ^ c₃) := by ring
      _ ≤ 1 := hsmall8
  have hcenterBound (v : CubeVertex n) :
      ∑ c : Loc β γ n, (if _root_.hammingDist c.1 v ≤ radius β γ n then
        wc β γ n c₃ c else 0) ≤ 4 := by
    rw [HypercubeRamsey.Lane_q_s04_prof.center_weight_sum_eq]
    linarith [htailBound]
  have hkeyNonempty : Nonempty (Key β γ n) := by
    letI : NeZero (gadgetPower β γ n) := ⟨(gadgetPower_pos β γ n).ne'⟩
    exact ⟨fun _ => (0, ∅)⟩
  have hN : 0 < N := by
    by_contra hnot
    have hzero : N = 0 := by omega
    obtain ⟨κ⟩ := hkeyNonempty
    have hsum := (M.μ (tag κ)).sum_eq_one
    simp [hzero] at hsum
  let Players := HypercubeRamsey.Lane_q_s04_prof.ProfilePlayers β γ n
  let Actions : Players → Type := HypercubeRamsey.Lane_q_s04_prof.ProfileActions M tag
  let near : Loc β γ n × Key β γ n → Finset (EvenRole n) := fun ck =>
    Finset.univ.filter fun a =>
      key β γ n a.1 = ck.2 ∧ _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n
  let m : Players → ℕ := fun _ => N
  let b : ∀ j : Players, Fin (m j) → ℝ := fun j x =>
    match j with
    | .inl ck => 2 * ((near ck).card : ℝ) * wc β γ n c₃ ck.1 *
        (N : ℝ) * (M.μ (tag ck.2)).w x
    | .inr u => 2 * (N : ℝ) * (M.ν (tag (key β γ n u.1))).w x
  let eprof := HypercubeRamsey.Lane_q_s04_prof.profileSumEquiv (A := Actions)
  let μplayer : ∀ j : Players, Law N := fun j =>
    match j with
    | .inl ck => M.μ (tag ck.2)
    | .inr u => M.ν (tag (key β γ n u.1))
  let active : ∀ j : Players, Actions j → Finset (Fin N) := fun j s =>
    match j with
    | .inl _ => s.1
    | .inr _ => s.1
  let xout : ∀ j : Players, (∀ i, Actions i) → Fin (m j) → ℝ := fun j σ x =>
    let masks := eprof σ
    match j with
    | .inl ck => (N : ℝ) * ∑ a ∈ near ck,
        (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag masks.1)
          (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag masks.2)).expect
          (fun ω => if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)
    | .inr u => (N : ℝ) *
        (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag masks.1)
          (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag masks.2)).expect
          (fun ω => oddRow M tag ω u x)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  letI : DecidableEq Players := Classical.decEq _
  letI : ∀ j : Players, Nonempty (Actions j) := by
    intro j
    cases j <;> infer_instance
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hresp : ∀ j (q₀ : ∀ i : Players, Actions i → ℝ),
      (∀ i a, 0 ≤ q₀ i a) → (∀ i, ∑ a, q₀ i a = 1) →
      ∃ qj : Actions j → ℝ, (∀ a, 0 ≤ qj a) ∧ ∑ a, qj a = 1 ∧
        ∀ x, ∑ σ : (∀ i, Actions i),
          (∏ i, (Function.update q₀ j qj) i (σ i)) * xout j σ x ≤ b j x := by
    intro j q₀ hq₀ hqsum
    let Q : ∀ i : Players, FinProb (Actions i) := fun i => ⟨q₀ i, hq₀ i, hqsum i⟩
    let Opp := FinProb.pi (fun i : {i // i ≠ j} => Q i.1)
    let pay (s : Actions j) (x : Fin N) : ℝ :=
      Opp.expect (fun τ => xout j
        ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x) - b j x
    have hmin : ∀ ρ : FinProb (Fin N), ∃ s : Actions j, ∑ x, ρ.w x * pay s x ≤ 0 := by
      intro ρ
      have hresponseMask : ∃ s : Actions j, ∀ x ∈ active j s,
          ρ.w x ≤ 2 * ∑ z, (μplayer j).w z * ρ.w z := by
        cases j with
        | inl ck =>
            obtain ⟨s, hlow⟩ := HypercubeRamsey.Lane_q_s04_prof.exists_low_price_mask
              (M.μ (tag ck.2)) ρ.w ρ.nonneg
            exact ⟨s, by simpa [active, μplayer] using hlow⟩
        | inr u =>
            obtain ⟨s, hlow⟩ := HypercubeRamsey.Lane_q_s04_prof.exists_low_price_mask
              (M.ν (tag (key β γ n u.1))) ρ.w ρ.nonneg
            exact ⟨s, by simpa [active, μplayer] using hlow⟩
      obtain ⟨s, hlow⟩ := hresponseMask
      have hprice (τ : ∀ i : {i // i ≠ j}, Actions i.1) :
          ∑ x, ρ.w x * xout j
            ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x ≤
            ∑ x, ρ.w x * b j x := by
        let σ : ∀ i : Players, Actions i :=
          (HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)
        let masks := eprof σ
        have hjs : σ j = s := by
          simp [σ, HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv]
        cases j with
        | inr u =>
            have hmask : masks.2 u = s := by
              change σ (.inr u) = s
              simpa [HypercubeRamsey.Lane_q_s04_prof.ProfilePlayers, eprof, masks] using hjs
            have hlow' : ∀ y ∈ (masks.2 u).1,
                ρ.w y ≤ 2 * ∑ z, (M.ν (tag (key β γ n u.1))).w z * ρ.w z := by
              intro y hy
              exact hlow y (by simpa [active, hmask] using hy)
            have hrow := HypercubeRamsey.Lane_q_s04_prof.odd_price_pure_le
              M tag masks.1 masks.2 u ρ.w ρ.nonneg hlow'
            have htarget : ∑ y, ρ.w y * b (.inr u) y =
                (N : ℝ) * (2 * ∑ z, (M.ν (tag (key β γ n u.1))).w z * ρ.w z) := by
              calc
                ∑ y, ρ.w y * b (.inr u) y =
                    ∑ y, (N : ℝ) *
                      (2 * ((M.ν (tag (key β γ n u.1))).w y * ρ.w y)) := by
                        apply Finset.sum_congr rfl
                        intro y hy
                        simp [b]
                        ring
                _ = (N : ℝ) *
                      (2 * ∑ y, (M.ν (tag (key β γ n u.1))).w y * ρ.w y) := by
                        calc
                          _ = (N : ℝ) * ∑ y, 2 *
                              ((M.ν (tag (key β γ n u.1))).w y * ρ.w y) := by
                                rw [Finset.mul_sum]
                          _ = (N : ℝ) *
                              (2 * ∑ y, (M.ν (tag (key β γ n u.1))).w y * ρ.w y) := by
                                congr 1
                                rw [← Finset.mul_sum]
            calc
              ∑ y, ρ.w y * xout (.inr u) σ y =
                  (N : ℝ) * ∑ y, ρ.w y *
                    (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag masks.1)
                      (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag masks.2)).expect
                      (fun ω => oddRow M tag ω u y) := by
                    simp [xout, masks, σ, eprof]
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
              _ ≤ (N : ℝ) *
                    (2 * ∑ z, (M.ν (tag (key β γ n u.1))).w z * ρ.w z) :=
                    mul_le_mul_of_nonneg_left hrow hNpos.le
              _ = ∑ y, ρ.w y * b (.inr u) y := htarget.symm
        | inl ck =>
            have hmask : masks.1 ck = s := by
              change σ (.inl ck) = s
              simpa [HypercubeRamsey.Lane_q_s04_prof.ProfilePlayers, eprof, masks] using hjs
            have hlow' : ∀ x ∈ (masks.1 ck).1,
                ρ.w x ≤ 2 * ∑ z, (M.μ (tag ck.2)).w z * ρ.w z := by
              intro x hx
              exact hlow x (by simpa [active, hmask] using hx)
            have hrole (a : EvenRole n) (ha : a ∈ near ck) :
                ∑ x, ρ.w x *
                  (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag masks.1)
                    (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag masks.2)).expect (fun ω =>
                      if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0) ≤
                  2 * (∑ z, (M.μ (tag ck.2)).w z * ρ.w z) * wc β γ n c₃ ck.1 := by
              rcases Finset.mem_filter.mp ha with ⟨_, hnearKey⟩
              exact HypercubeRamsey.Lane_q_s04_prof.even_price_pure_le
                M tag c₃ hselect hfacts masks.1 masks.2 ck a hnearKey.1 hnearKey.2
                ρ.w ρ.nonneg hlow'
            have htarget : ∑ x, ρ.w x * b (.inl ck) x =
                (N : ℝ) * ((near ck).card : ℝ) *
                  (2 * wc β γ n c₃ ck.1) *
                    (∑ z, (M.μ (tag ck.2)).w z * ρ.w z) := by
              let C : ℝ := (N : ℝ) * ((near ck).card : ℝ) *
                (2 * wc β γ n c₃ ck.1)
              calc
                ∑ x, ρ.w x * b (.inl ck) x =
                    ∑ x, C * ((M.μ (tag ck.2)).w x * ρ.w x) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      simp [b, C]
                      ring
                _ = C * ∑ x, (M.μ (tag ck.2)).w x * ρ.w x := by
                      rw [Finset.mul_sum]
                _ = (N : ℝ) * ((near ck).card : ℝ) *
                    (2 * wc β γ n c₃ ck.1) *
                      (∑ z, (M.μ (tag ck.2)).w z * ρ.w z) := by simp [C]
            let F (a : EvenRole n) (x : Fin N) :=
              (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag masks.1)
                (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag masks.2)).expect (fun ω =>
                  if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)
            have hxout (x : Fin N) :
                xout (.inl ck) σ x = (N : ℝ) * ∑ a ∈ near ck, F a x := by
              simp [xout, F, masks, σ, eprof]
            have hmove :
                ∑ x, ρ.w x * ∑ a ∈ near ck, F a x =
                  ∑ a ∈ near ck, ∑ x, ρ.w x * F a x := by
              calc
                _ = ∑ x, ∑ a ∈ near ck, ρ.w x * F a x := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      rw [Finset.mul_sum]
                _ = _ := by rw [Finset.sum_comm]
            have hinter :
                ∑ x, ρ.w x * xout (.inl ck) σ x =
                  (N : ℝ) * ∑ a ∈ near ck, ∑ x, ρ.w x * F a x := by
              calc
                _ = ∑ x, (N : ℝ) * (ρ.w x * ∑ a ∈ near ck, F a x) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      rw [hxout x]
                      ring
                _ = (N : ℝ) * ∑ x, ρ.w x * ∑ a ∈ near ck, F a x := by
                      rw [Finset.mul_sum]
                _ = _ := congrArg (fun z : ℝ => (N : ℝ) * z) hmove
            calc
              ∑ x, ρ.w x * xout (.inl ck) σ x =
                  (N : ℝ) * ∑ a ∈ near ck, ∑ x, ρ.w x *
                  (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag masks.1)
                    (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag masks.2)).expect (fun ω =>
                        if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0) := hinter
              _ ≤ (N : ℝ) * ∑ a ∈ near ck,
                    2 * (∑ z, (M.μ (tag ck.2)).w z * ρ.w z) * wc β γ n c₃ ck.1 := by
                    apply mul_le_mul_of_nonneg_left _ hNpos.le
                    apply Finset.sum_le_sum
                    intro a ha
                    exact hrole a ha
              _ = ∑ x, ρ.w x * b (.inl ck) x := by
                    rw [Finset.sum_const, nsmul_eq_mul]
                    calc
                      _ = (N : ℝ) * ((near ck).card : ℝ) *
                            (∑ z, (M.μ (tag ck.2)).w z * ρ.w z) *
                            wc β γ n c₃ ck.1 * 2 := by ring
                      _ = (N : ℝ) * ((near ck).card : ℝ) *
                            (2 * wc β γ n c₃ ck.1) *
                            (∑ z, (M.μ (tag ck.2)).w z * ρ.w z) := by ring
                      _ = _ := htarget.symm
      have hmix :
          ∑ x, ρ.w x * (Opp.expect
              (fun τ => xout j
                ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x)) ≤
            ∑ x, ρ.w x * b j x := by
        calc
          _ = Opp.expect (fun τ => ∑ x,
              ρ.w x * xout j
                ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x) := by
                symm
                exact HypercubeRamsey.Lane_q_s04_prof.expect_weighted_sum Opp ρ.w
                  (fun x τ => xout j
                    ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x)
          _ ≤ Opp.expect (fun _ => ∑ x, ρ.w x * b j x) :=
                FinProb.expect_mono Opp (fun τ => hprice τ)
          _ = ∑ x, ρ.w x * b j x := FinProb.expect_const Opp _
      have hmi : ∑ x, ρ.w x * pay s x ≤ 0 := by
        calc
          _ = ∑ x, ρ.w x * (Opp.expect (fun τ => xout j
                ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x) - b j x) := rfl
          _ = (∑ x, ρ.w x * Opp.expect (fun τ => xout j
                ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x)) -
                ∑ x, ρ.w x * b j x := by
              calc
                _ = ∑ x, (ρ.w x * Opp.expect (fun τ => xout j
                      ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x) -
                        ρ.w x * b j x) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring
                _ = _ := by rw [Finset.sum_sub_distrib]
          _ ≤ 0 := by linarith [hmix]
      exact ⟨s, hmi⟩
    obtain ⟨T, hT⟩ := HypercubeRamsey.finite_minimax pay hmin
    refine ⟨T.w, T.nonneg, T.sum_eq_one, ?_⟩
    intro x
    let Q : ∀ i : Players, FinProb (Actions i) := fun i =>
      ⟨q₀ i, hq₀ i, hqsum i⟩
    have hpi :
        ∑ σ : (∀ i, Actions i),
            (∏ i, (Function.update q₀ j T.w) i (σ i)) * xout j σ x =
          (FinProb.pi (Function.update Q j T)).expect (fun σ => xout j σ x) := by
      simp only [FinProb.expect, FinProb.pi]
      apply Finset.sum_congr rfl
      intro σ hσ
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hij : i = j
      · subst i
        simp [Q]
      · simp [Q, Function.update, hij]
    rw [hpi, HypercubeRamsey.Lane_q_s04_prof.pi_expect_update_split_dep]
    have hbSum : ∑ s, T.w s * b j x = b j x := by
      calc
        ∑ s, T.w s * b j x = (∑ s, T.w s) * b j x := by
          rw [Finset.sum_mul]
        _ = b j x := by rw [T.sum_eq_one]; ring
    have hminx : ∑ s, T.w s * (Opp.expect (fun τ =>
        xout j ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x) -
          b j x) ≤ 0 := by
      simpa [pay] using hT x
    have hsumPay :
        ∑ s, T.w s * (Opp.expect (fun τ =>
          xout j ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x) -
            b j x) =
          (∑ s, T.w s * Opp.expect (fun τ =>
            xout j ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x)) -
            b j x := by
      calc
        _ = ∑ s, (T.w s * Opp.expect (fun τ =>
              xout j ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x) -
                T.w s * b j x) := by
              apply Finset.sum_congr rfl
              intro s hs
              ring
        _ = _ - ∑ s, T.w s * b j x := by rw [Finset.sum_sub_distrib]
        _ = _ - b j x := by rw [hbSum]
    have hpay : ∑ s, T.w s *
        Opp.expect (fun τ =>
          xout j ((HypercubeRamsey.Lane_q_s04_prof.profileSplitEquiv j).symm (s, τ)) x) ≤
          b j x := by
      rw [hsumPay] at hminx
      linarith
    simpa [pay] using hpay
  obtain ⟨qmix, hq0, hqsum, hqout⟩ :=
    HypercubeRamsey.simultaneous_profiles xout b hresp
  let Qfinal : ∀ j : Players, FinProb (Actions j) := fun j =>
    ⟨qmix j, hq0 j, hqsum j⟩
  let q : XProf M tag := fun ck => Qfinal (.inl ck)
  let q' : YProf M tag := fun u => Qfinal (.inr u)
  have hplayerOut (j : Players) (x : Fin N) :
      (FinProb.pi Qfinal).expect (fun σ => xout j σ x) ≤ b j x := by
    have h := hqout j x
    simpa [FinProb.expect, FinProb.pi, Qfinal] using h
  have hprepPi (f : Prep M tag → ℝ) :
      (prepLaw M tag q q').expect f =
        (FinProb.pi Qfinal).expect (fun σ =>
          let masks := eprof σ
          (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag masks.1)
            (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag masks.2)).expect f) := by
    rw [HypercubeRamsey.Lane_q_s04_prof.prepLaw_expect_profile_average]
    let pure (s : XMasks M tag × YMasks M tag) :=
      (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag s.1)
        (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag s.2)).expect f
    have hpi := HypercubeRamsey.Lane_q_s04_prof.pi_profile_mask_expect M tag Qfinal pure
    calc
      (∑ s : XMasks M tag × YMasks M tag,
          (HypercubeRamsey.Lane_q_s04_prof.maskProfileLaw M tag q q').w s * pure s) =
          (HypercubeRamsey.Lane_q_s04_prof.maskProfileLaw M tag q q').expect pure := rfl
      _ = (HypercubeRamsey.Lane_q_s04_prof.maskProfileLaw M tag
            (fun ck => Qfinal (.inl ck)) (fun u => Qfinal (.inr u))).expect pure := rfl
      _ = (FinProb.pi Qfinal).expect (fun σ => pure (eprof σ)) := hpi.symm
  have hoddEq (u : OddRole n) (y : Fin N) :
      (FinProb.pi Qfinal).expect (fun σ => xout (.inr u) σ y) =
        (N : ℝ) * rawOdd M tag q q' u y := by
    let pureOdd (σ : ∀ i, Actions i) :=
      (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag (eprof σ).1)
        (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag (eprof σ).2)).expect
          (fun ω => oddRow M tag ω u y)
    have hx : (FinProb.pi Qfinal).expect (fun σ => xout (.inr u) σ y) =
        (N : ℝ) * (FinProb.pi Qfinal).expect pureOdd := by
      calc
        _ = (FinProb.pi Qfinal).expect (fun σ => (N : ℝ) * pureOdd σ) := by
              apply congrArg
              funext σ
              simp [xout, pureOdd, eprof]
        _ = (N : ℝ) * (FinProb.pi Qfinal).expect pureOdd :=
              FinProb.expect_smul _ _ _
    calc
      _ = (N : ℝ) * (FinProb.pi Qfinal).expect pureOdd := hx
      _ = (N : ℝ) * (prepLaw M tag q q').expect (fun ω => oddRow M tag ω u y) := by
            rw [(hprepPi (fun ω => oddRow M tag ω u y)).symm]
      _ = (N : ℝ) * rawOdd M tag q q' u y := rfl
  have hoddBound (u : OddRole n) (y : Fin N) :
      rawOdd M tag q q' u y ≤ 2 * (M.ν (tag (key β γ n u.1))).w y := by
    have h := hplayerOut (.inr u) y
    rw [hoddEq] at h
    change (N : ℝ) * rawOdd M tag q q' u y ≤
      2 * (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y at h
    nlinarith [hNpos]
  have hcenterExpected (ck : Loc β γ n × Key β γ n) (x : Fin N) :
      (FinProb.pi Qfinal).expect (fun σ => xout (.inl ck) σ x) =
        (N : ℝ) * ∑ a ∈ near ck,
          (prepLaw M tag q q').expect (fun ω =>
            if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0) := by
    let pure (a : EvenRole n) (σ : ∀ i, Actions i) :=
      (prepLaw M tag (HypercubeRamsey.Lane_q_s04_prof.pointXProf M tag (eprof σ).1)
        (HypercubeRamsey.Lane_q_s04_prof.pointYProf M tag (eprof σ).2)).expect (fun ω =>
          if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)
    have hxout (σ : ∀ i, Actions i) :
        xout (.inl ck) σ x = (N : ℝ) * ∑ a ∈ near ck, pure a σ := by
      simp [xout, pure, eprof]
    have hsum :
        (FinProb.pi Qfinal).expect (fun σ => ∑ a ∈ near ck, pure a σ) =
          ∑ a ∈ near ck, (FinProb.pi Qfinal).expect (pure a) := by
      let weight : EvenRole n → ℝ := fun a => if a ∈ near ck then 1 else 0
      have h := HypercubeRamsey.Lane_q_s04_prof.expect_weighted_sum
        (FinProb.pi Qfinal) weight pure
      simpa [weight, Finset.sum_filter] using h
    calc
      (FinProb.pi Qfinal).expect (fun σ => xout (.inl ck) σ x) =
          (FinProb.pi Qfinal).expect (fun σ => (N : ℝ) * ∑ a ∈ near ck, pure a σ) := by
            apply congrArg
            funext σ
            exact hxout σ
      _ = (N : ℝ) * (FinProb.pi Qfinal).expect
            (fun σ => ∑ a ∈ near ck, pure a σ) := FinProb.expect_smul _ _ _
      _ = (N : ℝ) * ∑ a ∈ near ck, (FinProb.pi Qfinal).expect (pure a) := by rw [hsum]
      _ = (N : ℝ) * ∑ a ∈ near ck,
            (prepLaw M tag q q').expect (fun ω =>
              if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0) := by
            congr 1
            apply Finset.sum_congr rfl
            intro a ha
            exact (hprepPi (fun ω =>
              if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)).symm
  have hsumRaw (x : Fin N) :
      (N : ℝ) * ∑ a : EvenRole n, rawEven M tag q q' a x =
        ∑ ck : Loc β γ n × Key β γ n,
          (FinProb.pi Qfinal).expect (fun σ => xout (.inl ck) σ x) := by
    let contrib (ck : Loc β γ n × Key β γ n) (a : EvenRole n) :=
      (prepLaw M tag q q').expect (fun ω =>
        if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)
    have hreorder :
        (∑ a : EvenRole n, ∑ ck : Loc β γ n × Key β γ n,
          if a ∈ near ck then contrib ck a else 0) =
        ∑ ck : Loc β γ n × Key β γ n, ∑ a ∈ near ck, contrib ck a := by
      rw [Finset.sum_comm]
      simp [Finset.sum_filter]
    calc
      (N : ℝ) * ∑ a : EvenRole n, rawEven M tag q q' a x =
          (N : ℝ) * ∑ a : EvenRole n, ∑ ck : Loc β γ n × Key β γ n,
            if a ∈ near ck then contrib ck a else 0 := by
              apply congrArg (fun z : ℝ => (N : ℝ) * z)
              apply Finset.sum_congr rfl
              intro a ha
              simpa [near, contrib] using
                (HypercubeRamsey.Lane_q_s04_prof.rawEven_center_decomp M tag q q' a x).symm
      _ = (N : ℝ) * ∑ ck : Loc β γ n × Key β γ n, ∑ a ∈ near ck, contrib ck a := by
            rw [hreorder]
      _ = ∑ ck : Loc β γ n × Key β γ n,
            (FinProb.pi Qfinal).expect (fun σ => xout (.inl ck) σ x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ck hck
            exact (hcenterExpected ck x).symm
  have hcellSum (x : Fin N) :
      ∑ ck : Loc β γ n × Key β γ n,
          (FinProb.pi Qfinal).expect (fun σ => xout (.inl ck) σ x) ≤
        ∑ ck, b (.inl ck) x := by
    apply Finset.sum_le_sum
    intro ck hck
    exact hplayerOut (.inl ck) x
  have hbudget (x : Fin N) := HypercubeRamsey.Lane_q_s04_prof.center_weight_budget_le
    M tag c₃ x hcenterBound
  have hbSum (x : Fin N) :
      ∑ ck : Loc β γ n × Key β γ n, b (.inl ck) x ≤
        8 * (N : ℝ) * ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x := by
    have hbeq :
        (∑ ck : Loc β γ n × Key β γ n, b (.inl ck) x) =
          2 * (N : ℝ) * ∑ ck : Loc β γ n × Key β γ n,
            ((near ck).card : ℝ) * wc β γ n c₃ ck.1 * (M.μ (tag ck.2)).w x := by
      simp [b]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ck hck
      ring
    rw [hbeq]
    have hcoef : 0 ≤ 2 * (N : ℝ) := by positivity
    calc
      2 * (N : ℝ) * ∑ ck : Loc β γ n × Key β γ n,
          ((near ck).card : ℝ) * wc β γ n c₃ ck.1 * (M.μ (tag ck.2)).w x ≤
          2 * (N : ℝ) * (4 * ∑ a : EvenRole n,
            (M.μ (tag (key β γ n a.1))).w x) :=
            mul_le_mul_of_nonneg_left (hbudget x) hcoef
      _ = 8 * (N : ℝ) * ∑ a : EvenRole n,
            (M.μ (tag (key β γ n a.1))).w x := by ring
  have hevenBound (x : Fin N) :
      ∑ a : EvenRole n, rawEven M tag q q' a x ≤
        8 * ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x := by
    have h := hsumRaw x
    have h' : (N : ℝ) * ∑ a : EvenRole n, rawEven M tag q q' a x ≤
        8 * (N : ℝ) * ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x :=
      h.le.trans ((hcellSum x).trans (hbSum x))
    nlinarith [hNpos, h']
  refine ⟨q, q', ?_⟩
  refine ⟨?_, ?_⟩
  · intro u y
    exact hoddBound u y
  · intro x
    exact hevenBound x

end HypercubeRamsey.S04
