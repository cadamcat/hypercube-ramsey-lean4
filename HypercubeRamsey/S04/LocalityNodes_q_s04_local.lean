import HypercubeRamsey.S04.CoreLemmas

namespace HypercubeRamsey.S04.Lane_q_s04_local

open Classical OAI.HypercubeRamsey

variable {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop}
variable {X Y : Finset (Fin N)}
variable (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)

private theorem ball_mem {v w : CubeVertex n} {R : ℕ}
    (h : _root_.hammingDist v w ≤ R) : w ∈ ballV v R := by
  simp [ballV, h]

private theorem agree_pos {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (c : Loc β γ n)
    (hc : _root_.hammingDist c.1 v ≤ R) : ppos ω c = ppos ω' c :=
  (h.1 c (ball_mem (by simpa [_root_.hammingDist_comm] using hc))).1

private theorem agree_act {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (c : Loc β γ n)
    (hc : _root_.hammingDist c.1 v ≤ R) : pact ω c = pact ω' c :=
  (h.1 c (ball_mem (by simpa [_root_.hammingDist_comm] using hc))).2.1

private theorem agree_tie {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (c : Loc β γ n)
    (hc : _root_.hammingDist c.1 v ≤ R) : pties ω c = pties ω' c :=
  (h.1 c (ball_mem (by simpa [_root_.hammingDist_comm] using hc))).2.2

private theorem agree_mask {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (ck : Loc β γ n × Key β γ n)
    (hc : _root_.hammingDist ck.1.1 v ≤ R) :
    axm (paux ω) ck = axm (paux ω') ck :=
  (h.2.1 ck (ball_mem (by simpa [_root_.hammingDist_comm] using hc))).1

private theorem agree_tuple {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (ck : Loc β γ n × Key β γ n)
    (hc : _root_.hammingDist ck.1.1 v ≤ R) :
    aW (paux ω) ck = aW (paux ω') ck :=
  (h.2.1 ck (ball_mem (by simpa [_root_.hammingDist_comm] using hc))).2

private theorem agree_ymask {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (u : OddRole n)
    (hu : u.1 ∈ ballV v R) : aym (paux ω) u = aym (paux ω') u :=
  h.2.2 u hu

private theorem oddAdj_dist {u : OddRole n} {v : CubeVertex n}
    (hv : v ∈ oddAdj u) : _root_.hammingDist u.1 v = 1 := by
  exact (Finset.mem_filter.mp hv).2

private theorem pool_distance {u : OddRole n} {v : CubeVertex n}
    (hv : v ∈ oddAdj u) {c : Loc β γ n} {P : Pos β γ n}
    {j : Fin (topH β γ n)} (hc : c ∈ pool P u j) :
    _root_.hammingDist c.1 v ≤ radius β γ n + 2 := by
  rcases (Finset.mem_filter.mp hc).2.2.2 with ⟨w, hw, hcw⟩
  have huw : _root_.hammingDist u.1 w = 1 := oddAdj_dist hw
  have hvu : _root_.hammingDist v u.1 = 1 := by
    simpa [_root_.hammingDist_comm] using oddAdj_dist hv
  have huv : _root_.hammingDist u.1 v = 1 := oddAdj_dist hv
  have hwu : _root_.hammingDist w u.1 = 1 := by
    simpa [_root_.hammingDist_comm] using huw
  have hcu : _root_.hammingDist c.1 u.1 ≤ radius β γ n + 1 := by
    calc
      _ ≤ _root_.hammingDist c.1 w + _root_.hammingDist w u.1 :=
        _root_.hammingDist_triangle c.1 w u.1
      _ ≤ radius β γ n + 1 := by omega
  calc
    _ ≤ _root_.hammingDist c.1 u.1 + _root_.hammingDist u.1 v :=
      _root_.hammingDist_triangle c.1 u.1 v
    _ ≤ radius β γ n + 1 + 1 := by omega
    _ = radius β γ n + 2 := by omega

private theorem pool_eq {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (u : OddRole n) (j : Fin (topH β γ n))
    (hv : v ∈ oddAdj u) (hR : radius β γ n + 2 ≤ R) :
    pool (ppos ω) u j = pool (ppos ω') u j := by
  classical
  apply Finset.ext
  intro c
  simp only [pool, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hpos, hlevel, hnear⟩
    have hc : c ∈ pool (ppos ω) u j := by
      simp [pool, hpos, hlevel, hnear]
    have hdist := pool_distance hv hc
    refine ⟨?_, hlevel, hnear⟩
    rw [← agree_pos M tag h c (by omega)]
    exact hpos
  · rintro ⟨hpos, hlevel, hnear⟩
    have hc : c ∈ pool (ppos ω') u j := by
      simp [pool, hpos, hlevel, hnear]
    have hdist := pool_distance hv hc
    refine ⟨?_, hlevel, hnear⟩
    rw [agree_pos M tag h c (by omega)]
    exact hpos

private theorem valid_iff_of_agree {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (u : OddRole n) (D : Finset (Loc β γ n))
    (hu : u.1 ∈ ballV v R) (hD : ∀ c ∈ D, _root_.hammingDist c.1 v ≤ R) :
    Valid M tag u (paux ω) D ↔ Valid M tag u (paux ω') D := by
  classical
  let Z := Zset β γ u
  have hy : aym (paux ω) u = aym (paux ω') u := agree_ymask M tag h u hu
  have hW : ∀ c ∈ D, ∀ κ, aW (paux ω) (c, κ) = aW (paux ω') (c, κ) := by
    intro c hc κ
    exact agree_tuple M tag h (c, κ) (hD c hc)
  have hall (y : Fin N) :
      HitsAll E G (aW (paux ω)) D Z y ↔ HitsAll E G (aW (paux ω')) D Z y := by
    constructor
    · intro hh c hc κ hκ j
      rw [← hW c hc κ]
      exact hh c hc κ hκ j
    · intro hh c hc κ hκ j
      rw [hW c hc κ]
      exact hh c hc κ hκ j
  have hbut (c₀ : Loc β γ n) (κ₀ : Key β γ n) (y : Fin N) :
      HitsBut E G (aW (paux ω)) D Z c₀ κ₀ y ↔
        HitsBut E G (aW (paux ω')) D Z c₀ κ₀ y := by
    constructor
    · intro hh c hc κ hκ hne j
      rw [← hW c hc κ]
      exact hh c hc κ hκ hne j
    · intro hh c hc κ hκ hne j
      rw [hW c hc κ]
      exact hh c hc κ hκ hne j
  have hprAll :
      (maskLaw (aym (paux ω) u)).pr (HitsAll E G (aW (paux ω)) D Z) =
        (maskLaw (aym (paux ω') u)).pr (HitsAll E G (aW (paux ω')) D Z) := by
    rw [hy]
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy' : HitsAll E G (aW (paux ω)) D Z y
    · have hy'' := (hall y).mp hy'
      simp [hy', hy'']
    · have hy'' : ¬ HitsAll E G (aW (paux ω')) D Z y := fun h' => hy' ((hall y).mpr h')
      simp [hy', hy'']
  have hprBut (c₀ : Loc β γ n) (hc₀ : c₀ ∈ D) (κ₀ : Key β γ n) (hκ : κ₀ ∈ Z) :
      (maskLaw (aym (paux ω) u)).pr
        (HitsBut E G (aW (paux ω)) D Z c₀ κ₀) =
      (maskLaw (aym (paux ω') u)).pr
        (HitsBut E G (aW (paux ω')) D Z c₀ κ₀) := by
    rw [hy]
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy' : HitsBut E G (aW (paux ω)) D Z c₀ κ₀ y
    · have hy'' := (hbut c₀ κ₀ y).mp hy'
      simp [hy', hy'']
    · have hy'' : ¬ HitsBut E G (aW (paux ω')) D Z c₀ κ₀ y :=
        fun h' => hy' ((hbut c₀ κ₀ y).mpr h')
      simp [hy', hy'']
  have hprAll' :
      (maskLaw (aym (paux ω) u)).pr (HitsAll E G (aW (paux ω)) D (Zset β γ u)) =
        (maskLaw (aym (paux ω') u)).pr (HitsAll E G (aW (paux ω')) D (Zset β γ u)) := by
    simpa [Z] using hprAll
  have hprBut' (c₀ : Loc β γ n) (hc₀ : c₀ ∈ D) (κ₀ : Key β γ n)
      (hκ : κ₀ ∈ Zset β γ u) :
      (maskLaw (aym (paux ω) u)).pr
        (HitsBut E G (aW (paux ω)) D (Zset β γ u) c₀ κ₀) =
      (maskLaw (aym (paux ω') u)).pr
        (HitsBut E G (aW (paux ω')) D (Zset β γ u) c₀ κ₀) := by
    simpa [Z] using hprBut c₀ hc₀ κ₀ hκ
  constructor
  · intro hV
    refine ⟨hV.card_pos, hV.card_le, ?_, ?_⟩
    · rw [← hprAll']
      exact hV.mass
    · intro c hc κ hκ
      rw [← hprAll', ← hprBut' c hc κ hκ]
      exact hV.ratio c hc κ hκ
  · intro hV
    refine ⟨hV.card_pos, hV.card_le, ?_, ?_⟩
    · rw [hprAll']
      exact hV.mass
    · intro c hc κ hκ
      rw [hprAll', hprBut' c hc κ hκ]
      exact hV.ratio c hc κ hκ

private theorem marked_eq {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (u : OddRole n) (j : Fin (topH β γ n))
    (hv : v ∈ oddAdj u) (hR : radius β γ n + 2 ≤ R) :
    marked M tag (ppos ω) (paux ω) u j = marked M tag (ppos ω') (paux ω') u j := by
  classical
  have hp := pool_eq M tag h u j hv hR
  have hcands : cands (ppos ω) u j = cands (ppos ω') u j := by
    simp [cands, hp]
  have hfilter :
      (cands (ppos ω) u j).filter (fun D => ¬ Valid M tag u (paux ω) D) =
      (cands (ppos ω') u j).filter (fun D => ¬ Valid M tag u (paux ω') D) := by
    ext D
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hD, hbad⟩
      refine ⟨?_, ?_⟩
      · simpa [hcands] using hD
      · intro hgood
        apply hbad
        apply (valid_iff_of_agree M tag h u D (by
          have hdist : _root_.hammingDist v u.1 = 1 := by
            simpa [_root_.hammingDist_comm] using oddAdj_dist hv
          apply ball_mem
          omega) (by
            intro c hc
            have hcand : D ∈ cands (ppos ω) u j := by
              simpa [hcands] using hD
            have hpow := (Finset.mem_filter.mp hcand).1
            have hpool : c ∈ pool (ppos ω) u j :=
              (Finset.mem_powerset.mp hpow) hc
            have hd := pool_distance hv hpool
            omega)).mpr hgood
    · rintro ⟨hD, hbad⟩
      refine ⟨?_, ?_⟩
      · simpa [hcands] using hD
      · intro hgood
        apply hbad
        apply (valid_iff_of_agree M tag h u D (by
          have hdist : _root_.hammingDist v u.1 = 1 := by
            simpa [_root_.hammingDist_comm] using oddAdj_dist hv
          apply ball_mem
          omega) (by
            intro c hc
            have hcand : D ∈ cands (ppos ω') u j := by
              simpa [hcands] using hD
            have hpow := (Finset.mem_filter.mp hcand).1
            have hpool : c ∈ pool (ppos ω') u j :=
              (Finset.mem_powerset.mp hpow) hc
            have hd := pool_distance hv hpool
            omega)).mp hgood
  unfold marked
  rw [hfilter]

private theorem forbidden_eq {v : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV v R) ω ω') (hR : radius β γ n + 2 ≤ R) (l : Fin (topH β γ n + 1)) :
    forbidden M tag (ppos ω) (paux ω) v l = forbidden M tag (ppos ω') (paux ω') v l := by
  classical
  apply Finset.ext
  intro c
  simp only [forbidden, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlevel, u, hv, j, D, hD, hcD⟩
    refine ⟨hlevel, u, hv, j, D, ?_, hcD⟩
    rw [← marked_eq M tag h u j hv hR]
    exact hD
  · rintro ⟨hlevel, u, hv, j, D, hD, hcD⟩
    refine ⟨hlevel, u, hv, j, D, ?_, hcD⟩
    rw [marked_eq M tag h u j hv hR]
    exact hD

theorem elig_local_proof (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) :
    EligLocal M tag := by
  classical
  intro v l ω ω' h
  have hforb : forbidden M tag (ppos ω) (paux ω) v l =
      forbidden M tag (ppos ω') (paux ω') v l := by
    exact forbidden_eq M tag h (le_rfl) l
  apply Finset.ext
  intro c
  simp only [elig, Finset.mem_sdiff]
  rw [hforb]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hp, hl, hd⟩, hnot⟩
    refine ⟨⟨?_, hl, hd⟩, hnot⟩
    rw [← agree_pos M tag h c (by omega)]
    exact hp
  · rintro ⟨⟨hp, hl, hd⟩, hnot⟩
    refine ⟨⟨?_, hl, hd⟩, hnot⟩
    rw [agree_pos M tag h c (by omega)]
    exact hp

private theorem agreeOn_mono {S T : Finset (CubeVertex n)} {ω ω' : Prep M tag}
    (hTS : T ⊆ S) (h : AgreeOn M tag S ω ω') : AgreeOn M tag T ω ω' := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    exact h.1 c (hTS hc)
  · intro ck hc
    exact h.2.1 ck (hTS hc)
  · intro u hu
    exact h.2.2 u (hTS hu)

private theorem ball_subset {q x : CubeVertex n} {R S : ℕ}
    (hx : _root_.hammingDist q x ≤ R) :
    ballV x S ⊆ ballV q (R + S) := by
  intro z hz
  have hzx : _root_.hammingDist x z ≤ S := (Finset.mem_filter.mp hz).2
  have hqz := _root_.hammingDist_triangle q x z
  have hqx : _root_.hammingDist q x ≤ R := hx
  exact ball_mem (by
    calc
      _ ≤ _root_.hammingDist q x + _root_.hammingDist x z := hqz
      _ ≤ R + S := Nat.add_le_add hqx hzx)

private theorem reach_within {Sites : Finset (CubeVertex n)} {P A : Pos β γ n}
    {F : (hd β γ n).EligMap} {q x : CubeVertex n} {R j : ℕ}
    (hreach : (hd β γ n).Reach Sites P A F q R x j) :
    _root_.hammingDist x q ≤ R := by
  refine HDParams.Reach.rec
    (motive := fun v _ _ => _root_.hammingDist v q ≤ R) ?_ ?_ ?_ hreach
  · intro v hv hdist
    exact hdist
  · intro v j hj hprev hbad ih
    exact ih
  · intro v v' j hprev hv' hdist hstep ih
    exact hdist

private theorem bad_iff_of_agree {q x : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (he : EligLocal M tag)
    (h : AgreeOn M tag (ballV q (R + radius β γ n + 2)) ω ω')
    (hx : _root_.hammingDist x q ≤ R) (j : Fin (topH β γ n + 1)) :
    (hd β γ n).Bad (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) x j ↔
      (hd β γ n).Bad (ppos ω') (pact ω') (elig M tag (ppos ω') (paux ω')) x j := by
  classical
  have hx' : _root_.hammingDist q x ≤ R := by
    simpa [_root_.hammingDist_comm] using hx
  have hsmall : AgreeOn M tag (ballV x (radius β γ n + 2)) ω ω' :=
    agreeOn_mono M tag (ball_subset (q := q) (x := x) (R := R)
      (S := radius β γ n + 2) hx') h
  have hE := he x j ω ω' hsmall
  have hD : (hd β γ n).r + (hd β γ n).D = radius β γ n + 2 := rfl
  have hcounts :
      (Finset.univ.filter (fun z : CubeVertex n =>
        ppos ω (z, j) = true ∧ pact ω (z, j) = true ∧
          _root_.hammingDist z x ≤ (hd β γ n).r + (hd β γ n).D)) =
      (Finset.univ.filter (fun z : CubeVertex n =>
        ppos ω' (z, j) = true ∧ pact ω' (z, j) = true ∧
          _root_.hammingDist z x ≤ (hd β γ n).r + (hd β γ n).D)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp, ha, hz⟩
      refine ⟨?_, ?_, hz⟩
      · rw [← agree_pos M tag h (z, j) (by
          have hqx : _root_.hammingDist q x ≤ R := by
            simpa [_root_.hammingDist_comm] using hx
          have hxz : _root_.hammingDist x z ≤ (hd β γ n).r + (hd β γ n).D := by
            simpa [_root_.hammingDist_comm] using hz
          rw [hD] at hxz
          have hqz := _root_.hammingDist_triangle q x z
          have hzq : _root_.hammingDist z q = _root_.hammingDist q z :=
            _root_.hammingDist_comm z q
          calc
            _ = _root_.hammingDist q z := hzq
            _ ≤ _root_.hammingDist q x + _root_.hammingDist x z := hqz
            _ ≤ R + (radius β γ n + 2) := Nat.add_le_add hqx hxz
            _ = R + radius β γ n + 2 := by omega)]
        exact hp
      · rw [← agree_act M tag h (z, j) (by
          have hqx : _root_.hammingDist q x ≤ R := by
            simpa [_root_.hammingDist_comm] using hx
          have hxz : _root_.hammingDist x z ≤ (hd β γ n).r + (hd β γ n).D := by
            simpa [_root_.hammingDist_comm] using hz
          rw [hD] at hxz
          have hqz := _root_.hammingDist_triangle q x z
          have hzq : _root_.hammingDist z q = _root_.hammingDist q z :=
            _root_.hammingDist_comm z q
          calc
            _ = _root_.hammingDist q z := hzq
            _ ≤ _root_.hammingDist q x + _root_.hammingDist x z := hqz
            _ ≤ R + (radius β γ n + 2) := Nat.add_le_add hqx hxz
            _ = R + radius β γ n + 2 := by omega)]
        exact ha
    · rintro ⟨hp, ha, hz⟩
      refine ⟨?_, ?_, hz⟩
      · rw [agree_pos M tag h (z, j) (by
          have hqx : _root_.hammingDist q x ≤ R := by
            simpa [_root_.hammingDist_comm] using hx
          have hxz : _root_.hammingDist x z ≤ (hd β γ n).r + (hd β γ n).D := by
            simpa [_root_.hammingDist_comm] using hz
          rw [hD] at hxz
          have hqz := _root_.hammingDist_triangle q x z
          have hzq : _root_.hammingDist z q = _root_.hammingDist q z :=
            _root_.hammingDist_comm z q
          calc
            _ = _root_.hammingDist q z := hzq
            _ ≤ _root_.hammingDist q x + _root_.hammingDist x z := hqz
            _ ≤ R + (radius β γ n + 2) := Nat.add_le_add hqx hxz
            _ = R + radius β γ n + 2 := by omega)]
        exact hp
      · rw [agree_act M tag h (z, j) (by
          have hqx : _root_.hammingDist q x ≤ R := by
            simpa [_root_.hammingDist_comm] using hx
          have hxz : _root_.hammingDist x z ≤ (hd β γ n).r + (hd β γ n).D := by
            simpa [_root_.hammingDist_comm] using hz
          rw [hD] at hxz
          have hqz := _root_.hammingDist_triangle q x z
          have hzq : _root_.hammingDist z q = _root_.hammingDist q z :=
            _root_.hammingDist_comm z q
          calc
            _ = _root_.hammingDist q z := hzq
            _ ≤ _root_.hammingDist q x + _root_.hammingDist x z := hqz
            _ ≤ R + (radius β γ n + 2) := Nat.add_le_add hqx hxz
            _ = R + radius β γ n + 2 := by omega)]
        exact ha
  have hcard :
      ((Finset.univ.filter (fun z : CubeVertex n =>
        ppos ω (z, j) = true ∧ pact ω (z, j) = true ∧
          _root_.hammingDist z x ≤ (hd β γ n).r + (hd β γ n).D)).card : ℝ) =
      ((Finset.univ.filter (fun z : CubeVertex n =>
        ppos ω' (z, j) = true ∧ pact ω' (z, j) = true ∧
          _root_.hammingDist z x ≤ (hd β γ n).r + (hd β γ n).D)).card : ℝ) := by
    exact_mod_cast congrArg Finset.card hcounts
  have hactElig : ∀ ℓ, ℓ ∈ elig M tag (ppos ω) (paux ω) x j →
      pact ω ℓ = pact ω' ℓ := by
    intro ℓ hℓ
    have hℓ' := hℓ
    unfold elig at hℓ'
    have hraw := (Finset.mem_sdiff.mp hℓ').1
    have hdist : _root_.hammingDist ℓ.1 x ≤ radius β γ n :=
      ((Finset.mem_filter.mp hraw).2).2.2
    have hxℓ : _root_.hammingDist x ℓ.1 ≤ radius β γ n := by
      simpa [_root_.hammingDist_comm] using hdist
    have hqx : _root_.hammingDist q x ≤ R := by
      simpa [_root_.hammingDist_comm] using hx
    have hℓq : _root_.hammingDist ℓ.1 q ≤ R + radius β γ n + 2 := by
      calc
        _ = _root_.hammingDist q ℓ.1 := _root_.hammingDist_comm ℓ.1 q
        _ ≤ _root_.hammingDist q x + _root_.hammingDist x ℓ.1 :=
          _root_.hammingDist_triangle q x ℓ.1
        _ ≤ R + radius β γ n := Nat.add_le_add hqx hxℓ
        _ ≤ R + radius β γ n + 2 := by omega
    exact agree_act M tag h ℓ hℓq
  have hnoActive :
      (∀ ℓ ∈ elig M tag (ppos ω) (paux ω) x j, pact ω ℓ = false) ↔
      (∀ ℓ ∈ elig M tag (ppos ω') (paux ω') x j, pact ω' ℓ = false) := by
    constructor
    · intro hna ℓ hℓ
      have hℓ' : ℓ ∈ elig M tag (ppos ω) (paux ω) x j := by
        rw [hE]
        exact hℓ
      have hact := hactElig ℓ hℓ'
      rw [← hact]
      exact hna ℓ hℓ'
    · intro hna ℓ hℓ
      have hℓ' : ℓ ∈ elig M tag (ppos ω') (paux ω') x j := by
        rw [← hE]
        exact hℓ
      have hact := hactElig ℓ hℓ
      rw [hact]
      exact hna ℓ hℓ'
  unfold HDParams.Bad
  rw [hnoActive, hcard]

private theorem badN_iff_of_agree {q x : CubeVertex n} {R j : ℕ} {ω ω' : Prep M tag}
    (he : EligLocal M tag)
    (h : AgreeOn M tag (ballV q (R + radius β γ n + 2)) ω ω')
    (hx : _root_.hammingDist x q ≤ R) :
    (hd β γ n).BadN (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) x j ↔
      (hd β γ n).BadN (ppos ω') (pact ω') (elig M tag (ppos ω') (paux ω')) x j := by
  unfold HDParams.BadN
  constructor
  · rintro ⟨hj, hb⟩
    exact ⟨hj, (bad_iff_of_agree M tag he h hx ⟨j, hj⟩).mp hb⟩
  · rintro ⟨hj, hb⟩
    exact ⟨hj, (bad_iff_of_agree M tag he h hx ⟨j, hj⟩).mpr hb⟩

private theorem reach_iff_of_agree {q : CubeVertex n} {R : ℕ} {ω ω' : Prep M tag}
    (he : EligLocal M tag)
    (h : AgreeOn M tag (ballV q (R + radius β γ n + 2)) ω ω') :
    ∀ {x j}, (hd β γ n).Reach (evenSites n) (ppos ω) (pact ω)
        (elig M tag (ppos ω) (paux ω)) q R x j ↔
      (hd β γ n).Reach (evenSites n) (ppos ω') (pact ω')
        (elig M tag (ppos ω') (paux ω')) q R x j := by
  intro x j
  constructor
  · intro hr
    induction hr with
    | start v hv hdist => exact .start v hv hdist
    | up v j hj hprev hbad ih =>
      apply HDParams.Reach.up v j hj ih
      exact (badN_iff_of_agree M tag he h (reach_within hprev)).mp hbad
    | down v v' j hprev hv' hdist hstep ih =>
      exact .down v v' j ih hv' hdist hstep
  · intro hr
    induction hr with
    | start v hv hdist => exact .start v hv hdist
    | up v j hj hprev hbad ih =>
      apply HDParams.Reach.up v j hj ih
      exact (badN_iff_of_agree M tag he h (reach_within hprev)).mpr hbad
    | down v v' j hprev hv' hdist hstep ih =>
      exact .down v v' j ih hv' hdist hstep

theorem sel_local_proof (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (he : EligLocal M tag) : SelLocal M tag := by
  classical
  intro v ω ω' h
  let p := hd β γ n
  let R := (hd β γ n).Rlong
  have hreach (j : ℕ) :
      p.Reach (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) v R v j ↔
        p.Reach (evenSites n) (ppos ω') (pact ω')
          (elig M tag (ppos ω') (paux ω')) v R v j := by
    apply reach_iff_of_agree M tag he
    simpa [R] using h
  have hheight :
      p.height (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) R v =
        p.height (evenSites n) (ppos ω') (pact ω') (elig M tag (ppos ω') (paux ω')) R v := by
    unfold HDParams.height
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, hr⟩
      exact ⟨hj, (hreach j).mp hr⟩
    · rintro ⟨hj, hr⟩
      exact ⟨hj, (hreach j).mpr hr⟩
  have hvpos : ∀ j : Fin (topH β γ n + 1),
      ppos ω (v, j) = ppos ω' (v, j) := by
    intro j
    exact agree_pos M tag h (v, j) (by simp)
  have hvact : ∀ j : Fin (topH β γ n + 1),
      pact ω (v, j) = pact ω' (v, j) := by
    intro j
    exact agree_act M tag h (v, j) (by simp)
  have hvtie : ∀ j : Fin (topH β γ n + 1),
      pties ω (v, j) = pties ω' (v, j) := by
    intro j
    exact agree_tie M tag h (v, j) (by simp)
  have hsiteSmall : AgreeOn M tag (ballV v (radius β γ n + 2)) ω ω' :=
    agreeOn_mono M tag (ball_subset (q := v) (x := v) (R := R)
      (S := radius β γ n + 2) (by simp [R])) h
  have hE : ∀ j, elig M tag (ppos ω) (paux ω) v j =
      elig M tag (ppos ω') (paux ω') v j := by
    intro j
    exact he v j ω ω' hsiteSmall
  have hActAtElig : ∀ (j : Fin (topH β γ n + 1)) (ℓ : Loc β γ n),
      ℓ ∈ elig M tag (ppos ω) (paux ω) v j → pact ω ℓ = pact ω' ℓ := by
    intro j ℓ hℓ
    have hℓ' := hℓ
    unfold elig at hℓ'
    have hraw := (Finset.mem_sdiff.mp hℓ').1
    have hdist : _root_.hammingDist ℓ.1 v ≤ radius β γ n :=
      ((Finset.mem_filter.mp hraw).2).2.2
    exact agree_act M tag h ℓ (by omega)
  have hActive (j : Fin (topH β γ n + 1)) :
      (elig M tag (ppos ω) (paux ω) v j).filter (fun ℓ => pact ω ℓ = true) =
      (elig M tag (ppos ω') (paux ω') v j).filter (fun ℓ => pact ω' ℓ = true) := by
    ext ℓ
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hℓ, ha⟩
      have hℓ' : ℓ ∈ elig M tag (ppos ω') (paux ω') v j := by
        rw [← hE j]
        exact hℓ
      have hact := hActAtElig j ℓ hℓ
      exact ⟨hℓ', by rw [← hact]; exact ha⟩
    · rintro ⟨hℓ, ha⟩
      have hℓ' : ℓ ∈ elig M tag (ppos ω) (paux ω) v j := by
        rw [hE j]
        exact hℓ
      have hact := hActAtElig j ℓ hℓ'
      exact ⟨hℓ', by rw [hact]; exact ha⟩
  have hBad : ∀ j : Fin (topH β γ n + 1),
      p.Bad (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) v j ↔
      p.Bad (ppos ω') (pact ω') (elig M tag (ppos ω') (paux ω')) v j := by
    intro j
    exact bad_iff_of_agree M tag he (by simpa using h) (by simp) j
  have hheight' := hheight
  change (hd β γ n).height (evenSites n) (ppos ω) (pact ω)
      (elig M tag (ppos ω) (paux ω)) ((hd β γ n).Rlong) v =
    (hd β γ n).height (evenSites n) (ppos ω') (pact ω')
      (elig M tag (ppos ω') (paux ω')) ((hd β γ n).Rlong) v at hheight'
  have hBad' := hBad
  change ∀ j : Fin (topH β γ n + 1),
      (hd β γ n).Bad (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) v j ↔
      (hd β γ n).Bad (ppos ω') (pact ω') (elig M tag (ppos ω') (paux ω')) v j at hBad'
  unfold sel
  simp [HDParams.selection, HDParams.selectionAt, HDParams.priority,
    hheight', hBad', hActive, hvtie]

private theorem sel_mem_elig {ω : Prep M tag} {v : CubeVertex n} {c : Loc β γ n}
    (hsel : sel M tag ω v = some c) :
    ∃ j : Fin (topH β γ n + 1), c ∈ elig M tag (ppos ω) (paux ω) v j := by
  classical
  let p := hd β γ n
  by_cases hH : (hd β γ n).height (evenSites n) (ppos ω) (pact ω)
      (elig M tag (ppos ω) (paux ω)) (hd β γ n).Rlong v < (hd β γ n).H
  · have hsel' := hsel
    simp [sel, HDParams.selection, HDParams.selectionAt, hH] at hsel'
    rcases hsel' with ⟨_, ⟨hne, hchosen⟩⟩
    let j0 : Fin (p.H + 1) :=
      ⟨p.height (evenSites n) (ppos ω) (pact ω)
        (elig M tag (ppos ω) (paux ω)) p.Rlong v, Nat.lt_succ_of_lt hH⟩
    let active : Finset p.Loc :=
      (elig M tag (ppos ω) (paux ω) v j0).filter (fun ℓ => pact ω ℓ = true)
    let priorities := active.image (p.priority (pties ω) (v, j0))
    have hneP : priorities.Nonempty := by
      rcases hne with ⟨ℓ, hℓ⟩
      exact ⟨p.priority (pties ω) (v, j0) ℓ,
        Finset.mem_image.mpr ⟨ℓ, by simpa [active, j0] using hℓ, rfl⟩⟩
    let q := priorities.min' hneP
    have hmem : ∃ ℓ, ℓ ∈ active ∧ p.priority (pties ω) (v, j0) ℓ = q :=
      Finset.mem_image.mp (Finset.min'_mem priorities hneP)
    have hchosen' : Classical.choose hmem = c := by
      simpa [active, priorities, q, j0] using hchosen
    rcases Classical.choose_spec hmem with ⟨hactive, _⟩
    rw [hchosen'] at hactive
    exact ⟨j0, (Finset.mem_filter.mp hactive).1⟩
  · have hsel' := hsel
    simp [sel, HDParams.selection, HDParams.selectionAt, hH] at hsel'

private theorem sel_mem_ball {ω : Prep M tag} {v : CubeVertex n} {c : Loc β γ n}
    (hsel : sel M tag ω v = some c) : _root_.hammingDist c.1 v ≤ radius β γ n := by
  rcases sel_mem_elig M tag hsel with ⟨j, hj⟩
  have hj' := hj
  unfold elig at hj'
  have hraw := (Finset.mem_sdiff.mp hj').1
  exact ((Finset.mem_filter.mp hraw).2).2.2

private theorem selSet_distance {ω : Prep M tag} {u : OddRole n} {c : Loc β γ n}
    (hc : c ∈ selSet M tag ω u) :
    _root_.hammingDist c.1 u.1 ≤ radius β γ n + 1 := by
  classical
  rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
  have hsel : sel M tag ω v = some c := by simpa using hcv
  have hcv' := sel_mem_ball M tag hsel
  have hvu : _root_.hammingDist v u.1 = 1 := by
    simpa [_root_.hammingDist_comm] using oddAdj_dist hv
  calc
    _ ≤ _root_.hammingDist c.1 v + _root_.hammingDist v u.1 :=
      _root_.hammingDist_triangle c.1 v u.1
    _ ≤ radius β γ n + 1 := by omega

theorem odd_local_proof (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (hs : SelLocal M tag) : OddLocal M tag := by
  classical
  intro u ω ω' h
  have hSelAt : ∀ v, v ∈ oddAdj u → sel M tag ω v = sel M tag ω' v := by
    intro v hv
    have hsub : ballV v ((hd β γ n).Rlong + radius β γ n + 2) ⊆
        ballV u.1 ((hd β γ n).Rlong + radius β γ n + 3) := by
      intro z hz
      have hvz : _root_.hammingDist v z ≤ (hd β γ n).Rlong + radius β γ n + 2 :=
        (Finset.mem_filter.mp hz).2
      have huv : _root_.hammingDist u.1 v = 1 := oddAdj_dist hv
      have huz := _root_.hammingDist_triangle u.1 v z
      exact ball_mem (by omega)
    exact hs v ω ω' (agreeOn_mono M tag hsub h)
  have hsets : selSet M tag ω u = selSet M tag ω' u := by
    unfold selSet
    apply Finset.ext
    intro c
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨v, hv, hc⟩
      refine ⟨v, hv, ?_⟩
      rw [hSelAt v hv] at hc
      exact hc
    · rintro ⟨v, hv, hc⟩
      refine ⟨v, hv, ?_⟩
      rw [← hSelAt v hv] at hc
      exact hc
  have hvalid :
      Valid M tag u (paux ω) (selSet M tag ω u) ↔
        Valid M tag u (paux ω') (selSet M tag ω u) := by
    apply valid_iff_of_agree M tag h u (selSet M tag ω u) (by simp [ballV])
    intro c hc
    have hd := selSet_distance M tag hc
    omega
  have hOK : OddOK M tag ω u ↔ OddOK M tag ω' u := by
    unfold OddOK
    constructor
    · rintro ⟨hsel, hV⟩
      refine ⟨?_, ?_⟩
      · intro v hv
        rw [← hSelAt v hv]
        exact hsel v hv
      · simpa [hsets] using hvalid.mp hV
    · rintro ⟨hsel, hV⟩
      refine ⟨?_, ?_⟩
      · intro v hv
        rw [hSelAt v hv]
        exact hsel v hv
      · have hV' : Valid M tag u (paux ω') (selSet M tag ω u) := by
          simpa [hsets] using hV
        exact hvalid.mpr hV'
  have hmask : aym (paux ω) u = aym (paux ω') u :=
    agree_ymask M tag h u (by simp [ballV])
  have hW : ∀ c ∈ selSet M tag ω u, ∀ κ,
      aW (paux ω) (c, κ) = aW (paux ω') (c, κ) := by
    intro c hc κ
    have hdist := selSet_distance M tag hc
    exact agree_tuple M tag h (c, κ) (by
      change _root_.hammingDist c.1 u.1 ≤ (hd β γ n).Rlong + radius β γ n + 3
      omega)
  have hAll (y : Fin N) :
      HitsAll E G (aW (paux ω)) (selSet M tag ω u) (Zset β γ u) y ↔
        HitsAll E G (aW (paux ω')) (selSet M tag ω u) (Zset β γ u) y := by
    constructor
    · intro hy c hc κ hκ j
      rw [← hW c hc κ]
      exact hy c hc κ hκ j
    · intro hy c hc κ hκ j
      rw [hW c hc κ]
      exact hy c hc κ hκ j
  have hAllD (y : Fin N) :
      HitsAll E G (aW (paux ω)) (selSet M tag ω u) (Zset β γ u) y ↔
        HitsAll E G (aW (paux ω')) (selSet M tag ω' u) (Zset β γ u) y := by
    simpa [hsets] using hAll y
  have hmass :
      (maskLaw (aym (paux ω) u)).pr
          (HitsAll E G (aW (paux ω)) (selSet M tag ω u) (Zset β γ u)) =
        (maskLaw (aym (paux ω') u)).pr
          (HitsAll E G (aW (paux ω')) (selSet M tag ω' u) (Zset β γ u)) := by
    rw [hmask]
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : HitsAll E G (aW (paux ω)) (selSet M tag ω u) (Zset β γ u) y
    · have hy' := (hAllD y).mp hy
      simp [hy, hy']
    · have hy' : ¬ HitsAll E G (aW (paux ω')) (selSet M tag ω' u) (Zset β γ u) y :=
        fun h' => hy ((hAllD y).mpr h')
      simp [hy, hy']
  have hmass' := hmass
  rw [hmask] at hmass'
  constructor
  · exact hOK
  · intro y
    by_cases hgood : OddOK M tag ω u
    · have hgood' := hOK.mp hgood
      simp [oddDraw, hgood, hgood', FinProb.cond, hmask, hmass', hAllD]
    · have hgood' : ¬ OddOK M tag ω' u := fun h' => hgood (hOK.mpr h')
      simp [oddDraw, hgood, hgood']

private theorem dist_add_bound {a v z : CubeVertex n} {K S : ℕ}
    (hav : _root_.hammingDist a v ≤ K) (hvz : _root_.hammingDist v z ≤ S) :
    _root_.hammingDist z a ≤ K + S := by
  have hzv : _root_.hammingDist z v ≤ S := by
    simpa [_root_.hammingDist_comm] using hvz
  have hva : _root_.hammingDist v a ≤ K := by
    simpa [_root_.hammingDist_comm] using hav
  calc
    _ ≤ _root_.hammingDist z v + _root_.hammingDist v a :=
      _root_.hammingDist_triangle z v a
    _ ≤ S + K := Nat.add_le_add hzv hva
    _ ≤ K + S := by omega

private theorem ball_subset_bound {q v : CubeVertex n} {K S T : ℕ}
    (hqv : _root_.hammingDist q v ≤ K) (hT : K + S ≤ T) :
    ballV v S ⊆ ballV q T := by
  intro z hz
  have hvz : _root_.hammingDist v z ≤ S := (Finset.mem_filter.mp hz).2
  exact ball_mem (by
    have hzq := (dist_add_bound hqv hvz).trans hT
    simpa [_root_.hammingDist_comm] using hzq)

private theorem elig_center_dist {ω : Prep M tag} {v : CubeVertex n}
    {l : Fin (topH β γ n + 1)} {c : Loc β γ n}
    (hc : c ∈ elig M tag (ppos ω) (paux ω) v l) :
    _root_.hammingDist c.1 v ≤ radius β γ n := by
  have hc' := hc
  unfold elig at hc'
  have hraw := (Finset.mem_sdiff.mp hc').1
  exact ((Finset.mem_filter.mp hraw).2).2.2

private theorem countAt_eq_of_agree {q v : CubeVertex n} {R K : ℕ}
    {ω ω' : Prep M tag} (h : AgreeOn M tag (ballV q R) ω ω')
    (hqv : _root_.hammingDist q v ≤ K) (hR : K + radius β γ n ≤ R)
    (l : Fin (topH β γ n + 1)) :
    countAt (ppos ω) v l = countAt (ppos ω') v l := by
  classical
  unfold countAt
  congr 1
  apply Finset.ext
  intro z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hz⟩
    refine ⟨?_, hz⟩
    have hzq : _root_.hammingDist z q ≤ K + radius β γ n :=
      dist_add_bound hqv (by simpa [_root_.hammingDist_comm] using hz)
    have hcq : _root_.hammingDist (z, l).1 q ≤ R := by
      have hR' : K + radius β γ n ≤ R := by omega
      simpa using hzq.trans hR'
    rw [← agree_pos M tag h (z, l) hcq]
    exact hp
  · rintro ⟨hp, hz⟩
    refine ⟨?_, hz⟩
    have hzq : _root_.hammingDist z q ≤ K + radius β γ n :=
      dist_add_bound hqv (by simpa [_root_.hammingDist_comm] using hz)
    have hcq : _root_.hammingDist (z, l).1 q ≤ R := by
      have hR' : K + radius β γ n ≤ R := by omega
      simpa using hzq.trans hR'
    rw [agree_pos M tag h (z, l) hcq]
    exact hp

private theorem legalAt_iff_of_agree {v q : CubeVertex n} {R K : ℕ}
    {ω ω' : Prep M tag} (h : AgreeOn M tag (ballV q R) ω ω')
    (hvq : _root_.hammingDist q v ≤ K) (hR : K + radius β γ n + 2 ≤ R)
    (he : EligLocal M tag) (l : Fin (topH β γ n + 1)) :
    (hd β γ n).LegalAt (ppos ω) (elig M tag (ppos ω) (paux ω)) v l ↔
      (hd β γ n).LegalAt (ppos ω') (elig M tag (ppos ω') (paux ω')) v l := by
  classical
  have hsub : ballV v (radius β γ n + 2) ⊆ ballV q R :=
    ball_subset_bound hvq (by omega)
  have hlocal := agreeOn_mono M tag hsub h
  have hE := he v l ω ω' hlocal
  have hpos : ∀ c, c ∈ elig M tag (ppos ω) (paux ω) v l →
      ppos ω c = ppos ω' c := by
    intro c hc
    have hdist := elig_center_dist M tag hc
    exact agree_pos M tag h c (by
      have hcq := dist_add_bound hvq (by simpa [_root_.hammingDist_comm] using hdist)
      have hcq' : _root_.hammingDist c.1 q ≤ R := by
        simpa using hcq.trans (by omega)
      exact hcq')
  unfold HDParams.LegalAt
  constructor
  · rintro ⟨hcoords, hcard⟩
    refine ⟨?_, ?_⟩
    · intro c hc
      have hcOld : c ∈ elig M tag (ppos ω) (paux ω) v l := by
        rw [hE]
        exact hc
      have hcoord := hcoords c hcOld
      have hp := hpos c hcOld
      refine ⟨?_, hcoord.2.1, hcoord.2.2⟩
      rw [← hp]
      exact hcoord.1
    · rw [← hE]
      exact hcard
  · rintro ⟨hcoords, hcard⟩
    refine ⟨?_, ?_⟩
    · intro c hc
      have hcNew : c ∈ elig M tag (ppos ω') (paux ω') v l := by
        rw [← hE]
        exact hc
      have hcoord := hcoords c hcNew
      have hp := hpos c hc
      refine ⟨?_, hcoord.2.1, hcoord.2.2⟩
      rw [hp]
      exact hcoord.1
    · rw [hE]
      exact hcard

private theorem evenAdj_dist_le_two {a : EvenRole n} {j : Fin n}
    {v : CubeVertex n} (hv : v ∈ oddAdj (oddNbr a j)) :
    _root_.hammingDist a.1 v ≤ 2 := by
  have hau : _root_.hammingDist a.1 (oddNbr a j).1 = 1 := by
    change _root_.hammingDist a.1 (cubeFlip a.1 j) = 1
    exact cubeFlip_adj a.1 j
  have huv : _root_.hammingDist (oddNbr a j).1 v = 1 := oddAdj_dist hv
  have hav := _root_.hammingDist_triangle a.1 (oddNbr a j).1 v
  omega

private theorem evenNbr_agree {a : EvenRole n} {j : Fin n} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV a.1 (locR β γ n)) ω ω') :
    AgreeOn M tag
      (ballV (oddNbr a j).1 ((hd β γ n).Rlong + radius β γ n + 3)) ω ω' := by
  have hau : _root_.hammingDist a.1 (oddNbr a j).1 = 1 := by
    change _root_.hammingDist a.1 (cubeFlip a.1 j) = 1
    exact cubeFlip_adj a.1 j
  have hsub : ballV (oddNbr a j).1 ((hd β γ n).Rlong + radius β γ n + 3) ⊆
      ballV a.1 (locR β γ n) := by
    apply ball_subset_bound (q := a.1) (v := (oddNbr a j).1) (K := 1)
      (S := (hd β γ n).Rlong + radius β γ n + 3) (T := locR β γ n)
    · omega
    · dsimp [locR]
      omega
  exact agreeOn_mono M tag hsub h

private theorem evLocal_iff_of_agree {a : EvenRole n} {c : Loc β γ n}
    {ω ω' : Prep M tag} (h : AgreeOn M tag (ballV a.1 (locR β γ n)) ω ω')
    (he : EligLocal M tag) (hs : SelLocal M tag) (ho : OddLocal M tag) :
    EvLocal M tag ω a c ↔ EvLocal M tag ω' a c := by
  classical
  have hsmall : AgreeOn M tag
      (ballV a.1 ((hd β γ n).Rlong + radius β γ n + 2)) ω ω' := by
    have hsub : ballV a.1 ((hd β γ n).Rlong + radius β γ n + 2) ⊆
        ballV a.1 (locR β γ n) := by
      apply ball_subset_bound (q := a.1) (v := a.1) (K := 0)
        (S := (hd β γ n).Rlong + radius β γ n + 2) (T := locR β γ n)
      · simp
      · dsimp [locR]
        omega
    exact agreeOn_mono M tag hsub h
  have hsel : sel M tag ω a.1 = sel M tag ω' a.1 := hs a.1 ω ω' hsmall
  constructor
  · intro hE
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hsel]
      exact hE.sel_eq
    · intro v hv l
      have hva : _root_.hammingDist a.1 v ≤ (hd β γ n).Rlong := by
        simpa [_root_.hammingDist_comm] using (Finset.mem_filter.mp hv).2
      have hLegal := legalAt_iff_of_agree M tag h hva (by
        dsimp [locR]
        omega) he l
      exact hLegal.mp (hE.legal v hv l)
    · intro j
      exact ((ho (oddNbr a j) ω ω' (evenNbr_agree M tag h)).1).mp (hE.odd_ok j)
    · intro j v hv l
      have hdist := evenAdj_dist_le_two hv
      have hcount := countAt_eq_of_agree M tag h hdist (by
        dsimp [locR]
        omega) l
      rw [← hcount]
      exact hE.counts j v hv l
  · intro hE
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsel]
      exact hE.sel_eq
    · intro v hv l
      have hva : _root_.hammingDist a.1 v ≤ (hd β γ n).Rlong := by
        simpa [_root_.hammingDist_comm] using (Finset.mem_filter.mp hv).2
      have hLegal := legalAt_iff_of_agree M tag h hva (by
        dsimp [locR]
        omega) he l
      exact hLegal.mpr (hE.legal v hv l)
    · intro j
      exact ((ho (oddNbr a j) ω ω' (evenNbr_agree M tag h)).1).mpr (hE.odd_ok j)
    · intro j v hv l
      have hdist := evenAdj_dist_le_two hv
      have hcount := countAt_eq_of_agree M tag h hdist (by
        dsimp [locR]
        omega) l
      rw [hcount]
      exact hE.counts j v hv l

private theorem agreeOn_updW {S : Finset (CubeVertex n)} {ω ω' : Prep M tag}
    (h : AgreeOn M tag S ω ω') (ck : Loc β γ n × Key β γ n)
    (z : Fin (tupLen β γ n) → Fin N) :
    AgreeOn M tag S (updW ω ck z) (updW ω' ck z) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases h.1 c hc with ⟨hp, ha, ht⟩
    simp only [ppos] at hp
    simp only [pact] at ha
    simp only [pties] at ht
    simp only [ppos, pact, pties, updW]
    rw [hp, ha, ht]
    exact ⟨rfl, ⟨rfl, rfl⟩⟩
  · intro ck' hc
    have hc' := h.2.1 ck' hc
    refine ⟨?_, ?_⟩
    · simpa [axm, paux, updW] using hc'.1
    · by_cases heq : ck' = ck
      · subst ck'
        simp [aW, paux, updW]
      · simpa [aW, paux, updW, heq] using hc'.2
  · intro u hu
    simpa [aym, paux, updW] using h.2.2 u hu

private theorem oddRow_eq_of_agree {u : OddRole n} {ω ω' : Prep M tag}
    (ho : OddLocal M tag)
    (h : AgreeOn M tag (ballV u.1 ((hd β γ n).Rlong + radius β γ n + 3)) ω ω')
    (y : Fin N) : oddRow M tag ω u y = oddRow M tag ω' u y := by
  obtain ⟨hiff, hdraw⟩ := ho u ω ω' h
  by_cases hgood : OddOK M tag ω u
  · have hgood' := hiff.mp hgood
    simp [oddRow, hgood, hgood', hdraw y]
  · have hgood' : ¬ OddOK M tag ω' u := fun h' => hgood (hiff.mpr h')
    simp [oddRow, hgood, hgood']

private theorem oddAdj_center_dist {a : CubeVertex n} {u : OddRole n} {v : CubeVertex n}
    (hau : _root_.hammingDist a u.1 ≤ 1) (hv : v ∈ oddAdj u) :
    _root_.hammingDist a v ≤ 2 := by
  have huv : _root_.hammingDist u.1 v = 1 := oddAdj_dist hv
  have hav := _root_.hammingDist_triangle a u.1 v
  omega

private theorem refPool_distance {a : CubeVertex n} {u : OddRole n} {c : Loc β γ n}
    {P : Pos β γ n} (hau : _root_.hammingDist a u.1 ≤ 1)
    (hc : c ∈ refPool P u) : _root_.hammingDist c.1 a ≤ radius β γ n + 2 := by
  rcases (Finset.mem_filter.mp hc).2.2 with ⟨v, hv, hcv⟩
  have hav : _root_.hammingDist a v ≤ 2 := oddAdj_center_dist hau hv
  have hva : _root_.hammingDist v a ≤ 2 := by
    simpa [_root_.hammingDist_comm] using hav
  calc
    _ ≤ _root_.hammingDist c.1 v + _root_.hammingDist v a :=
      _root_.hammingDist_triangle c.1 v a
    _ ≤ radius β γ n + 2 := by omega

private theorem refPool_eq_of_agree {a : CubeVertex n} {u : OddRole n}
    {ω ω' : Prep M tag} (h : AgreeOn M tag (ballV a (locR β γ n)) ω ω')
    (hau : _root_.hammingDist a u.1 ≤ 1) :
    refPool (ppos ω) u = refPool (ppos ω') u := by
  classical
  apply Finset.ext
  intro c
  simp only [refPool, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hnear⟩
    have hc : c ∈ refPool (ppos ω) u := by simp [refPool, hp, hnear]
    have hdist := refPool_distance hau hc
    have hloc : _root_.hammingDist c.1 a ≤ locR β γ n := by
      have hRloc : radius β γ n + 2 ≤ locR β γ n := by
        dsimp [locR]
        omega
      exact hdist.trans hRloc
    refine ⟨?_, hnear⟩
    rw [← agree_pos M tag h c hloc]
    exact hp
  · rintro ⟨hp, hnear⟩
    have hc : c ∈ refPool (ppos ω') u := by simp [refPool, hp, hnear]
    have hdist := refPool_distance hau hc
    have hloc : _root_.hammingDist c.1 a ≤ locR β γ n := by
      have hRloc : radius β γ n + 2 ≤ locR β γ n := by
        dsimp [locR]
        omega
      exact hdist.trans hRloc
    refine ⟨?_, hnear⟩
    rw [agree_pos M tag h c hloc]
    exact hp

private theorem refSets_eq_of_agree {a : CubeVertex n} {u : OddRole n}
    {ω ω' : Prep M tag} (h : AgreeOn M tag (ballV a (locR β γ n)) ω ω')
    (hau : _root_.hammingDist a u.1 ≤ 1) (c : Loc β γ n) :
    refSets (ppos ω) u c = refSets (ppos ω') u c := by
  simp [refSets, refPool_eq_of_agree M tag h hau]

private theorem delLaw_w_eq_of_agree {a : CubeVertex n} {u : OddRole n}
    {ω ω' : Prep M tag} {D : Finset (Loc β γ n)} {c : Loc β γ n} {κ : Key β γ n}
    (h : AgreeOn M tag (ballV a (locR β γ n)) ω ω')
    (hau : _root_.hammingDist a u.1 ≤ 1)
    (hD : ∀ c' ∈ D, _root_.hammingDist c'.1 a ≤ locR β γ n) (y : Fin N) :
    (delLaw M tag ω u D c κ).w y = (delLaw M tag ω' u D c κ).w y := by
  classical
  have hu : u.1 ∈ ballV a (locR β γ n) := by
    apply ball_mem
    have hR : 1 ≤ locR β γ n := by
      dsimp [locR]
      omega
    exact hau.trans hR
  have hmask : aym (paux ω) u = aym (paux ω') u := agree_ymask M tag h u hu
  have hW : ∀ c' ∈ D, ∀ κ', aW (paux ω) (c', κ') = aW (paux ω') (c', κ') := by
    intro c' hc' κ'
    exact agree_tuple M tag h (c', κ') (hD c' hc')
  have hbut (x : Fin N) :
      HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ x ↔
        HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ x := by
    constructor
    · intro hx c' hc' κ' hκ' hne j
      rw [← hW c' hc' κ']
      exact hx c' hc' κ' hκ' hne j
    · intro hx c' hc' κ' hκ' hne j
      rw [hW c' hc' κ']
      exact hx c' hc' κ' hκ' hne j
  have hmass :
      (maskLaw (aym (paux ω) u)).pr
          (HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ) =
        (maskLaw (aym (paux ω') u)).pr
          (HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ) := by
    rw [hmask]
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ x
    · have hx' := (hbut x).mp hx
      simp [hx, hx']
    · have hx' : ¬ HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ x :=
        fun hx' => hx ((hbut x).mpr hx')
      simp [hx, hx']
  have hmass' := hmass
  rw [hmask] at hmass'
  by_cases hm : 0 < (maskLaw (aym (paux ω) u)).pr (HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ)
  · have hm' : 0 < (maskLaw (aym (paux ω') u)).pr
        (HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ) := by
      rw [← hmass]
      exact hm
    simp [delLaw, hm, hm', FinProb.cond, hmask, hmass', hbut]
  · have hm' : ¬ 0 < (maskLaw (aym (paux ω') u)).pr
        (HitsBut E G (aW (paux ω')) D (Zset β γ u) c κ) := by
      intro hm'
      apply hm
      rw [hmass]
      exact hm'
    simp only [delLaw, dif_neg hm, dif_neg hm']
    simp [hmask]

private theorem refOK_iff_of_agree {a : CubeVertex n} {u : OddRole n}
    {ω ω' : Prep M tag} (h : AgreeOn M tag (ballV a (locR β γ n)) ω ω')
    (hau : _root_.hammingDist a u.1 ≤ 1) (c : Loc β γ n) :
    RefOK M tag ω u c ↔ RefOK M tag ω' u c := by
  classical
  have hsets := refSets_eq_of_agree M tag h hau c
  have hcount (v : CubeVertex n) (hv : v ∈ oddAdj u) (l : Fin (topH β γ n + 1)) :
      countAt (ppos ω) v l = countAt (ppos ω') v l := by
    have hav := oddAdj_center_dist hau hv
    exact countAt_eq_of_agree M tag h hav (by dsimp [locR]; omega) l
  unfold RefOK
  constructor
  · rintro ⟨hcounts, hnonempty⟩
    refine ⟨?_, ?_⟩
    · intro v hv l
      rw [← hcount v hv l]
      exact hcounts v hv l
    · rw [← hsets]
      exact hnonempty
  · rintro ⟨hcounts, hnonempty⟩
    refine ⟨?_, ?_⟩
    · intro v hv l
      rw [hcount v hv l]
      exact hcounts v hv l
    · rw [hsets]
      exact hnonempty

private theorem refRow_w_eq_of_agree {a : CubeVertex n} {u : OddRole n}
    {ω ω' : Prep M tag} (h : AgreeOn M tag (ballV a (locR β γ n)) ω ω')
    (hau : _root_.hammingDist a u.1 ≤ 1) (c : Loc β γ n) (κ : Key β γ n)
    (y : Fin N) : (refRow M tag ω u c κ).w y = (refRow M tag ω' u c κ).w y := by
  classical
  have hsets := refSets_eq_of_agree M tag h hau c
  have hOK : RefOK M tag ω u c ↔ RefOK M tag ω' u c :=
    refOK_iff_of_agree M tag h hau c
  by_cases hgood : RefOK M tag ω u c
  · have hgood' := hOK.mp hgood
    unfold refRow
    simp only [dif_pos hgood, dif_pos hgood']
    unfold Law.mix
    apply Finset.sum_congr rfl
    intro D _
    by_cases hD : D ∈ refSets (ppos ω) u c
    · have hD' : D ∈ refSets (ppos ω') u c := by
        rw [← hsets]
        exact hD
      have hpow := (Finset.mem_filter.mp hD).1
      have hsub := Finset.mem_powerset.mp hpow
      have hDlocal : ∀ c' ∈ D, _root_.hammingDist c'.1 a ≤ locR β γ n := by
        intro c' hc'
        have hpool : c' ∈ refPool (ppos ω) u := hsub hc'
        have hd := refPool_distance hau hpool
        have hR : radius β γ n + 2 ≤ locR β γ n := by
          dsimp [locR]
          omega
        exact hd.trans hR
      have hρ : (FinProb.uniform (refSets (ppos ω) u c) hgood.2).w D =
          (FinProb.uniform (refSets (ppos ω') u c) hgood'.2).w D := by
        simp [FinProb.uniform, hsets]
      rw [hρ, delLaw_w_eq_of_agree M tag h hau hDlocal y]
    · have hD' : D ∉ refSets (ppos ω') u c := by
        intro hD'
        apply hD
        rw [hsets]
        exact hD'
      simp [FinProb.uniform, hD, hD']
  · have hgood' : ¬ RefOK M tag ω' u c := fun h' => hgood (hOK.mpr h')
    simp [refRow, hgood, hgood']

private theorem refProd_eq_of_agree {a : EvenRole n} {c : Loc β γ n} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV a.1 (locR β γ n)) ω ω')
    (y : Fin n → Fin N) : refProd M tag ω a c y = refProd M tag ω' a c y := by
  classical
  unfold refProd
  apply Finset.prod_congr rfl
  intro j _
  have hau : _root_.hammingDist a.1 (oddNbr a j).1 ≤ 1 := by
    have hflip : _root_.hammingDist a.1 (oddNbr a j).1 = 1 := by
      change _root_.hammingDist a.1 (cubeFlip a.1 j) = 1
      exact cubeFlip_adj a.1 j
    omega
  exact refRow_w_eq_of_agree M tag h hau c (key β γ n a.1) (y j)

private theorem sel_eq_of_agree_even {a : EvenRole n} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV a.1 (locR β γ n)) ω ω') (hs : SelLocal M tag) :
    sel M tag ω a.1 = sel M tag ω' a.1 := by
  have hsub : ballV a.1 ((hd β γ n).Rlong + radius β γ n + 2) ⊆
      ballV a.1 (locR β γ n) := by
    apply ball_subset_bound (q := a.1) (v := a.1) (K := 0)
      (S := (hd β γ n).Rlong + radius β γ n + 2) (T := locR β γ n)
    · simp
    · dsimp [locR]
      omega
  exact hs a.1 ω ω' (agreeOn_mono M tag hsub h)

private theorem comm_eq_of_agree {a : EvenRole n} {c : Loc β γ n} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV a.1 (locR β γ n)) ω ω')
    (hc : _root_.hammingDist c.1 a.1 ≤ locR β γ n) (y : Fin n → Fin N) :
    comm M tag ω a c y = comm M tag ω' a c y := by
  classical
  have hmask : axm (paux ω) (c, key β γ n a.1) = axm (paux ω') (c, key β γ n a.1) := by
    exact agree_mask M tag h (c, key β γ n a.1) (by
      change _root_.hammingDist c.1 a.1 ≤ locR β γ n
      exact hc)
  unfold comm
  simp [hmask]

private theorem marg_eq_of_agree {a : EvenRole n} {c : Loc β γ n} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV a.1 (locR β γ n)) ω ω')
    (hc : _root_.hammingDist c.1 a.1 ≤ radius β γ n)
    (he : EligLocal M tag) (hs : SelLocal M tag) (ho : OddLocal M tag)
    (y : Fin n → Fin N) : marg M tag ω a c y = marg M tag ω' a c y := by
  classical
  have hmask : axm (paux ω) (c, key β γ n a.1) = axm (paux ω') (c, key β γ n a.1) := by
    have hR : radius β γ n ≤ locR β γ n := by
      dsimp [locR]
      omega
    exact agree_mask M tag h (c, key β γ n a.1) (by
      change _root_.hammingDist c.1 a.1 ≤ locR β γ n
      exact hc.trans hR)
  have hprior (z : Fin (tupLen β γ n) → Fin N) :
      (prior M tag ω c (key β γ n a.1)).w z =
        (prior M tag ω' c (key β γ n a.1)).w z := by
    simp [prior, FinProb.pi, hmask]
  have hlik (z : Fin (tupLen β γ n) → Fin N) :
      lik M tag ω a c z y = lik M tag ω' a c z y := by
    have hupd := agreeOn_updW M tag h (c, key β γ n a.1) z
    have hev := evLocal_iff_of_agree M tag (c := c) hupd he hs ho
    have hrows : ∀ j : Fin n,
        oddRow M tag (updW ω (c, key β γ n a.1) z) (oddNbr a j) (y j) =
          oddRow M tag (updW ω' (c, key β γ n a.1) z) (oddNbr a j) (y j) := by
      intro j
      exact oddRow_eq_of_agree M tag ho (evenNbr_agree M tag hupd) (y j)
    simp [lik, hev, hrows]
  unfold marg
  apply Finset.sum_congr rfl
  intro z _
  rw [hprior z, hlik z]

private theorem predOK_iff_of_agree {a : EvenRole n} {c : Loc β γ n}
    {ω ω' : Prep M tag} (h : AgreeOn M tag (ballV a.1 (locR β γ n)) ω ω')
    (hc : _root_.hammingDist c.1 a.1 ≤ radius β γ n)
    (he : EligLocal M tag) (hs : SelLocal M tag) (ho : OddLocal M tag)
    (y : Fin n → Fin N) :
    PredOK M tag ω a c y ↔ PredOK M tag ω' a c y := by
  have hmarg := marg_eq_of_agree M tag h hc he hs ho y
  have href := refProd_eq_of_agree M tag (c := c) h y
  unfold PredOK
  rw [hmarg, href]

private theorem evenRowAt_eq_of_agree {a : EvenRole n} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV a.1 (locR β γ n)) ω ω')
    (he : EligLocal M tag) (hs : SelLocal M tag) (ho : OddLocal M tag)
    (f : OddRole n → Fin N) (x : Fin N) :
    evenRowAt M tag ω a (nbrLabels f a) x = evenRowAt M tag ω' a (nbrLabels f a) x := by
  classical
  have hsel := sel_eq_of_agree_even M tag h hs
  cases hcase : sel M tag ω a.1 with
  | none =>
      have hcase' : sel M tag ω' a.1 = none := by rw [← hsel]; exact hcase
      simp [evenRowAt, hcase, hcase']
  | some c =>
      have hcase' : sel M tag ω' a.1 = some c := by
        rw [hsel] at hcase
        exact hcase
      have hc := sel_mem_ball M tag hcase
      have hev := evLocal_iff_of_agree M tag (c := c) h he hs ho
      have hp := predOK_iff_of_agree M tag h hc he hs ho (nbrLabels f a)
      have hrad : radius β γ n ≤ locR β γ n := by
        dsimp [locR]
        omega
      have hcomm := comm_eq_of_agree M tag (c := c) h (hc.trans hrad) (nbrLabels f a)
      simp [evenRowAt, hcase, hcase', hev, hp, hcomm]

private theorem finN_nonempty (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) :
    Nonempty (Fin N) := by
  classical
  let κ : Key β γ n := fun _ => (⟨0, gadgetPower_pos β γ n⟩, ∅)
  let μ₀ : Law N := M.μ (tag κ)
  by_contra hN
  haveI : IsEmpty (Fin N) := ⟨fun x => hN ⟨x⟩⟩
  have hsum : (∑ x, μ₀.w x) = 0 := by simp
  rw [μ₀.sum_eq_one] at hsum
  norm_num at hsum

private theorem evenMean_eq_of_agree {a : EvenRole n} {ω ω' : Prep M tag}
    (h : AgreeOn M tag (ballV a.1 (locR β γ n)) ω ω')
    (he : EligLocal M tag) (hs : SelLocal M tag) (ho : OddLocal M tag)
    (x : Fin N) : evenMean M tag ω a x = evenMean M tag ω' a x := by
  classical
  let S : Finset (OddRole n) := Finset.univ.image (oddNbr a)
  let P : OddRole n → FinProb (Fin N) := fun u => oddDraw M tag ω u
  let P' : OddRole n → FinProb (Fin N) := fun u => oddDraw M tag ω' u
  let F : (OddRole n → Fin N) → ℝ := fun f => evenRowAt M tag ω a (nbrLabels f a) x
  let F' : (OddRole n → Fin N) → ℝ := fun f => evenRowAt M tag ω' a (nbrLabels f a) x
  let z₀ : Fin N := Classical.choice (finN_nonempty M tag)
  let f₀ : OddRole n → Fin N := fun _ => z₀
  have hdep : FinProb.DependsOn F S := by
    intro f g hfg
    have hlabels : nbrLabels f a = nbrLabels g a := by
      funext j
      exact hfg (oddNbr a j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    simp [F, hlabels]
  have hdep' : FinProb.DependsOn F' S := by
    intro f g hfg
    have hlabels : nbrLabels f a = nbrLabels g a := by
      funext j
      exact hfg (oddNbr a j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    simp [F', hlabels]
  have hred := FinProb.pi_expect_depends P S F f₀ hdep
  have hred' := FinProb.pi_expect_depends P' S F' f₀ hdep'
  let e := Equiv.piEquivPiSubtypeProd (fun u : OddRole n => u ∈ S) (fun _ => Fin N)
  let b₀ : (∀ u : {u // u ∉ S}, Fin N) := fun _ => z₀
  have hdraw : ∀ u, u ∈ S → ∀ y,
      (oddDraw M tag ω u).w y = (oddDraw M tag ω' u).w y := by
    intro u hu y
    rcases Finset.mem_image.mp hu with ⟨j, hj, hju⟩
    subst u
    exact ((ho (oddNbr a j) ω ω' (evenNbr_agree M tag h)).2 y)
  have hredEq :
      (FinProb.pi (fun u : {u // u ∈ S} => P u.1)).expect
          (fun g => F (e.symm (g, b₀))) =
      (FinProb.pi (fun u : {u // u ∈ S} => P' u.1)).expect
          (fun g => F' (e.symm (g, b₀))) := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro g _
    have hweight :
        (FinProb.pi (fun u : {u // u ∈ S} => P u.1)).w g =
          (FinProb.pi (fun u : {u // u ∈ S} => P' u.1)).w g := by
      simp only [FinProb.pi]
      apply Finset.prod_congr rfl
      intro u _
      exact hdraw u.1 u.2 (g u)
    have hrow := evenRowAt_eq_of_agree M tag h he hs ho (e.symm (g, b₀)) x
    have hredpoint : (fun g => F (e.symm (g, b₀))) g =
        (fun g => F' (e.symm (g, b₀))) g := by
      simpa [F, F'] using hrow
    rw [hweight, hredpoint]
  unfold evenMean oddDrawLaw
  calc
    (FinProb.pi P).expect F =
        (FinProb.pi (fun u : {u // u ∈ S} => P u.1)).expect
          (fun g => F (e.symm (g, b₀))) := by
            simpa [P, F, S, e, b₀] using hred
    _ = (FinProb.pi (fun u : {u // u ∈ S} => P' u.1)).expect
          (fun g => F' (e.symm (g, b₀))) := hredEq
    _ = (FinProb.pi P').expect F' := by
          simpa [P', F', S, e, b₀] using hred'.symm

theorem even_local_proof (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (he : EligLocal M tag) (hs : SelLocal M tag) (ho : OddLocal M tag) : EvenLocal M tag := by
  intro a x ω ω' h
  exact evenMean_eq_of_agree M tag h he hs ho x

noncomputable section

private abbrev PrepCoordIndex (β γ : ℝ) (n : ℕ) :=
  Loc β γ n ⊕ (Loc β γ n ⊕ (Loc β γ n ⊕ ((Loc β γ n × Key β γ n) ⊕ OddRole n)))

namespace PrepCoordIndex

private abbrev pos : Loc β γ n → PrepCoordIndex β γ n := Sum.inl
private abbrev act (c : Loc β γ n) : PrepCoordIndex β γ n := Sum.inr (Sum.inl c)
private abbrev tie (c : Loc β γ n) : PrepCoordIndex β γ n := Sum.inr (Sum.inr (Sum.inl c))
private abbrev xblock (ck : Loc β γ n × Key β γ n) : PrepCoordIndex β γ n :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl ck)))
private abbrev ymask (u : OddRole n) : PrepCoordIndex β γ n := Sum.inr (Sum.inr (Sum.inr (Sum.inr u)))

end PrepCoordIndex

private abbrev PrepCoordTy (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) :
    PrepCoordIndex β γ n → Type
  | Sum.inl _ => Bool
  | Sum.inr (Sum.inl _) => Bool
  | Sum.inr (Sum.inr (Sum.inl _)) => (hd β γ n).TiePerm
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ck))) =>
      Mask (M.μ (tag ck.2)) × (Fin (tupLen β γ n) → Fin N)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr u))) => Mask (M.ν (tag (key β γ n u.1)))

private instance prepCoordTyFintype (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (i : PrepCoordIndex β γ n) : Fintype (PrepCoordTy M tag i) := by
  cases i with
  | inl c => simp only [PrepCoordTy]; infer_instance
  | inr rest =>
    cases rest with
    | inl c => simp only [PrepCoordTy]; infer_instance
    | inr rest =>
      cases rest with
      | inl c => simp only [PrepCoordTy]; infer_instance
      | inr rest =>
        cases rest with
        | inl ck => simp only [PrepCoordTy]; infer_instance
        | inr u => simp only [PrepCoordTy]; infer_instance

private noncomputable def PrepCoordLaw (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag)
    (i : PrepCoordIndex β γ n) : FinProb (PrepCoordTy M tag i) := by
  cases i with
  | inl _ =>
      exact FinProb.bernoulli ((hd β γ n).lam / ((hd β γ n).V : ℝ))
  | inr rest =>
    cases rest with
    | inl _ =>
        exact FinProb.bernoulli ((n : ℝ) ^ (hd β γ n).b₀ / (hd β γ n).lam)
    | inr rest =>
      cases rest with
      | inl _ =>
          exact FinProb.uniformAll ⟨Equiv.refl (Fin (Fintype.card (Loc β γ n)))⟩
      | inr rest =>
        cases rest with
        | inl ck =>
            exact FinProb.bind (q ck) fun xm =>
              FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw xm
        | inr u =>
            exact q' u

private def prepCoordSite : PrepCoordIndex β γ n → CubeVertex n
  | Sum.inl c => c.1
  | Sum.inr (Sum.inl c) => c.1
  | Sum.inr (Sum.inr (Sum.inl c)) => c.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ck))) => ck.1.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr u))) => u.1

private def prepCoordToSample (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (z : ∀ i : PrepCoordIndex β γ n, PrepCoordTy M tag i) : Prep M tag :=
  (((fun c => z (PrepCoordIndex.pos c),
      ((fun ck => (z (PrepCoordIndex.xblock ck)).1, fun u => z (PrepCoordIndex.ymask u)),
        fun ck => (z (PrepCoordIndex.xblock ck)).2)),
      fun c => z (PrepCoordIndex.act c)),
    fun c => z (PrepCoordIndex.tie c))

private def sampleToPrepCoord (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (ω : Prep M tag) : ∀ i : PrepCoordIndex β γ n, PrepCoordTy M tag i
  | Sum.inl c => ppos ω c
  | Sum.inr (Sum.inl c) => pact ω c
  | Sum.inr (Sum.inr (Sum.inl c)) => pties ω c
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ck))) => (axm (paux ω) ck, aW (paux ω) ck)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr u))) => aym (paux ω) u

private def prepCoordEquiv (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) :
    (∀ i : PrepCoordIndex β γ n, PrepCoordTy M tag i) ≃ Prep M tag where
  toFun := prepCoordToSample M tag
  invFun := sampleToPrepCoord M tag
  left_inv := by
    intro z
    funext i
    rcases i with c | c | c | ck | u <;> rfl
  right_inv := by
    intro ω
    cases ω with
    | mk x ties =>
      cases x with
      | mk y act =>
        cases y with
        | mk pos aux =>
          cases aux with
          | mk masks W =>
            cases masks with
            | mk xm ym => rfl

private noncomputable def prepCoordBlockLaw (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag) :
    ∀ i : PrepCoordIndex β γ n, FinProb (PrepCoordTy M tag i) :=
  PrepCoordLaw M tag q q'

private theorem map_equiv_weight {α δ : Type*} [Fintype α] [Fintype δ] [DecidableEq δ]
    (P : FinProb α) (e : α ≃ δ) (x : δ) :
    (FinProb.map P e).w x = P.w (e.symm x) := by
  unfold FinProb.map
  have hiff (a : α) : (e a = x) ↔ a = e.symm x := by
    constructor
    · intro h
      apply e.injective
      simpa using h
    · intro h
      simpa [h]
  simp [hiff]

private theorem finProb_ext_of_w {α : Type*} [Fintype α] {P Q : FinProb α}
    (h : P.w = Q.w) : P = Q := by
  cases P with
  | mk pw pn ps =>
    cases Q with
    | mk qw qn qs =>
      simp only at h
      subst qw
      rfl

set_option maxHeartbeats 1000000 in
private theorem prepLaw_eq_coordMap (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag) :
    prepLaw M tag q q' =
      FinProb.map (FinProb.pi (prepCoordBlockLaw M tag q q')) (prepCoordEquiv M tag) := by
  classical
  apply finProb_ext_of_w
  funext ω
  calc
    (prepLaw M tag q q').w ω =
        (FinProb.pi (prepCoordBlockLaw M tag q q')).w (sampleToPrepCoord M tag ω) := by
          dsimp [prepCoordBlockLaw, PrepCoordLaw, PrepCoordTy, prepCoordTyFintype,
            sampleToPrepCoord, ppos, pact, pties,
            paux, axm, aym, aW, prepLaw, auxLaw, tupleLaw, FinProb.pi, FinProb.bind,
            FinProb.prod, HDParams.posLaw, HDParams.actLaw, HDParams.tieLaw,
            FinProb.uniformAll, FinProb.bernoulli]
          simp only [Fintype.prod_sum_type, id_eq]
          rw [Finset.prod_mul_distrib]
          ring
    _ = (FinProb.map (FinProb.pi (prepCoordBlockLaw M tag q q'))
        (prepCoordEquiv M tag)).w ω :=
          (map_equiv_weight (P := FinProb.pi (prepCoordBlockLaw M tag q q'))
            (e := prepCoordEquiv M tag) (x := ω)).symm

private def prepCoordsIn (S : Finset (CubeVertex n)) : Finset (PrepCoordIndex β γ n) :=
  Finset.univ.filter fun i => prepCoordSite i ∈ S

private theorem mem_prepCoordsIn {S : Finset (CubeVertex n)} (i : PrepCoordIndex β γ n) :
    i ∈ prepCoordsIn S ↔ prepCoordSite i ∈ S := by
  simp [prepCoordsIn]

private theorem prepCoord_agree_of_dep {M : Menu4 β γ G n N E X Y}
    {tag : Key β γ n → M.ι} {S : Finset (CubeVertex n)}
    {z z' : ∀ i : PrepCoordIndex β γ n, PrepCoordTy M tag i}
    (h : ∀ i ∈ prepCoordsIn S, z i = z' i) :
    AgreeOn M tag S (prepCoordToSample M tag z) (prepCoordToSample M tag z') := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    have hp := h (PrepCoordIndex.pos c) ((mem_prepCoordsIn (PrepCoordIndex.pos c)).2 (by simp [prepCoordSite, hc]))
    have ha := h (PrepCoordIndex.act c) ((mem_prepCoordsIn (PrepCoordIndex.act c)).2 (by simp [prepCoordSite, hc]))
    have ht := h (PrepCoordIndex.tie c) ((mem_prepCoordsIn (PrepCoordIndex.tie c)).2 (by simp [prepCoordSite, hc]))
    exact ⟨hp, ha, ht⟩
  · intro ck hck
    have hx := h (PrepCoordIndex.xblock ck)
      ((mem_prepCoordsIn (PrepCoordIndex.xblock ck)).2 (by simp [prepCoordSite, hck]))
    exact ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  · intro u hu
    exact h (PrepCoordIndex.ymask u)
      ((mem_prepCoordsIn (PrepCoordIndex.ymask u)).2 (by simpa [prepCoordSite] using hu))

private theorem pi_expect_prod_local {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (T : Finset κ) (S : κ → Finset ι) (f : κ → (∀ i, Ω i) → ℝ)
    (hdisj : ∀ i j, i ∈ T → j ∈ T → i ≠ j → Disjoint (S i) (S j))
    (hlocal : ∀ i, i ∈ T → FinProb.DependsOn (f i) (S i)) :
    (FinProb.pi P).expect (fun ω => ∏ i ∈ T, f i ω) =
      ∏ i ∈ T, (FinProb.pi P).expect (f i) := by
  classical
  induction T using Finset.induction with
  | empty => simp [FinProb.expect_const]
  | @insert i T hi ih =>
      let U := T.biUnion S
      let g : (∀ j, Ω j) → ℝ := fun ω => ∏ j ∈ T, f j ω
      have hdep : FinProb.DependsOn g U := by
        intro ω ω' hω
        apply Finset.prod_congr rfl
        intro j hj
        apply hlocal j (Finset.mem_insert_of_mem hj)
        intro k hk
        exact hω k (Finset.mem_biUnion.mpr ⟨j, hj, hk⟩)
      have hdisj' : Disjoint U (S i) := by
        apply Finset.disjoint_left.mpr
        intro k hk hki
        rcases Finset.mem_biUnion.mp hk with ⟨j, hj, hkj⟩
        have hji : j ≠ i := by
          intro hEq
          subst j
          exact hi hj
        exact (Finset.disjoint_left.mp
          (hdisj j i (Finset.mem_insert_of_mem hj) (Finset.mem_insert_self _ _) hji)) hkj hki
      have hmul := FinProb.pi_expect_mul_of_disjoint P g (f i) U (S i) hdep
        (hlocal i (Finset.mem_insert_self _ _)) hdisj'
      simp only [Finset.prod_insert hi]
      calc
        (FinProb.pi P).expect (fun ω => f i ω * g ω) =
            (FinProb.pi P).expect (fun ω => g ω * f i ω) := by
              apply congrArg (FinProb.expect (FinProb.pi P))
              funext ω
              ring
        _ = (FinProb.pi P).expect g * (FinProb.pi P).expect (f i) := hmul
        _ = (FinProb.pi P).expect (f i) * ∏ j ∈ T, (FinProb.pi P).expect (f j) := by
              rw [ih
                (by
                  intro a b ha hb hab
                  exact hdisj a b (Finset.mem_insert_of_mem ha)
                    (Finset.mem_insert_of_mem hb) hab)
                (by
                  intro a ha
                  exact hlocal a (Finset.mem_insert_of_mem ha))]
              ring

theorem prep_factor_proof (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (q : XProf M tag) (q' : YProf M tag) : PrepFactor M tag q q' := by
  classical
  intro m S f hdisj hlocal
  let P := prepCoordBlockLaw M tag q q'
  let T : Finset (Fin m) := Finset.univ
  let scopes : Fin m → Finset (PrepCoordIndex β γ n) := fun i => prepCoordsIn (S i)
  let funcs : Fin m → (∀ j : PrepCoordIndex β γ n, PrepCoordTy M tag j) → ℝ :=
    fun i z => f i (prepCoordToSample M tag z)
  have hdisj' : ∀ i j, i ∈ T → j ∈ T → i ≠ j → Disjoint (scopes i) (scopes j) := by
    intro i j hi hj hij
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hsitei : prepCoordSite k ∈ S i := (Finset.mem_filter.mp hki).2
    have hsitej : prepCoordSite k ∈ S j := (Finset.mem_filter.mp hkj).2
    exact (Finset.disjoint_left.mp (hdisj i j hij)) hsitei hsitej
  have hlocal' : ∀ i, i ∈ T → FinProb.DependsOn (funcs i) (scopes i) := by
    intro i hi z z' hz
    exact hlocal i (prepCoordToSample M tag z) (prepCoordToSample M tag z')
      (prepCoord_agree_of_dep hz)
  have hfact := pi_expect_prod_local P T scopes funcs hdisj' hlocal'
  have hmain (F : Prep M tag → ℝ) :
      (prepLaw M tag q q').expect F =
        (FinProb.pi P).expect (fun z => F (prepCoordToSample M tag z)) := by
    rw [prepLaw_eq_coordMap M tag q q']
    exact FinProb.map_expect _ _ _
  rw [hmain (fun ω => ∏ i, f i ω)]
  rw [hfact]
  apply Finset.prod_congr rfl
  intro i hi
  exact (hmain (f i)).symm

private theorem pi_weight_split_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (ω : ∀ i, Ω i) :
    (∏ i, (P i).w (ω i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
        (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by
  classical
  let f : ι → ℝ := fun i => (P i).w (ω i)
  let t : Finset ι := Finset.univ.filter (fun i => i ∉ s)
  have hs : (∏ i : {i // i ∈ s}, f i.1) = ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl
  }
  have hnot : (∏ i : {i // i ∉ s}, f i.1) = ∏ i ∈ Finset.univ with i ∉ s, f i := by
    calc
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 :=
        Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, f i) =
        (∏ i ∈ Finset.univ with i ∈ s, f i) *
          (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) * (∏ i : {i // i ∉ s}, f i.1) := by
      rw [← hs, ← hnot]

private theorem pi_expect_split_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
              f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [pi_weight_split_local P s (e.symm (a, b))]
  change ((∏ i : {i // i ∈ s}, (P i.1).w (e.symm (a, b) i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (e.symm (a, b) i.1))) * f (e.symm (a, b)) = _
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [hleft, hright]
  rfl

private def piSingletonEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} (i : ι) :
    (∀ j : {j // j ∈ ({i} : Finset ι)}, Ω j.1) ≃ Ω i where
  toFun := fun x => x ⟨i, by simp⟩
  invFun := fun x j => (Finset.mem_singleton.mp j.2).symm ▸ x
  left_inv := by
    intro x
    funext j
    have hj : j.1 = i := Finset.mem_singleton.mp j.2
    have hj' : j = ⟨i, by simp⟩ := Subtype.ext hj
    subst j
    rfl
  right_inv := by intro x; rfl

private theorem pi_singleton_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (i : ι) (x : ∀ j : {j // j ∈ ({i} : Finset ι)}, Ω j.1) :
    (FinProb.pi (fun j : {j // j ∈ ({i} : Finset ι)} => P j.1)).w x =
      (P i).w (piSingletonEquiv i x) := by
  classical
  letI : Unique {j // j ∈ ({i} : Finset ι)} := {
    default := ⟨i, by simp⟩
    uniq := by
      intro j
      apply Subtype.ext
      exact Finset.mem_singleton.mp j.2
  }
  have hdefault : (default : {j // j ∈ ({i} : Finset ι)}) = ⟨i, by simp⟩ := by
    apply Subtype.ext
    rfl
  simp [FinProb.pi, piSingletonEquiv, hdefault]

private def piUpdate {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (ω : ∀ j, Ω j) (i : ι) (y : Ω i) : ∀ j, Ω j :=
  fun j => if h : j = i then h ▸ y else ω j

set_option maxHeartbeats 1000000 in
private theorem pi_expect_kernel_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ j, Fintype (Ω j)] (P : ∀ j, FinProb (Ω j))
    (i : ι) (K : Ω i → FinProb (Ω i)) (f : (∀ j, Ω j) → ℝ)
    (hinv : ∀ y, (∑ x, (P i).w x * (K x).w y) = (P i).w y) :
    (FinProb.pi P).expect f =
      (FinProb.pi P).expect fun ω => (K (ω i)).expect fun y => f (piUpdate ω i y) := by
  classical
  let s : Finset ι := {i}
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ s) Ω
  let Ps := FinProb.pi (fun j : {j // j ∈ s} => P j.1)
  let Pc := FinProb.pi (fun j : {j // j ∉ s} => P j.1)
  let σ := piSingletonEquiv (Ω := Ω) i
  have hcoord (a : ∀ j : {j // j ∈ s}, Ω j.1)
      (b : ∀ j : {j // j ∉ s}, Ω j.1) :
      (Equiv.piEquivPiSubtypeProd (fun j => j ∈ s) Ω).symm (a, b) i = σ a := by
    simp [e, s, σ, piSingletonEquiv, Equiv.piEquivPiSubtypeProd]
  have hupdate (a : ∀ j : {j // j ∈ s}, Ω j.1)
      (b : ∀ j : {j // j ∉ s}, Ω j.1) (y : Ω i) :
      piUpdate ((Equiv.piEquivPiSubtypeProd (fun j => j ∈ s) Ω).symm (a, b)) i y =
        (Equiv.piEquivPiSubtypeProd (fun j => j ∈ s) Ω).symm (σ.symm y, b) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [piUpdate, e, s, σ, piSingletonEquiv, Equiv.piEquivPiSubtypeProd]
    · simp [piUpdate, hji, e, s, Equiv.piEquivPiSubtypeProd]
  have hweight (a : ∀ j : {j // j ∈ s}, Ω j.1) : Ps.w a = (P i).w (σ a) := by
    simpa [Ps, s, σ] using pi_singleton_weight P i a
  have hsum (H : Ω i → ℝ) :
      (∑ a : (∀ j : {j // j ∈ s}, Ω j.1), Ps.w a * H (σ a)) =
        ∑ x, (P i).w x * H x := by
    calc
      _ = ∑ x, Ps.w (σ.symm x) * H x :=
        Fintype.sum_equiv σ _ _ (by intro a; rfl)
      _ = ∑ x, (P i).w x * H x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hweight (σ.symm x)]
        simp [σ]
  rw [pi_expect_split_local P s f]
  rw [pi_expect_split_local P s (fun ω => (K (ω i)).expect fun y => f (piUpdate ω i y))]
  simp only [FinProb.expect]
  simp_rw [hcoord, hupdate]
  have hleft (b : ∀ j : {j // j ∉ s}, Ω j.1) :
      (∑ a, Ps.w a * f (e.symm (a, b))) =
        ∑ x, (P i).w x * f (e.symm (σ.symm x, b)) := by
    simpa [Equiv.symm_apply_apply] using
      (hsum (fun x => f (e.symm (σ.symm x, b))))
  have hkernel (y : Ω i) :
      (∑ a, Ps.w a * (K (σ a)).w y) =
        ∑ x, (P i).w x * (K x).w y := hsum (fun x => (K x).w y)
  have hR (b : ∀ j : {j // j ∉ s}, Ω j.1) :
      (∑ a, Ps.w a * ∑ y, (K (σ a)).w y * f (e.symm (σ.symm y, b))) =
        ∑ y, (P i).w y * f (e.symm (σ.symm y, b)) := by
    calc
      _ = ∑ y, (∑ a, Ps.w a * (K (σ a)).w y) * f (e.symm (σ.symm y, b)) := by
        calc
          (∑ a, Ps.w a * ∑ y, (K (σ a)).w y * f (e.symm (σ.symm y, b))) =
              ∑ a, ∑ y, Ps.w a * (K (σ a)).w y * f (e.symm (σ.symm y, b)) := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring
          _ = ∑ y, ∑ a, Ps.w a * (K (σ a)).w y * f (e.symm (σ.symm y, b)) :=
                Finset.sum_comm
          _ = ∑ y, (∑ a, Ps.w a * (K (σ a)).w y) * f (e.symm (σ.symm y, b)) := by
                apply Finset.sum_congr rfl
                intro y _
                calc
                  (∑ a, Ps.w a * (K (σ a)).w y * f (e.symm (σ.symm y, b))) =
                      ∑ a, (Ps.w a * (K (σ a)).w y) * f (e.symm (σ.symm y, b)) := by
                        apply Finset.sum_congr rfl
                        intro a _
                        ring
                  _ = (∑ a, Ps.w a * (K (σ a)).w y) * f (e.symm (σ.symm y, b)) :=
                        (Finset.sum_mul Finset.univ
                          (fun a => Ps.w a * (K (σ a)).w y)
                          (f (e.symm (σ.symm y, b)))).symm
      _ = ∑ y, (∑ x, (P i).w x * (K x).w y) * f (e.symm (σ.symm y, b)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hkernel y]
      _ = ∑ y, (P i).w y * f (e.symm (σ.symm y, b)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hinv y]
  calc
    (∑ a, ∑ b, Ps.w a * Pc.w b * f (e.symm (a, b))) =
        ∑ b, Pc.w b * ∑ a, Ps.w a * f (e.symm (a, b)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b _
          calc
            (∑ a, Ps.w a * Pc.w b * f (e.symm (a, b))) =
                ∑ a, Pc.w b * (Ps.w a * f (e.symm (a, b))) := by
                  apply Finset.sum_congr rfl
                  intro a _
                  ring
            _ = Pc.w b * ∑ a, Ps.w a * f (e.symm (a, b)) := by
                  rw [← Finset.mul_sum]
    _ = ∑ b, Pc.w b * ∑ x, (P i).w x * f (e.symm (σ.symm x, b)) := by
          apply Finset.sum_congr rfl
          intro b _
          apply congrArg (fun z : ℝ => Pc.w b * z)
          exact hleft b
    _ = ∑ b, Pc.w b * ∑ y, (P i).w y * f (e.symm (σ.symm y, b)) := by
          rfl
    _ = ∑ b, Pc.w b * (∑ a, Ps.w a * ∑ y, (K (σ a)).w y *
          f (e.symm (σ.symm y, b))) := by
          apply Finset.sum_congr rfl
          intro b _
          apply congrArg (fun z : ℝ => Pc.w b * z)
          exact (hR b).symm
    _ = ∑ a, ∑ b, Ps.w a * Pc.w b * ∑ y, (K (σ a)).w y *
          f (e.symm (σ.symm y, b)) := by
          calc
            _ = ∑ b, ∑ a, Pc.w b *
                  (Ps.w a * ∑ y, (K (σ a)).w y * f (e.symm (σ.symm y, b))) := by
                    apply Finset.sum_congr rfl
                    intro b _
                    rw [← Finset.mul_sum]
            _ = ∑ a, ∑ b, Ps.w a * Pc.w b *
                  ∑ y, (K (σ a)).w y * f (e.symm (σ.symm y, b)) := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro a _
                    apply Finset.sum_congr rfl
                    intro b _
                    ring

private noncomputable def xBlockLaw (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (q : XProf M tag) (ck : Loc β γ n × Key β γ n) :
    FinProb (PrepCoordTy M tag (PrepCoordIndex.xblock ck)) := by
  letI : Fintype (Mask (M.μ (tag ck.2)) × (Fin (tupLen β γ n) → Fin N)) :=
    prepCoordTyFintype M tag (PrepCoordIndex.xblock ck)
  exact FinProb.bind (q ck) fun xm => FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw xm

private noncomputable def xBlockKernel (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (ck : Loc β γ n × Key β γ n)
    (b : PrepCoordTy M tag (PrepCoordIndex.xblock ck)) :
    FinProb (PrepCoordTy M tag (PrepCoordIndex.xblock ck)) := by
  letI : Fintype (Mask (M.μ (tag ck.2)) × (Fin (tupLen β γ n) → Fin N)) :=
    prepCoordTyFintype M tag (PrepCoordIndex.xblock ck)
  exact FinProb.map (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw b.1)
    fun W => (b.1, W)

private theorem xBlockKernel_weight (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (ck : Loc β γ n × Key β γ n)
    (b b' : PrepCoordTy M tag (PrepCoordIndex.xblock ck)) :
    (xBlockKernel M tag ck b).w b' =
      if b.1 = b'.1 then (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw b.1).w b'.2 else 0 := by
  classical
  letI : Fintype (Mask (M.μ (tag ck.2)) × (Fin (tupLen β γ n) → Fin N)) :=
    prepCoordTyFintype M tag (PrepCoordIndex.xblock ck)
  rcases b' with ⟨xm', W'⟩
  by_cases h : b.1 = xm'
  · subst xm'
    change (∑ W, if (b.1, W) = (b.1, W') then
      (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw b.1).w W else 0) = _
    simp
  · have hp : ∀ W : Fin (tupLen β γ n) → Fin N, (b.1, W) ≠ (xm', W') := by
      intro W heq
      exact h (congrArg Prod.fst heq)
    change (∑ W, if (b.1, W) = (xm', W') then
      (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw b.1).w W else 0) = _
    simp [hp]
    intro heq
    exact (h heq).elim

private theorem xBlockKernel_stationary (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (q : XProf M tag) (ck : Loc β γ n × Key β γ n)
    (b' : PrepCoordTy M tag (PrepCoordIndex.xblock ck)) :
    (∑ b, (xBlockLaw M tag q ck).w b * (xBlockKernel M tag ck b).w b') =
      (xBlockLaw M tag q ck).w b' := by
  classical
  letI : Fintype (Mask (M.μ (tag ck.2)) × (Fin (tupLen β γ n) → Fin N)) :=
    prepCoordTyFintype M tag (PrepCoordIndex.xblock ck)
  dsimp [PrepCoordTy, prepCoordTyFintype]
  rcases b' with ⟨xm', W'⟩
  rw [Fintype.sum_prod_type]
  simp_rw [xBlockKernel_weight]
  have hmass (xm : Mask (M.μ (tag ck.2))) :
      ∑ W : Fin (tupLen β γ n) → Fin N,
        (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw xm).w W = 1 :=
    (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw xm).sum_eq_one
  unfold xBlockLaw
  simp only [FinProb.bind]
  calc
    (∑ xm, ∑ W, (q ck).w xm *
        (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw xm).w W *
        (if xm = xm' then (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw xm).w W' else 0)) =
      ∑ xm, if xm = xm' then (q ck).w xm *
          (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw xm).w W' *
          ∑ W, (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw xm).w W else 0 := by
        apply Finset.sum_congr rfl
        intro xm _
        by_cases h : xm = xm'
        · subst xm
          simp only [if_pos rfl, if_true]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro W _
          ring
        · simp [h, eq_comm]
    _ = (q ck).w xm' *
          (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw xm').w W' := by
        simp [hmass, eq_comm]
    _ = (xBlockLaw M tag q ck).w (xm', W') := by
        simp [xBlockLaw, FinProb.bind]

private theorem prepCoordUpdate_toSample (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (z : ∀ i : PrepCoordIndex β γ n, PrepCoordTy M tag i)
    (ck : Loc β γ n × Key β γ n) (W : Fin (tupLen β γ n) → Fin N) :
    prepCoordToSample M tag
        (piUpdate z (PrepCoordIndex.xblock ck) ((z (PrepCoordIndex.xblock ck)).1, W)) =
      updW (prepCoordToSample M tag z) ck W := by
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · funext c'
        simp [prepCoordToSample, piUpdate, updW, ppos, PrepCoordIndex.xblock] <;> rfl
      · apply Prod.ext
        · apply Prod.ext
          · funext ck'
            by_cases h : ck' = ck
            · subst ck'
              simp [prepCoordToSample, piUpdate, updW, paux, axm, PrepCoordIndex.xblock] <;> rfl
            · simp [prepCoordToSample, piUpdate, updW, paux, axm, PrepCoordIndex.xblock, h] <;> rfl
          · funext u
            simp [prepCoordToSample, piUpdate, updW, paux, aym, PrepCoordIndex.xblock] <;> rfl
        · funext ck'
          by_cases h : ck' = ck
          · subst ck'
            funext j
            simp [prepCoordToSample, piUpdate, updW, paux, aW, PrepCoordIndex.xblock] <;> rfl
          · funext j
            simp [prepCoordToSample, piUpdate, updW, paux, aW, PrepCoordIndex.xblock, h] <;> rfl
    · funext c'
      simp [prepCoordToSample, piUpdate, updW, pact, PrepCoordIndex.xblock] <;> rfl
  · funext c'
    simp [prepCoordToSample, piUpdate, updW, pties, PrepCoordIndex.xblock] <;> rfl

theorem prep_resample_proof (M : Menu4 β γ G n N E X Y)
    (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag) :
    Resample M tag q q' := by
  classical
  intro c κ g
  let ck : Loc β γ n × Key β γ n := (c, κ)
  let i₀ : PrepCoordIndex β γ n := PrepCoordIndex.xblock ck
  let P := prepCoordBlockLaw M tag q q'
  let K : PrepCoordTy M tag i₀ → FinProb (PrepCoordTy M tag i₀) :=
    fun b => xBlockKernel M tag ck b
  let F : (∀ i : PrepCoordIndex β γ n, PrepCoordTy M tag i) → ℝ :=
    fun z => g (prepCoordToSample M tag z)
  have hInv : ∀ b, (∑ b₀, (P i₀).w b₀ * (K b₀).w b) = (P i₀).w b := by
    intro b
    simpa [P, i₀, K, prepCoordBlockLaw, PrepCoordLaw, PrepCoordTy,
      prepCoordTyFintype, xBlockLaw, xBlockKernel] using
      xBlockKernel_stationary M tag q ck b
  have hPi := pi_expect_kernel_update P i₀ K F hInv
  have hmain (H : Prep M tag → ℝ) :
      (prepLaw M tag q q').expect H =
        (FinProb.pi P).expect (fun z => H (prepCoordToSample M tag z)) := by
    rw [prepLaw_eq_coordMap M tag q q']
    exact FinProb.map_expect _ _ _
  have hpoint (z : ∀ i : PrepCoordIndex β γ n, PrepCoordTy M tag i) :
      (K (z i₀)).expect (fun b => F (piUpdate z i₀ b)) =
        ∑ W, (prior M tag (prepCoordToSample M tag z) c κ).w W *
          g (updW (prepCoordToSample M tag z) ck W) := by
    change (xBlockKernel M tag ck (z (PrepCoordIndex.xblock ck))).expect
        (fun b => g (prepCoordToSample M tag (piUpdate z (PrepCoordIndex.xblock ck) b))) = _
    unfold xBlockKernel
    rw [FinProb.map_expect]
    have hsample (W : Fin (tupLen β γ n) → Fin N) :=
      prepCoordUpdate_toSample M tag z ck W
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro W _
    change (FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw
        (z (PrepCoordIndex.xblock ck)).1).w W *
        g (prepCoordToSample M tag
          (piUpdate z (PrepCoordIndex.xblock ck) ((z (PrepCoordIndex.xblock ck)).1, W))) = _
    rw [hsample W]
    simp only [prior, prepCoordToSample, paux, axm]
    simp [ck]
  let R : Prep M tag → ℝ := fun ω =>
    ∑ W, (prior M tag ω c κ).w W * g (updW ω ck W)
  calc
    (prepLaw M tag q q').expect g = (FinProb.pi P).expect F := hmain g
    _ = (FinProb.pi P).expect fun z => (K (z i₀)).expect fun b => F (piUpdate z i₀ b) := hPi
    _ = (FinProb.pi P).expect (fun z => R (prepCoordToSample M tag z)) := by
          apply congrArg (FinProb.expect (FinProb.pi P))
          funext z
          exact hpoint z
    _ = (prepLaw M tag q q').expect R := (hmain R).symm

end

end HypercubeRamsey.S04.Lane_q_s04_local
