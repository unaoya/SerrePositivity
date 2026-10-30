module

public import SerrePositivity.Asymptotic.MinimalTruncationComparison
public import SerrePositivity.Asymptotic.MinimalSupport
public import SerrePositivity.Asymptotic.KoszulHomologyLimit
public import SerrePositivity.Asymptotic.PaperBaseChangeEvaluation
public import SerrePositivity.CategoryTheory.IteratedCone
public import SerrePositivity.CategoryTheory.AlternatingSum

/-! # 極小分解の正規化極限とランク商の Betti 評価

全分解の Koszul 分裂と、商における同じ二項公式を比較する。
比較する次数ごとに切り詰めを深くするため、切り詰めの境界に支持を要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits Filter Asymptotics IsLocalRing

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing S] (φ : R →+* S)

/-- 極小分解全体を係数変更した複体。一般には下に非有界である。 -/
noncomputable abbrev minimalBaseChangeResolution (M : FGModuleCat.{u} R) :=
  baseChange φ (extRes (MinimalFreeResolution.resolution M))

/-- 加群の消去元は、係数変更した全分解でも零ホモトピックに作用する。 -/
lemma minimalBaseChangeResolution_null (M : FGModuleCat.{u} R) (a : R)
    (ha : a • 𝟙 M.obj = 0) :
    Nonempty (Homotopy (smulId (φ a) (minimalBaseChangeResolution φ M)) 0) := by
  have h := (ModuleCat.extendScalars φ).mapHomotopy
    (resolutionScalarNullHomotopy (MinimalFreeResolution.resolution M) a ha)
  rw [extendScalars_mapHomologicalComplex_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at h
  exact ⟨h⟩

variable [Nontrivial S] {s : ℕ → ℕ} (M : ℕ → FGModuleCat.{u} R)
  {e : ℕ} (z : Fin e → R) {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)

omit [Nontrivial S] in
include hfg hJ hfin in
/-- 全分解の各次数の長さは有限で `O(s)`。有限性を新しい入力にせず、
深い有限自由モデルの Koszul 評価と、その直和因子への上界から導く。 -/
lemma minimalBaseChangeResolution_length_bound
    (hbetti : ∀ i,
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)))
    (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0) (q : ℤ) :
    (∀ n, lam.len ((minimalBaseChangeResolution φ (M n)).homology q) ≠ ⊤) ∧
    (fun n ↦ (lam.len ((minimalBaseChangeResolution φ (M n)).homology q)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
  let m := (-q).toNat + 1
  obtain ⟨L, hb, eL, _, _⟩ := exists_minimal_truncated_sequence M m (fun i _ ↦ hbetti i)
  let hL : strictlyBoundedComplex _ L := ⟨-(m : ℤ), 0, hb.1, hb.2⟩
  let L' := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj L
  let hL' := changeRing_strictlyBounded φ L hL
  let x : Fin e → S := fun j ↦ φ (z j) ^ v
  have hJ' : J ≤ (Ideal.span (Set.range x)).radical := le_radical_span_pow (φ ∘ z) hJ v
  have hnull (n : ℕ) (j : Fin e) : Nonempty
      (Homotopy (smulId (x j) (minimalBaseChangeResolution φ (M n))) 0) := by
    simpa only [map_pow] using minimalBaseChangeResolution_null φ (M n) (z j ^ v) (hM n j)
  let P := fun n ↦ minimalBaseChangeResolution φ (M n)
  have hlen (n : ℕ) : lam.len ((koszulComplexOn x (P n)).homology q) =
      lam.len ((koszulComplexOn x ((evaluateComplex n).obj L')).homology q) := by
    apply lam.len_congr _ _
    exact ((minimalModelKoszulHomologyIsoAt M φ m L (fun n ↦ (eL n).some) x q
      (by dsimp [m]; omega) n).symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ q).mapIso
        ((koszulFunctor x).mapIso (FreeSequence.evaluateComplexTensorIso φ n L))).toLinearEquiv
  have hkfin (n : ℕ) : lam.len ((koszulComplexOn x (P n)).homology q) ≠ ⊤ := by
    rw [hlen]
    exact sequenceKoszulHomology_ne_top lam hfg x hJ' (hfin v hv) L' hL' n q
  have hkO : (fun n ↦ (lam.len ((koszulComplexOn x (P n)).homology q)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
    simp_rw [hlen]
    exact sequenceKoszulHomology_isBigO lam hfg x hJ' (hfin v hv) L' hL' q
  have hle (n : ℕ) : lam.len ((P n).homology q) ≤
      lam.len ((koszulComplexOn x (P n)).homology q) := by
    let r := (retractKoszulComplexOn x (P n) (hnull n)).map
      (HomologicalComplex.homologyFunctor _ _ q)
    exact lam.len_le_of_injective r.i.hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
      (supported_homology_isPowTorsion hfg hJ' (isSupported_koszulComplexOn x (P n)) q)
  refine ⟨fun n ↦ ne_top_of_le_ne_top (hkfin n) (hle n), ?_⟩
  apply IsBigO.trans (g := fun n ↦ (lam.len ((koszulComplexOn x (P n)).homology q)).toReal) ?_ hkO
  apply IsBigO.of_norm_le
  intro n
  simp only [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (hkfin n) (hle n)

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 支持つき商の係数変更と、代表の同型による評価の移送を同時に簡約するため。
/-- 高次 Betti 数が `o(s)` で、加群列に共通の消去冪があれば、ランク商の評価は
全極小分解のホモロジー長の正規化極限と一致する。元の切り詰めの一様支持は不要。 -/
theorem paperBaseChangeBetti_eq_minimal_homology_limit
    (l : ℕ) (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
    (hbetti : ∀ i ≤ l,
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)))
    (hsmall : ∀ i, l < i →
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ)))
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0) (q : ℤ) :
    paperBaseChangeBetti φ z lam hfg hJ hfin U hU hs
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ q =
    normalizedLimit U s (fun n ↦
      (lam.len ((minimalBaseChangeResolution φ (M n)).homology q)).toReal) := by
  let P := fun n ↦ minimalBaseChangeResolution φ (M n)
  let X : (paperSupportedRank (s := s) z).FullSubcategory :=
    ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩
  have hall (i : ℕ) :
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)) := by
    by_cases hi : i ≤ l
    · exact hbetti i hi
    · exact (hsmall i (by omega)).isBigO
  have hbound := minimalBaseChangeResolution_length_bound φ M z lam hfg hJ hfin hall v hv hM
  have hnull (n : ℕ) (j : Fin e) : Nonempty
      (Homotopy (smulId (φ (z j) ^ v) (P n)) 0) := by
    simpa only [map_pow] using minimalBaseChangeResolution_null φ (M n) (z j ^ v) (hM n j)
  have ht (n : ℕ) (q : ℤ) : IsPowTorsion J ((P n).homology q) :=
    supported_homology_isPowTorsion hfg hJ (show IsSupported (φ ∘ z) (P n) from
      ⟨v, hnull n⟩) q
  have heq : paperBaseChangeBetti φ z lam hfg hJ hfin U hU hs X =
      fun q ↦ normalizedLimit U s (fun n ↦ (lam.len ((P n).homology q)).toReal) := by
    apply coneLength_binomial_cancel_of_hasFiniteSupport e _ _
      (paperBaseChangeBetti_hasFiniteSupport φ z lam hfg hJ hfin U hU hs X) 1
    · intro q hq
      have hz (n : ℕ) : (lam.len ((P n).homology q)).toReal = 0 := by
        have hx : IsZero ((P n).X q) := (ModuleCat.extendScalars φ).map_isZero
          (extRes_isZero_X (MinimalFreeResolution.resolution (M n)) q (by omega))
        have := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X (P n) q hx)
        rw [lam.len_eq_zero_of_subsingleton, ENNReal.toReal_zero]
      simp_rw [hz]
      exact normalizedLimit_zero U s
    · intro q
      let m := max l ((-q).toNat + 1)
      obtain ⟨L, hb, eL, ⟨iKL⟩⟩ := exists_deeper_minimal_truncation M l m (le_max_left _ _)
        K hK eK hbetti (fun i hi _ ↦ hsmall i hi)
      let hL : strictlyBoundedComplex _ L := ⟨-(m : ℤ), 0, hb.1, hb.2⟩
      have h' := (scalarSupported z).prop_of_iso iKL h
      have hx (j : Fin e) : z j ^ v • 𝟙
          ((paperSequenceFunctor R s).obj (sequenceHomotopyObj L hL)) = 0 :=
        minimal_truncated_paper_scalar_zero M m L hL eL
          (hsmall (m + 1) (by dsimp [m]; omega)) (z j ^ v) (fun n ↦ hM n j)
      have hi (r : ℤ) := paperBaseChangeBetti_iso φ z lam hfg hJ hfin U hU hs
        (show X ≅ ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj L hL), h'⟩ from
          ObjectProperty.isoMk _ iKL) r
      have hformula := paperBaseChangeBetti_koszul_formula φ z lam hfg hJ hfin U hU hs
        L hL h' v hv hx (-q)
      simp only [neg_sub, sub_neg_eq_add, add_comm] at hformula
      have hlen (n : ℕ) : lam.len
          ((koszulComplexOn (fun j ↦ φ (z j) ^ v)
            (baseChange φ ((evaluateComplex n).obj L))).homology (- -q)) =
          lam.len ((koszulComplexOn (fun j ↦ φ (z j) ^ v) (P n)).homology q) := by
        apply lam.len_congr _ _
        exact (eqToIso (congrArg (fun r : ℤ ↦
          (koszulComplexOn (fun j ↦ φ (z j) ^ v)
            (baseChange φ ((evaluateComplex n).obj L))).homology r) (neg_neg q)) ≪≫
          minimalModelKoszulHomologyIsoAt M φ m L
            (fun n ↦ (eL n).some) _ q (by dsimp [m]; omega) n).toLinearEquiv
      simp_rw [← hi, hlen] at hformula
      rw [← hformula]
      exact normalizedLimit_koszul_null_binomial lam _ P hnull ht
        (fun n q ↦ (hbound q).1 n) U hU s hs (fun q ↦ (hbound q).2) q
  exact congrFun heq q

variable (l : ℕ) (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
  (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
  (hbetti : ∀ i ≤ l,
    (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
      =O[atTop] (fun n ↦ (s n : ℝ)))
  (hsmall : ∀ i, l < i →
    (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
      =o[atTop] (fun n ↦ (s n : ℝ)))
  (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
  (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0)

include eK hbetti hsmall hv hM in
/-- 商の各次数の評価を、代数係数の Tor の正規化極限として計算する。 -/
theorem paperBaseChangeBetti_eq_minimal_tor_limit (i : ℕ) :
    paperBaseChangeBetti φ z lam hfg hJ hfin U hU hs
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ (-(i : ℤ)) =
    normalizedLimit U s (fun n ↦ (lam.len (TorAlg φ i (M n))).toReal) := by
  rw [paperBaseChangeBetti_eq_minimal_homology_limit φ M z lam hfg hJ hfin U hU hs
    l K hK eK hbetti hsmall h v hv hM]
  congr 1
  funext n
  let e := torIsoCochain φ (isResolutionOf_extRes (MinimalFreeResolution.resolution (M n))) i
  exact congrArg ENNReal.toReal (lam.len_congr _ _ e.toLinearEquiv.symm)

include eK hbetti hsmall hv hM in
/-- 極小分解から構成した対象は、係数変更後も正の cochain 次数の評価が零。 -/
lemma paperBaseChangeBetti_minimal_eq_zero_of_pos (q : ℤ) (hq : 0 < q) :
    paperBaseChangeBetti φ z lam hfg hJ hfin U hU hs
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ q = 0 := by
  rw [paperBaseChangeBetti_eq_minimal_homology_limit φ M z lam hfg hJ hfin U hU hs
    l K hK eK hbetti hsmall h v hv hM]
  have hz (n : ℕ) :
      (lam.len ((minimalBaseChangeResolution φ (M n)).homology q)).toReal = 0 := by
    have hx := (ModuleCat.extendScalars φ).map_isZero
      (extRes_isZero_X (MinimalFreeResolution.resolution (M n)) q hq)
    have := ModuleCat.subsingleton_of_isZero
      (isZero_homology_of_isZero_X (minimalBaseChangeResolution φ (M n)) q hx)
    rw [lam.len_eq_zero_of_subsingleton, ENNReal.toReal_zero]
  simp_rw [hz]
  exact normalizedLimit_zero U s

include eK hbetti hsmall hv hM in
/-- 商の Euler 評価は、Tor の各次数の正規化極限の交代和である。
各段の Euler 数との極限交換は主張せず、商で有限支持になった係数を足し合わせる。 -/
theorem paperBaseChangeEulerK0_eq_minimal_tor_limits :
    paperBaseChangeEulerK0 φ z lam hfg hJ hfin U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) =
    ∑ᶠ i : ℕ, (-1 : ℝ) ^ i *
      normalizedLimit U s (fun n ↦ (lam.len (TorAlg φ i (M n))).toReal) := by
  rw [paperBaseChangeEulerK0_mk, alternating_finsum_eq_nat _
    (paperBaseChangeBetti_minimal_eq_zero_of_pos φ M z lam hfg hJ hfin U hU hs
      l K hK eK hbetti hsmall h v hv hM)]
  congr 1
  funext i
  rw [paperBaseChangeBetti_eq_minimal_tor_limit φ M z lam hfg hJ hfin U hU hs
    l K hK eK hbetti hsmall h v hv hM]

end SerrePositivity.Asymptotic
