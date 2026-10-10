module

public import SerrePositivity.Asymptotic.CompletedComplexEvaluation
public import SerrePositivity.Asymptotic.KoszulTower
public import SerrePositivity.PerfectComplex.KoszulAmplitude

/-! # ランク商での新交叉型消滅

商でのスカラーの零作用と、実際の Koszul ホモロジー長の正規化超極限から、
共通の反復錐定理で対象としての消滅を得る。
元の複体列への一様支持は仮定せず、Koszul 複体列自身の一様支持を使う。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 支持部分圏と二段階の商を含む型の比較に余裕を与える。
/-- (Supp) と (Kosₘ) から得られるランク商での消滅。
振幅は Koszul ホモロジー長の超極限で確認すればよい。 -/
theorem completedRankHomology_vanishing_of_koszul
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (a b : ℤ)
    (hKos : ∀ q, q < a ∨ b < q → normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology q)).toReal) = 0)
    (q : ℤ) (hq : q < a + e ∨ b < q) :
    IsZero ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj
      (completedComplexObj z K hK h)) := by
  let x : ℕ → R := fun k ↦ if hk : k < e then z ⟨k, hk⟩ ^ v else 0
  have heq : (fun j : Fin e ↦ x j) = (fun j ↦ z j ^ v) := by
    funext j
    simp [x, j.isLt]
  let X := sequenceKoszulTowerObj completedSequenceFunctor z x K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  have hval (i : ℤ) : completedRankBetti lam hfg z hJ hfin U hU hs (X e) i =
      normalizedLimit U s (fun t ↦ (lam.len
        ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology i)).toReal) := by
    have huni : supportedSequence z
        (sequenceHomotopyObj (sequenceKoszul (fun j : Fin e ↦ x j) K)
          (sequenceKoszul_bounded _ K hK)) := by
      rw [heq]
      exact sequenceKoszul_pow_supported z v hv K hK
    have he := completedRankBetti_complex z lam hfg hJ hfin U hU hs
      (sequenceKoszul (fun j : Fin e ↦ x j) K) (sequenceKoszul_bounded _ K hK)
      huni (X e).property i
    refine he.trans (congrArg (normalizedLimit U s) (funext fun t ↦ ?_))
    rw [heq]
    exact congrArg ENNReal.toReal (lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ i).mapIso
        (evaluateSequenceKoszulIso (fun j ↦ z j ^ v) K t)).toLinearEquiv))
  have hv' := sequenceKoszulTower_vanishing completedSequenceFunctor z x K hK h H e
    (fun j hj ↦ by simpa [x, hj] using hx ⟨j, hj⟩) a b
    (fun i hi ↦ ?_) q hq
  · exact hv'.of_iso
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app (X 0)).symm
  · apply IsZero.of_iso _
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs i).app (X e))
    apply (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mp
    exact (hval i).trans (hKos i hi)

omit [Nontrivial R] in
include hfg hJ in
/-- 各段の Koszul 消滅と項の振幅は、正規化超極限での (Kosₘ) を供給する。 -/
lemma sequenceKoszul_normalizedLimit_amplitude
    (v : ℕ)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ z j ^ v) i) = 0)
    (K : CochainComplex (FreeSequence R s) ℤ) (a b : ℤ)
    (hbound : ∀ t q, q < a ∨ b < q → IsZero (((evaluateComplex t).obj K).X q))
    (q : ℤ) (hq : q < a ∨ b < q) : normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v)
        ((evaluateComplex t).obj K)).homology q)).toReal) = 0 := by
  have hz (t : ℕ) : lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology q) = 0 :=
    lambdaHomology_koszul_projective_amplitude lam hfg (fun j ↦ z j ^ v)
      (le_radical_span_pow z hJ v) hzero ((evaluateComplex t).obj K)
      (fun q ↦ by
        change Module.Finite R (Fin ((K.X q).rank t) → R)
        infer_instance)
      (fun q ↦ by
        change Module.Projective R (Fin ((K.X q).rank t) → R)
        infer_instance) a b (hbound t) q hq
  simp only [hz, ENNReal.toReal_zero, normalizedLimit_zero]

/-- 環自身の Koszul 消滅と自由列の振幅から、商でのホモロジー消滅を得る。 -/
theorem completedRankHomology_vanishing
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ z j ^ v) i) = 0)
    (a b : ℤ)
    (hbound : ∀ t q, q < a ∨ b < q → IsZero (((evaluateComplex t).obj K).X q))
    (q : ℤ) (hq : q < a + e ∨ b < q) :
    IsZero ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj
      (completedComplexObj z K hK h)) :=
  completedRankHomology_vanishing_of_koszul lam hfg z hJ hfin U hU hs K hK h v hv hx a b
    (sequenceKoszul_normalizedLimit_amplitude lam hfg z hJ U v hzero K a b hbound) q hq

/-- 正の cochain ホモロジーが消えると、実際の Koszul 反復は第零次を保つ。 -/
lemma completedRankHomology_koszul_zero_iso
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (v : ℕ)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (habove : ∀ q : ℤ, 0 < q → IsZero
      ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj (completedComplexObj z K hK h))) :
    Nonempty ((completedRankHomology lam hfg z hJ hfin U hU hs 0).obj
      (completedComplexObj z K hK h) ≅
      (completedRankHomology lam hfg z hJ hfin U hU hs 0).obj
        (completedComplexObj z (sequenceKoszul (fun j ↦ z j ^ v) K)
          (sequenceKoszul_bounded _ K hK)
          (sequenceKoszul_map_supported completedSequenceFunctor z _ K hK h))) := by
  let x : ℕ → R := fun k ↦ if hk : k < e then z ⟨k, hk⟩ ^ v else 0
  have heq : (fun j : Fin e ↦ x j) = (fun j ↦ z j ^ v) := by
    funext j
    simp [x, j.isLt]
  let X := sequenceKoszulTowerObj completedSequenceFunctor z x K hK h
  let T := sequenceKoszulTowerTriangle completedSequenceFunctor z x K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  obtain ⟨eq⟩ := iteratedZeroCone_homology_zero_iso X (fun k ↦ (T k).mor₂)
    (fun k ↦ (T k).mor₃) e
    (sequenceKoszulTower_zero_triangles completedSequenceFunctor z x K hK h e
      (fun j hj ↦ by simpa [x, hj] using hx ⟨j, hj⟩)) H
    (fun q hq ↦ (habove q hq).of_iso
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app (X 0)))
  have hf : X e = completedComplexObj z (sequenceKoszul (fun j ↦ z j ^ v) K)
      (sequenceKoszul_bounded _ K hK)
      (sequenceKoszul_map_supported completedSequenceFunctor z _ K hK h) := by
    change completedComplexObj z (sequenceKoszul (fun j : Fin e ↦ x j) K) _ _ = _
    simp only [heq]
  let eq' := ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs 0).app (X 0)).symm ≪≫
    eq ≪≫ (completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs 0).app (X e)
  exact ⟨eq' ≪≫ H.mapIso (eqToIso hf)⟩

/-- 第零次以外が消える場合の Euler 下界は、加法的長さの全射単調性による。 -/
lemma completedRankEuler_lower_bound_of_vanishing
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory)
    (hz : ∀ q : ℤ, q ≠ 0 → IsZero ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj X))
    {Y : LengthSerreQuotient lam s U hU hs}
    (f : (completedRankHomology lam hfg z hJ hfin U hU hs 0).obj X ⟶ Y) [Epi f] :
    lengthQuotientValue lam s U hU hs Y ≤ completedRankEuler lam hfg z hJ hfin U hU hs X := by
  rw [completedRankEuler_eq_homologicalEuler,
    homologicalEuler_eq_length_zero (lengthQuotientValue lam s U hU hs)
      (completedRankHomology lam hfg z hJ hfin U hU hs 0)
      (fun X hX ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs X).mpr hX) X
      (fun q hq ↦ (hz q hq).of_iso
        ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app X))]
  exact (additiveLength_le_of_epi _ (lengthQuotientValue_add lam s U hU hs)
    (lengthQuotientValue_nonneg lam s U hU hs) f).trans_eq
    (lengthQuotientValue_iso lam s U hU hs
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs 0).app X)).symm

/-- Koszul 振幅と実際の第零次 Koszul ホモロジーからの全射による Euler 下界。 -/
theorem completedRankEuler_koszul_lower_bound
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (hKos : ∀ q, q < -(e : ℤ) ∨ 0 < q → normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology q)).toReal) = 0)
    {Y : LengthSerreQuotient lam s U hU hs}
    (f : (completedRankHomology lam hfg z hJ hfin U hU hs 0).obj
      (completedComplexObj z (sequenceKoszul (fun j ↦ z j ^ v) K)
        (sequenceKoszul_bounded _ K hK)
        (sequenceKoszul_map_supported completedSequenceFunctor z _ K hK h)) ⟶ Y) [Epi f] :
    lengthQuotientValue lam s U hU hs Y ≤
      completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) := by
  have hz (q : ℤ) (hq : q ≠ 0) : IsZero
      ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj (completedComplexObj z K hK h)) :=
    completedRankHomology_vanishing_of_koszul lam hfg z hJ hfin U hU hs K hK h v hv hx
      (-(e : ℤ)) 0 hKos q (by omega)
  obtain ⟨eq⟩ := completedRankHomology_koszul_zero_iso lam hfg z hJ hfin U hU hs K hK h v hx
    (fun q hq ↦ hz q (by omega))
  exact completedRankEuler_lower_bound_of_vanishing lam hfg z hJ hfin U hU hs _ hz (eq.hom ≫ f)

end SerrePositivity.Asymptotic
