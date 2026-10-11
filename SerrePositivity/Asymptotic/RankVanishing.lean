module

public import SerrePositivity.Asymptotic.CompletedComplexEvaluation
public import SerrePositivity.Asymptotic.KoszulTower
public import SerrePositivity.PerfectComplex.KoszulAmplitude
public import SerrePositivity.LengthAlgebra.PerfectVanishing

/-! # ランク商での新交叉型消滅と第零次

商でのスカラーの零作用と、実際の Koszul ホモロジー長の正規化超極限から、
共通の反復錐定理で対象としての消滅、Euler 評価の第零次への集中、全射による下界を得る。
元の複体列への一様支持は仮定せず、Koszul 複体列自身の一様支持を使う。

- `completedRankBetti_koszulTower_top`：Koszul 塔の頂上の Betti 数は、各段の実際の Koszul
  ホモロジー長の正規化超極限。共通定理への振幅の入力はこれで確かめる。
- `completedRankHomology_vanishing_of_koszul`、`completedRankHomology_vanishing`：
  `iteratedZeroCone_vanishing` の適用（解説の補題「消滅」のランク版）。
- `completedRankEuler_eq_koszul_zero_limit_of_koszul`：`iteratedZeroCone_euler_eq_length_zero` の
  適用。振幅 `[-e, 0]` では Euler 評価は Koszul 第零ホモロジー長の正規化極限。
- `completedRankEuler_koszul_lower_bound`：`iteratedZeroCone_euler_lower_bound` の適用
  （解説の補題「0 次の下界」のランク版）。
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

omit [Nontrivial R] in
/-- `z` の `v` 乗を自然数で添字づけた Koszul 塔のスカラー列。`e` 以上では `0`。 -/
def koszulPowScalars (v : ℕ) : ℕ → R := LengthAlgebra.koszulScalars (fun j ↦ z j ^ v)

omit [Nontrivial R] in
lemma koszulPowScalars_fin (v : ℕ) :
    (fun j : Fin e ↦ koszulPowScalars z v j) = fun j ↦ z j ^ v :=
  funext fun j ↦ LengthAlgebra.koszulScalars_fin _ j

omit [Nontrivial R] in
lemma koszulPowScalars_of_lt (v j : ℕ) (hj : j < e) :
    koszulPowScalars z v j = z ⟨j, hj⟩ ^ v := by
  simp [koszulPowScalars, LengthAlgebra.koszulScalars, hj]

omit [Nontrivial R] in
/-- `z^v` の零作用は、塔のスカラー列の零作用。 -/
lemma koszulPowScalars_smul_zero {D : Type*} [Category* D] [Preadditive D] [Linear R D]
    (X : D) (v : ℕ) (hx : ∀ j, z j ^ v • 𝟙 X = 0) :
    ∀ j < e, koszulPowScalars z v j • 𝟙 X = 0 := fun j hj ↦ by
  rw [koszulPowScalars_of_lt z v j hj]
  exact hx ⟨j, hj⟩

section tower

variable (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
  (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
  (v : ℕ)

set_option maxHeartbeats 800000 in
-- 支持部分圏と二段階の商を含む型の比較に余裕を与える。
/-- Koszul 塔の頂上の Betti 数は、各段の実際の Koszul ホモロジー長の正規化超極限。 -/
lemma completedRankBetti_koszulTower_top (hv : 0 < v) (i : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs
      (sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v) K hK h e) i =
      normalizedLimit U s (fun t ↦ (lam.len
        ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology i)).toReal) := by
  have huni : supportedSequence z
      (sequenceHomotopyObj (sequenceKoszul (fun j : Fin e ↦ koszulPowScalars z v j) K)
        (sequenceKoszul_bounded _ K hK)) := by
    rw [koszulPowScalars_fin]
    exact sequenceKoszul_pow_supported z v hv K hK
  have he := completedRankBetti_complex z lam hfg hJ hfin U hU hs
    (sequenceKoszul (fun j : Fin e ↦ koszulPowScalars z v j) K) (sequenceKoszul_bounded _ K hK)
    huni (sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v)
      K hK h e).property i
  refine he.trans (congrArg (normalizedLimit U s) (funext fun t ↦ ?_))
  rw [koszulPowScalars_fin]
  exact congrArg ENNReal.toReal (lam.len_congr _ _
    (((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (evaluateSequenceKoszulIso (fun j ↦ z j ^ v) K t)).toLinearEquiv))

set_option maxHeartbeats 800000 in
-- 支持部分圏と二段階の商を含む型の比較に余裕を与える。
/-- (Supp) と (Kosₘ) から得られるランク商での消滅。
振幅は Koszul ホモロジー長の超極限で確認すればよい。共通定理 `iteratedZeroCone_vanishing` の適用。 -/
theorem completedRankHomology_vanishing_of_koszul (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (a b : ℤ)
    (hKos : ∀ q, q < a ∨ b < q → normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology q)).toReal) = 0)
    (q : ℤ) (hq : q < a + e ∨ b < q) :
    IsZero ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj
      (completedComplexObj z K hK h)) := by
  let X := sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  have hv' := sequenceKoszulTower_vanishing completedSequenceFunctor z (koszulPowScalars z v)
    K hK h H e (koszulPowScalars_smul_zero z _ v hx) a b (fun i hi ↦ ?_) q hq
  · exact hv'.of_iso
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app (X 0)).symm
  · apply IsZero.of_iso _
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs i).app (X e))
    apply (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mp
    exact (completedRankBetti_koszulTower_top lam hfg z hJ hfin U hU hs K hK h v hv i).trans
      (hKos i hi)

set_option maxHeartbeats 800000 in
-- 支持部分圏と二段階の商を含む型の比較に余裕を与える。
/-- 振幅 `[-e, 0]` では、Euler 評価は実際の Koszul 第零ホモロジーの正規化極限。
共通定理 `iteratedZeroCone_euler_eq_length_zero` の適用。 -/
theorem completedRankEuler_eq_koszul_zero_limit_of_koszul (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (hKos : ∀ q, q < -(e : ℤ) ∨ 0 < q → normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology q)).toReal) = 0) :
    completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) =
      normalizedLimit U s (fun t ↦ (lam.len
        ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology 0)).toReal) := by
  let X := sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let T := sequenceKoszulTowerTriangle completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  rw [completedRankEuler_eq_homologicalEuler]
  change homologicalEuler _ H (X 0) = _
  rw [iteratedZeroCone_euler_eq_length_zero X (fun k ↦ (T k).mor₂) (fun k ↦ (T k).mor₃) e
    (sequenceKoszulTower_zero_triangles completedSequenceFunctor z (koszulPowScalars z v) K hK h e
      (koszulPowScalars_smul_zero z _ v hx)) H
    (lengthQuotientValue lam s U hU hs) (lengthQuotientValue_iso lam s U hU hs)
    (fun Y hY ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs Y).mpr hY) (fun q hq ↦ ?_)]
  · exact (lengthQuotientValue_iso lam s U hU hs
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs 0).app (X e))).trans
      (completedRankBetti_koszulTower_top lam hfg z hJ hfin U hU hs K hK h v hv 0)
  · apply IsZero.of_iso _
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app (X e))
    apply (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mp
    exact (completedRankBetti_koszulTower_top lam hfg z hJ hfin U hU hs K hK h v hv q).trans
      (hKos q hq)

set_option maxHeartbeats 800000 in
-- 支持部分圏と二段階の商を含む型の比較に余裕を与える。
/-- Koszul 振幅と実際の第零次 Koszul ホモロジーからの全射による Euler 下界。
共通定理 `iteratedZeroCone_euler_lower_bound` の適用。 -/
theorem completedRankEuler_koszul_lower_bound (hv : 0 < v)
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
  let X := sequenceKoszulTowerObj completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let T := sequenceKoszulTowerTriangle completedSequenceFunctor z (koszulPowScalars z v) K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  have hf : X e = completedComplexObj z (sequenceKoszul (fun j ↦ z j ^ v) K)
      (sequenceKoszul_bounded _ K hK)
      (sequenceKoszul_map_supported completedSequenceFunctor z _ K hK h) := by
    change completedComplexObj z (sequenceKoszul (fun j : Fin e ↦ koszulPowScalars z v j) K) _ _ = _
    simp only [koszulPowScalars_fin]
  let f' : (H.shift (0 : ℤ)).obj (X e) ⟶ Y :=
    ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs 0).app (X e)).hom ≫
      (H.mapIso (eqToIso hf)).hom ≫ f
  have : Epi f' := inferInstance
  rw [completedRankEuler_eq_homologicalEuler]
  change _ ≤ homologicalEuler _ H (X 0)
  apply iteratedZeroCone_euler_lower_bound X (fun k ↦ (T k).mor₂) (fun k ↦ (T k).mor₃) e
    (sequenceKoszulTower_zero_triangles completedSequenceFunctor z (koszulPowScalars z v) K hK h e
      (koszulPowScalars_smul_zero z _ v hx)) H
    (lengthQuotientValue lam s U hU hs) (lengthQuotientValue_iso lam s U hU hs)
    (lengthQuotientValue_add lam s U hU hs) (lengthQuotientValue_nonneg lam s U hU hs)
    (fun Y hY ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs Y).mpr hY) ?_ f'
  intro q hq
  apply IsZero.of_iso _ ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app (X e))
  apply (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mp
  exact (completedRankBetti_koszulTower_top lam hfg z hJ hfin U hU hs K hK h v hv q).trans
    (hKos q hq)

end tower

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

end SerrePositivity.Asymptotic

