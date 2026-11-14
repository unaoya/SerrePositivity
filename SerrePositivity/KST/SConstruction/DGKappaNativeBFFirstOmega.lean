module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFFirstComparison
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformationWhisker

/-!
概要：有限 native BF 再帰の基底の全 Hom 自然性と同じ実 Ω 条件。
方針：元の単射置換変換を使い、同じ評価の基点固定成分で随伴を比較する。
規約：元の零段 ΩB₀ を固定する。使われ方：同じ全四角形上の再帰基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories NonConnective Spectra
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：最初の同じ B₀ 比較は全 Hom に厳密に自然。
方針：元の単射置換の標的変換を、同じ成分で回収する。
規約：有限入力に限定。使われ方：実 BF 正段再帰の初期比較。 -/
lemma dgKappaNativeBFFiniteFirstComparison_whisker
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).map C E ≫
        eHomWhiskerLeft SSet ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C)
          (dgKappaNativeBFFiniteFirstComparison.{u, v} R D I E) =
      (dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).map C E ≫
        eHomWhiskerRight SSet (dgKappaNativeBFFiniteFirstComparison.{u, v} R D I C)
          ((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj E) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _
    (pointedEnrichedMonicReplacementTargetTransformation
      (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
      (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
      (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I))
    (dgKappaNativeBFFiniteFirstComparison.{u, v} R D I)
    (pointedEnrichedMonicReplacementTargetTransformation_app
      (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
      (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
      (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I)) C E

local instance nativeFiniteFirstOmegaZeroKan (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteZeroFunctor.{u, v} R D I).obj C).obj).right :=
  dgKappaNativeBFFiniteZero_kanComplex.{u, v} R D I C

local instance nativeFiniteFirstOmegaLoopKan (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex ((ihom PointedSimplicialSet.circle.{max (u + 1) v}).obj
      ((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C).obj).right :=
  loopSpace_kanComplex _

/-- 概要：同じ最初の実構造射は元の Ω 条件を満たす。
方針：同じ B₀ 比較の π 同型と、元の評価の円柱成分を使う。
規約：零段は同じ ΩB₀。使われ方：有限 BF Ω 列の帰納基底。 -/
lemma dgKappaNativeBFFiniteFirstStructureAdjoint_piIsomorphism
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (curry
      (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (((dgKappaNativeBFFiniteZeroFunctor.{u, v} R D I).obj C).obj) ⟶
        ((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C).obj from
          dgKappaNativeBFFiniteFirstStructureMap.{u, v} R D I C)).right := by
  apply evaluationCylinderAdjoint_piIsomorphism
    (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C).obj ⟶
      ((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C).obj from
        dgKappaNativeBFFiniteFirstComparison.{u, v} R D I C)
    (dgKappaNativeBFFiniteFirstComparison_piIsomorphism.{u, v} R D I C)
  exact pointedEnrichedMonicReplacementSource_component
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
    (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
    (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I) C

end SerrePositivity.KST.SConstruction
