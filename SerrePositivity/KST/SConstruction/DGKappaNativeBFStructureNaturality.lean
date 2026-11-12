module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFStepValue

/-!
概要：有限 native BF の元の全構造射の厳密な全 Hom 自然性。
方針：最初の源の括弧を照合し、同じ実単射置換と円柱押し出しの変換を使う。
規約：元の全実構造射を保持。使われ方：同じ四辺と二胞体を全 BF 写像空間へ束ねる。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories NonConnective
open Spectra
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：零段の suspension の作用は元の評価の源の作用に一致。
方針：同じ三つの元の Hom 作用の合成の括弧を照合する。
規約：全単体の等式。使われ方：最初の構造射の自然性。 -/
lemma dgKappaNativeBFFiniteZeroSuspension_map
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    ((dgKappaNativeBFFiniteZeroFunctor.{u, v} R D I).comp SSet
      (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})).map C E =
      (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I).map C E :=
  Category.assoc _ _ _

/-- 概要：同じ最初の実構造射は全 Hom に厳密に自然。
方針：同じ単射置換の源変換を元の零段の suspension に回収する。
規約：元の構造射を保持。使われ方：有限 BF 全列の構造自然性の基底。 -/
lemma dgKappaNativeBFFiniteFirstStructureMap_whisker
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    ((dgKappaNativeBFFiniteZeroFunctor.{u, v} R D I).comp SSet
        (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})).map C E ≫
        eHomWhiskerLeft SSet
          (((dgKappaNativeBFFiniteZeroFunctor.{u, v} R D I).comp SSet
            (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})).obj C)
          (dgKappaNativeBFFiniteFirstStructureMap.{u, v} R D I E) =
      (dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).map C E ≫
        eHomWhiskerRight SSet (dgKappaNativeBFFiniteFirstStructureMap.{u, v} R D I C)
          ((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj E) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _
    (pointedEnrichedMonicReplacementSourceTransformation
      (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
      (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
      (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I))
    (dgKappaNativeBFFiniteFirstStructureMap.{u, v} R D I)
    (pointedEnrichedMonicReplacementSourceTransformation_app
      (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
      (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
      (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I)) C E
  exact (congrArg (fun f => f ≫ eHomWhiskerLeft SSet
    ((dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I).obj C)
    (dgKappaNativeBFFiniteFirstStructureMap.{u, v} R D I E))
    (dgKappaNativeBFFiniteZeroSuspension_map.{u, v} R D I C E)).trans h

variable (r : ℕ) (S : DGKappaNativeBFFiniteStage.{u, v} R D I r)

/-- 概要：同じ正の実構造射は全 Hom に厳密に自然。
方針：元の同じ円柱押し出しの左比較自然性を使う。
規約：実際の前段の suspension を保持。使われ方：有限 BF 全列の構造自然性。 -/
lemma dgKappaNativeBFFiniteStepStructureMap_whisker
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S).map C E ≫
        eHomWhiskerLeft SSet
          ((dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S).obj C)
          (dgKappaNativeBFFiniteStepStructureMap.{u, v} R D I r S E) =
      (dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).map C E ≫
        eHomWhiskerRight SSet (dgKappaNativeBFFiniteStepStructureMap.{u, v} R D I r S C)
          ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj E) :=
  pointedEnrichedCylinderCompletionLeft_whisker
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r
      S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r) C E

end SerrePositivity.KST.SConstruction
