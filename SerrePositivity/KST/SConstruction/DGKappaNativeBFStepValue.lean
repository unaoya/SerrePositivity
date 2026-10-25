module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFStepInput
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFStage
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderCompletionNaturality
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderCompletionProperties

/-!
概要：同じ有限 native 入力上で、実際の前段の suspension を使う次 BF 段を作る。
方針：元の実 span の左脚を前段へ延長し、同じ全族円柱押し出しと Ex∞ を適用する。
規約：元の正段で前段を代用しない。使われ方：同じ四辺と二胞体の同時再帰。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories NonConnective
open Spectra SimplicialModel
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (r : ℕ)
  (S : DGKappaNativeBFFiniteStage.{u, v} R D I r)

/-- 概要：同じ実際の前段の suspension を左標的にする。
方針：同じ実段関手を元の円で suspension する。
規約：前段の実値を保持。使われ方：有限 BF 次段の左標的。 -/
def dgKappaNativeBFFiniteStepLeftTargetFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedSSetObject.{max (u + 1) v} :=
  S.functor.comp SSet (pointedTensorEnrichedFunctor PointedSimplicialSet.circle)

/-- 概要：同じ実 span の円柱押し出しから得る次の実 Kan BF 段。
方針：実際の前段へ延長した元の左脚と同じ右脚を一般構成へ渡す。
規約：全 Hom を保持。使われ方：有限 BF 再帰の次段。 -/
def dgKappaNativeBFFiniteStepFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedSSetObject.{max (u + 1) v} :=
  pointedEnrichedCylinderCompletionFunctor
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r
      S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r)

/-- 概要：同じ実際の前段から次段への suspension 構造射。
方針：元の同じ円柱押し出しの左比較を使う。
規約：元の実構造射を保持。使われ方：有限 BF 列の正の構造射。 -/
def dgKappaNativeBFFiniteStepStructureMap (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S).obj C ⟶
      (dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C :=
  pointedEnrichedCylinderCompletionLeft
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r
      S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r) C

/-- 概要：同じ元の隣接正段から次の実 BF 段への前向き比較。
方針：元の同じ円柱押し出しの右比較を使う。
規約：元の正段を保持。使われ方：有限 BF 再帰の次の比較。 -/
def dgKappaNativeBFFiniteStepComparison (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C ⟶
      (dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C :=
  pointedEnrichedCylinderCompletionRight
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r
      S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r) C

/-- 概要：同じ実次段の Kan 性。
方針：元の実押し出しへの同じ Ex∞ の Kan 性を使う。
規約：追加仮定なし。使われ方：有限 BF 再帰の次段不変条件。 -/
lemma dgKappaNativeBFFiniteStep_kanComplex (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj).right :=
  pointedEnrichedCylinderCompletion_kanComplex
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r
      S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r) C

/-- 概要：同じ正の構造射は基礎単体集合上で単射。
方針：元の円柱押し出しの左比較の単射性を使う。
規約：実際の前段の suspension を始域に持つ。使われ方：有限 BF 列の構造条件。 -/
lemma dgKappaNativeBFFiniteStepStructureMap_mono
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    Mono (show ((dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S).obj C).obj ⟶
      ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj from
        dgKappaNativeBFFiniteStepStructureMap.{u, v} R D I r S C).right :=
  pointedEnrichedCylinderCompletionLeft_mono
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r
      S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r) C

/-- 概要：同じ次段比較は全 Hom に厳密に自然。
方針：元の同じ右比較の全族自然性を使う。
規約：全二胞体を保持。使われ方：有限 BF 再帰の次の比較自然性。 -/
lemma dgKappaNativeBFFiniteStepComparison_whisker
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).map C E ≫
        eHomWhiskerLeft SSet
          ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C)
          (dgKappaNativeBFFiniteStepComparison.{u, v} R D I r S E) =
      (dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).map C E ≫
        eHomWhiskerRight SSet (dgKappaNativeBFFiniteStepComparison.{u, v} R D I r S C)
          ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj E) :=
  pointedEnrichedCylinderCompletionRight_whisker
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r
      S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r) C E

end SerrePositivity.KST.SConstruction
