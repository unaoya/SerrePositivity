module
public import SerrePositivity.KST.SConstruction.PointedStandardLoop
public import SerrePositivity.KST.SConstruction.PointedTensorEnrichedFunctor
public import SerrePositivity.KST.SConstruction.SuspensionLoopEnrichedPostcomposition
public import SerrePositivity.KST.SConstruction.PointedSSetWhisker

/-! # 同じ標準点つき loop の評価の全 Hom 自然性
概要：元の余単位 ΣΩX→X は、全 basedHom 入力に厳密に自然。
方針：元の逆随伴の因子分解と loop 作用の uncurry を合成する。
規約：元の circle と評価を変えない。使われ方：BF 最初の構造射の単射置換。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra

/-- 同じ元の loop を suspension した標準点つき厳密豊穣関手。 -/
def pointedStandardSuspensionLoopFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} :=
  pointedStandardLoopEnrichedFunctor.comp SSet
    (pointedTensorEnrichedFunctor PointedSimplicialSet.circle)

/-- 同じ元の余単位を、標準点つき対象の射として保持する。 -/
def pointedStandardLoopEvaluation (X : PointedSSetObject.{u}) :
    pointedStandardSuspensionLoopFunctor.obj X ⟶ X :=
  (ihom.ev PointedSimplicialSet.circle.{u}).app X.obj

/-- 元の全 loop・tensor Hom 作用は、同じ評価への前後合成と可換。 -/
lemma pointedStandardLoopEvaluation_closed (X Y : PointedSimplicialSet.{u}) :
    (pointedLoopHom X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map PointedSimplicialSet.circle
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X))).map
          ((ihom.ev PointedSimplicialSet.circle.{u}).app Y) =
      (MonoidalClosed.pre ((ihom.ev PointedSimplicialSet.circle.{u}).app X)).app Y := by
  have h := pointedLoopHom_uncurry X Y
  rw [suspensionLoopPointedMappingIso_inv_factor] at h
  exact (Category.assoc _ _ _).trans h

/-- 同じ元の評価は、標準 basedHom の全高次入力に厳密に自然。 -/
lemma pointedStandardLoopEvaluation_whisker (X Y : PointedSSetObject.{u}) :
    pointedStandardSuspensionLoopFunctor.map X Y ≫
        eHomWhiskerLeft SSet (pointedStandardSuspensionLoopFunctor.obj X)
          (pointedStandardLoopEvaluation Y) =
      eHomWhiskerRight SSet (pointedStandardLoopEvaluation X) Y := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  have h := congrArg Under.Hom.right (pointedStandardLoopEvaluation_closed X.obj Y.obj)
  exact h.trans (congrArg Under.Hom.right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre
      ((ihom.ev PointedSimplicialSet.circle.{u}).app X.obj) Y.obj)).symm

end SerrePositivity.KST.SConstruction
