module

public import SerrePositivity.InfinityCategories.F2.Presentable.LeftHornCellStep
public import SerrePositivity.InfinityCategories.F2.Presentable.OverLeftAnodyneCopies

/-!
概要：底上の左ホーンの一段の付加の単位は、全空間で左アノダインである。
方針：全左ホーンのコピーの余積と、その評価射に沿う pushout で閉性を使う。
規約：元の具体的な単位を判定し、底の quasicategory 性を要求しない。
使われ方：可算反復の単位の左アノダイン性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 底上の全左ホーンのコピーの境界は、全空間で左アノダイン。 -/
lemma leftHornCopiesBoundary_leftAnodyne {B : SSet.{u}} (X : Over B) :
    leftAnodyneExtensions ((leftHornCopiesBoundary B).app X).left := by
  have h : ((leftAnodyneExtensions.inverseImage (Over.forget B)).functorCategory (Over B))
      (leftHornCopiesBoundary B) := by
    change ((leftAnodyneExtensions.inverseImage (Over.forget B)).functorCategory (Over B))
      (colimMap (Discrete.natTrans
        (F := Discrete.functor (fun h : LeftHornCellIndex B ↦
          overCellCopiesFunctor (leftHornCellSource h) (leftHornCellSource h)))
        (G := Discrete.functor (fun h : LeftHornCellIndex B ↦
          overCellCopiesFunctor (leftHornCellSource h) (leftHornCellTarget h)))
        (fun h ↦ overCellCopiesMap (leftHornCellSource h.as) (leftHornCellArrow h.as))))
    apply MorphismProperty.colimMap
    intro h X
    exact overCellCopiesMap_leftAnodyne _ _
      (leftAnodyneExtensions_horn h.as.2.1.val h.as.2.1.property) X
  exact h X

/-- 底上の具体的な一段の単位は、全空間で左アノダイン。 -/
lemma leftHornCellStepUnit_leftAnodyne {B : SSet.{u}} (X : Over B) :
    leftAnodyneExtensions ((leftHornCellStepUnit B).app X).left := by
  have h := (IsPushout.of_hasPushout (leftHornCopiesEvaluation B)
    (leftHornCopiesBoundary B)).map ((evaluation (Over B) (Over B)).obj X)
  exact leftAnodyneExtensions.of_isPushout (h.map (Over.forget B))
    (leftHornCopiesBoundary_leftAnodyne X)

end SerrePositivity.InfinityCategories.F2.Presentable
