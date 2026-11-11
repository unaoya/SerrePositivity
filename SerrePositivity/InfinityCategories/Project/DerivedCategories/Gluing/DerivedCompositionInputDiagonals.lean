module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedCompositionInputLifts
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedCompositionDiagonalPath

/-! 入力付き合成対応の対角は、元の同じ二合成対角を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedFirstCompositionInputDiagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  pullback.fst
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.right))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedRightCoefficientInput R C D M X Y) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionDiagonal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.right)))

def dgGluingDerivedLastCompositionInputDiagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  pullback.fst
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLeftCoefficientInput R C D M X Y) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y)

lemma dgGluingHomDerivedFirstCompositionInputLift_diagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y := by
  rw [dgGluingDerivedFirstCompositionInputDiagonal, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift_composition R C D M X Y]
  rfl

lemma dgGluingHomDerivedLastCompositionInputLift_diagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift R C D M X Y ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionDiagonal R C D M X Y := by
  rw [dgGluingDerivedLastCompositionInputDiagonal, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift_composition R C D M X Y]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
