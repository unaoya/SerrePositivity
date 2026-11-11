module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCosliceYonedaPointedDisplay
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetTransportRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallStraighteningCounit
/-!
概要：同じ Hom 単位による空間値全関手を、元の F1 Yoneda 指定点評価と比較する。
方針：同じ実 coslice を表す二つの transport 表現を同じ可縮空間内で比較する。
規約：一つの全比較証人で分類図式と pointed 全空間の両方を比較する。
使われ方：D(R) 値 Hom と元の F1 Hom 関手族の全関手同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x : C)
/-- 同じ実 coslice の二表現を、同じ可縮な表現空間内で比較する実証人。 -/
def dgHomTargetSpaceComparisonWitness :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetTransportRepresentation R C x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaTransportRepresentation
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) := by
  have (n : SimplexCategoryᵒᵖ) : Small.{max (u + 1) v}
      (((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))).obj n) :=
    inferInstanceAs (Small.{max (u + 1) v} (ULift.{max (u + 1) v + 1}
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))).obj n)))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportRepresentationVertexIso.{max (u + 1) v} _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetTransportRepresentation R C x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaTransportRepresentation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
/-- 同じ比較証人から作る、Hom 基礎空間全関手と元の F1 Yoneda 評価の全関手同型。 -/
def dgHomTargetSpaceComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaSpaceInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetTransportRepresentation R C x).diagramIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaTransportRepresentation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
    (dgHomTargetSpaceComparisonWitness R C x)
/-- 同じ比較証人から作る、二つの実 pointed 全空間写像の全関手同型。 -/
def dgHomTargetPointedComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay R C x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaPointedDisplay (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetTransportRepresentation R C x).pointedIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaTransportRepresentation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
    (dgHomTargetSpaceComparisonWitness R C x)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetTransportRepresentation_pointedMap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaTransportRepresentation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointedTransportRepresentation_pointedMap] using e
end SerrePositivity.InfinityCategories.Project.DerivedCategories
