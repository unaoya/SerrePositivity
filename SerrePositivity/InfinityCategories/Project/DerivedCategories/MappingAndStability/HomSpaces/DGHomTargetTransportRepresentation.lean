module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGPointedTransportRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGHomTargetPointedFiberEquivalence
/-!
概要：同じ Hom 単位の実 pointed 表示を、元の coslice 射影の実 transport 表現にする。
方針：構成済みの全実 fiber 同値を用い、同じ全関手・同じ全空間写像を保持する。
規約：入力の小ささも出力の射影性も不要。使われ方：F1 Hom 関手族との全分類比較。
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
/-- 同じ実 Hom 単位の全単体表示から作る、元の coslice の実 transport 表現。 -/
def dgHomTargetTransportRepresentation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointedTransportRepresentation _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay R C x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay_projection R C x) (by
      rintro ⟨b⟩
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence R C x b)
/-- 同じ実表現の分類図式は、元の同じ Hom 基礎空間関手。 -/
lemma dgHomTargetTransportRepresentation_diagram :
    (dgHomTargetTransportRepresentation R C x).diagram =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x := rfl
/-- 同じ実表現の全空間側の写像は、元の同じ Hom 単位の pointed 表示。 -/
lemma dgHomTargetTransportRepresentation_pointedMap :
    (dgHomTargetTransportRepresentation R C x).pointedMap =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay R C x := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointedTransportRepresentation_pointedMap _ _ _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
