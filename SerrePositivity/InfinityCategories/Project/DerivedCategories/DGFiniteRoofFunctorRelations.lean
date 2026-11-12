module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedFamilyComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofCompositionPrisms

/-!
概要：実屋根の四三角形族を、同じパラメータ関手圏の四合成関係へ移す。
方針：共通対角と全射影を保持する slice 比較を使う。
規約：与えられた全パラメータ図式を変えない。使われ方：任意標的への屋根評価の合成。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D) (x y z : D) {K : SSet.{max u v}}
variable {r : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y}
variable {s : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P y z}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofOreData A D P x y z r s)
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofCompositionPrisms A D P x y z R)
include C
/-- 同時細分の第一三角形は、同じ共通対角への合成を表す。 -/
lemma dgFiniteRoofFunctor_first :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.ore.combinedDenominator)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D R.first.coefficient =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily
          (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.ore.combinedDenominator))
          R.first.coefficient) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom_comp_of_sliceHomotopy A D _ _ _ C.first
  exact C.first_over.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy_over A D _ _)
/-- 第二三角形も同じ共通対角への合成を表す。 -/
lemma dgFiniteRoofFunctor_second :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D R.ore.lift ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D
        (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.second.denominator.obj.hom)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily
          (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.ore.combinedDenominator))
          R.first.coefficient) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom_comp_of_sliceHomotopy A D _ _ _ C.oreTriangles.second
  exact C.oreTriangles.second_over.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy_over A D _ _)
/-- 合成分母の実三角形族は、同じ定値関手間の分母の合成を表す。 -/
lemma dgFiniteRoofFunctor_denominator :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.ore.combinedDenominator)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D
        (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.first.denominator.obj.hom)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (X := K)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.compositeDenominator.obj.hom)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom_comp_of_sliceHomotopy A D _ _ _ C.denominator
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy_over A D
    (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.ore.combinedDenominator))
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.first.denominator.obj.hom))
  exact C.denominator_over.trans h
/-- 合成分子の実三角形族は、同じパラメータ関手圏の分子の合成を表す。 -/
lemma dgFiniteRoofFunctor_numerator :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D R.ore.lift ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D R.second.coefficient =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D R.compositeNumerator := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom_comp_of_sliceHomotopy A D _ _ _ C.numerator
  exact C.numerator_over.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy_over A D _ _)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
