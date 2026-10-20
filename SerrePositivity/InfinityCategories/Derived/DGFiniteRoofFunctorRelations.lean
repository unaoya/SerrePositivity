module
public import SerrePositivity.InfinityCategories.Derived.DGPinchedFamilyComposition
public import SerrePositivity.InfinityCategories.Derived.DGFiniteRoofCompositionPrisms

/-!
概要：実屋根の四三角形族を、同じパラメータ関手圏の四合成関係へ移す。
方針：共通対角と全射影を保持する slice 比較を使う。
規約：与えられた全パラメータ図式を変えない。使われ方：任意標的への屋根評価の合成。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D] (P : Set D) (x y z : D) {K : SSet.{max u v}}
variable {r : K ⟶ dgRoofCorrespondence A D P x y}
variable {s : K ⟶ dgRoofCorrespondence A D P y z}
variable (R : DGFiniteRoofOreData A D P x y z r s)
variable (C : DGFiniteRoofCompositionPrisms A D P x y z R)
include C
/-- 同時細分の第一三角形は、同じ共通対角への合成を表す。 -/
lemma dgFiniteRoofFunctor_first :
    dgPinchedFamilyHom A D
      (SSet.const (X := K) (pinchedClosedVertex A D R.ore.combinedDenominator)) ≫
      dgPinchedFamilyHom A D R.first.coefficient =
        dgPinchedFamilyHom A D (pinchedHomCompositionFamily
          (SSet.const (pinchedClosedVertex A D R.ore.combinedDenominator))
          R.first.coefficient) := by
  apply dgPinchedFamilyHom_comp_of_sliceHomotopy A D _ _ _ C.first
  exact C.first_over.trans (dgPinchedCompositionFamilyHomotopy_over A D _ _)
/-- 第二三角形も同じ共通対角への合成を表す。 -/
lemma dgFiniteRoofFunctor_second :
    dgPinchedFamilyHom A D R.ore.lift ≫
      dgPinchedFamilyHom A D
        (SSet.const (X := K) (pinchedClosedVertex A D R.second.denominator.obj.hom)) =
        dgPinchedFamilyHom A D (pinchedHomCompositionFamily
          (SSet.const (pinchedClosedVertex A D R.ore.combinedDenominator))
          R.first.coefficient) := by
  apply dgPinchedFamilyHom_comp_of_sliceHomotopy A D _ _ _ C.oreTriangles.second
  exact C.oreTriangles.second_over.trans (dgPinchedCompositionFamilyHomotopy_over A D _ _)
/-- 合成分母の実三角形族は、同じ定値関手間の分母の合成を表す。 -/
lemma dgFiniteRoofFunctor_denominator :
    dgPinchedFamilyHom A D
      (SSet.const (X := K) (pinchedClosedVertex A D R.ore.combinedDenominator)) ≫
      dgPinchedFamilyHom A D
        (SSet.const (X := K) (pinchedClosedVertex A D R.first.denominator.obj.hom)) =
        dgPinchedFamilyHom A D (SSet.const (X := K)
          (pinchedClosedVertex A D R.compositeDenominator.obj.hom)) := by
  apply dgPinchedFamilyHom_comp_of_sliceHomotopy A D _ _ _ C.denominator
  have h := dgPinchedCompositionFamilyHomotopy_over A D
    (SSet.const (X := K) (pinchedClosedVertex A D R.ore.combinedDenominator))
    (SSet.const (pinchedClosedVertex A D R.first.denominator.obj.hom))
  exact C.denominator_over.trans h
/-- 合成分子の実三角形族は、同じパラメータ関手圏の分子の合成を表す。 -/
lemma dgFiniteRoofFunctor_numerator :
    dgPinchedFamilyHom A D R.ore.lift ≫ dgPinchedFamilyHom A D R.second.coefficient =
      dgPinchedFamilyHom A D R.compositeNumerator := by
  apply dgPinchedFamilyHom_comp_of_sliceHomotopy A D _ _ _ C.numerator
  exact C.numerator_over.trans (dgPinchedCompositionFamilyHomotopy_over A D _ _)
end SerrePositivity.InfinityCategories
