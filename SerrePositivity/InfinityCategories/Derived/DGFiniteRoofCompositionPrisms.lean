module
public import SerrePositivity.InfinityCategories.Derived.DGFiniteRoofCompositeDiagram
public import SerrePositivity.InfinityCategories.Derived.DGFiniteOreTrianglePrisms

/-! # 有限実屋根合成の四つの実三角形族

概要：共通対角の内部二三角形と、合成分母・分子の外部二三角形を実 slice 内に保持する。
方針：実 Ore 比較の貼り合わせと閉合成・全次元 AW 合成の canonical prism を接続する。
規約：両入力の元図式への輸送は Ore データに保持する。使われ方：反転関手の合成評価。
-/
@[expose] public section
noncomputable section
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

/-- 両入力の同時細分と合成候補の分母・分子を結ぶ、指定全底付きの四実三角形族。 -/
structure DGFiniteRoofCompositionPrisms where
  oreTriangles : DGFiniteOreTrianglePrisms A D P R.ore
  first : SSet.Homotopy
    (pinchedHomCompositionFamily
        (SSet.const (pinchedClosedVertex A D R.ore.combinedDenominator)) R.first.coefficient ≫
      dgPinchedHomSlice A D R.ore.refinedSource y)
    (R.first.coefficient ≫ dgPinchedHomSlice A D
      (ForgetEnrichment.to (Complex A) R.first.denominator.obj.left) y)
  first_over : first.h ≫ sliceOverProjection _ =
    R.ore.firstTriangleHomotopy.h ≫ sliceOverProjection _
  denominator : SSet.Homotopy
    (SSet.const (pinchedClosedVertex A D R.compositeDenominator.obj.hom) ≫
      dgPinchedHomSlice A D R.ore.refinedSource x)
    (SSet.const (pinchedClosedVertex A D R.first.denominator.obj.hom) ≫ dgPinchedHomSlice A D
      (ForgetEnrichment.to (Complex A) R.first.denominator.obj.left) x)
  denominator_over : denominator.h ≫ sliceOverProjection _ =
    (dgClosedCompositionFamilyHomotopy A D K R.ore.combinedDenominator
      R.first.denominator.obj.hom).h ≫ sliceOverProjection _
  numerator : SSet.Homotopy (R.compositeNumerator ≫ dgPinchedHomSlice A D R.ore.refinedSource z)
    (R.second.coefficient ≫ dgPinchedHomSlice A D
      (ForgetEnrichment.to (Complex A) R.second.denominator.obj.left) z)
  numerator_over : numerator.h ≫ sliceOverProjection _ =
    (dgPinchedCompositionFamilyHomotopy A D R.ore.lift R.second.coefficient).h ≫
      sliceOverProjection _

/-- 任意の有限同時 Ore データから、同じ候補図式と全底を持つ四実三角形族を構成できる。 -/
theorem dgFiniteRoofCompositionPrisms_nonempty :
    Nonempty (DGFiniteRoofCompositionPrisms A D P x y z R) := by
  obtain ⟨C⟩ := dgFiniteOreTrianglePrisms_nonempty A D P R.ore
  exact ⟨{
    oreTriangles := C
    first := R.ore.firstTriangleHomotopy
    first_over := rfl
    denominator := dgClosedCompositionFamilyHomotopy A D K R.ore.combinedDenominator
      R.first.denominator.obj.hom
    denominator_over := rfl
    numerator := dgPinchedCompositionFamilyHomotopy A D R.ore.lift R.second.coefficient
    numerator_over := rfl }⟩

/-- 任意の有限実屋根二図式に、元の二輸送・合成候補・指定底付き四三角形族が存在する。 -/
theorem dgFiniteRoofCompositionPrisms_exists [K.Finite]
    (hP : DGQuotient.localKFlat A D P)
    (r : K ⟶ dgRoofCorrespondence A D P x y) (s : K ⟶ dgRoofCorrespondence A D P y z) :
    ∃ R : DGFiniteRoofOreData A D P x y z r s,
      Nonempty (DGFiniteRoofCompositionPrisms A D P x y z R) := by
  obtain ⟨R⟩ := dgFiniteRoofOreData_nonempty A D P x y z r s hP
  exact ⟨R, dgFiniteRoofCompositionPrisms_nonempty A D P x y z R⟩

end SerrePositivity.InfinityCategories
