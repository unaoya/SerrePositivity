module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingPinchedFamilyEvaluation

/-!
概要：任意の有限二屋根図式に、任意標的の実三評価族と実合成三角形を供給する。
方針：同時 Ore 細分と指定全底付き四三角形族を評価し、全パラメータの実 Hom へ戻す。
規約：入力への輸送と合成候補を保持する。使われ方：全選択空間上の合成整合性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D] (P : Set D) (x y z : D)
variable {K : SSet.{max u v}} {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y)
variable (r : K ⟶ dgRoofCorrespondence A D P x y)
variable (s : K ⟶ dgRoofCorrespondence A D P y z)
/-- 任意標的の三実評価族と実合成三角形を持つ、入力への二輸送付きの同時細分。 -/
structure DGInvertingFiniteRoofComposition where
  source : DGFiniteRoofOreData A D P x y z r s
  prisms : DGFiniteRoofCompositionPrisms A D P x y z source
  first : DGInvertingPinchedFamilyEvaluation A D F
    source.first.denominator.obj.hom source.first.coefficient
  second : DGInvertingPinchedFamilyEvaluation A D F
    source.second.denominator.obj.hom source.second.coefficient
  composite : DGInvertingPinchedFamilyEvaluation A D F
    source.compositeDenominator.obj.hom source.compositeNumerator
  triangle : Truncated.Edge.CompStruct
    (intervalFamilyEdge (first.value ≫ pinchedHomToIntervalMappingSpace _ _))
    (intervalFamilyEdge (second.value ≫ pinchedHomToIntervalMappingSpace _ _))
    (intervalFamilyEdge (composite.value ≫ pinchedHomToIntervalMappingSpace _ _))
/-- 任意の有限二屋根図式は、任意の反転関手の下で全パラメータの実合成評価を持つ。 -/
theorem dgInvertingFiniteRoofComposition_nonempty [K.Finite] [Quasicategory Y]
    (hP : DGQuotient.localKFlat A D P) (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    Nonempty (DGInvertingFiniteRoofComposition A D P x y z F r s) := by
  obtain ⟨R, ⟨C⟩⟩ := dgFiniteRoofCompositionPrisms_exists A D P x y z hP r s
  obtain ⟨er⟩ := dgInvertingPinchedFamilyEvaluation_nonempty A D F P hF
    R.first.denominator.obj.hom R.first.denominator.property R.first.coefficient
  obtain ⟨es⟩ := dgInvertingPinchedFamilyEvaluation_nonempty A D F P hF
    R.second.denominator.obj.hom R.second.denominator.property R.second.coefficient
  obtain ⟨ec⟩ := dgInvertingPinchedFamilyEvaluation_nonempty A D F P hF
    R.compositeDenominator.obj.hom R.compositeDenominator.property R.compositeNumerator
  obtain ⟨T⟩ := dgInvertingPinchedFamilyEvaluation_compositionTriangle_nonempty
    A D F P x y z R C hF er es ec
  exact ⟨⟨R, C, er, es, ec, T⟩⟩
end SerrePositivity.InfinityCategories
