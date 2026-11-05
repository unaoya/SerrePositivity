module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleRawFunctorEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommonComplexUniverseReverse
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomRawInputIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCoefficientInputs
/-!
概要：元の左右 Hom 複体の全入力上で導来二作用を元の二脚の作用へ厳密に照合する。
方針：任意対象宇宙の加群値関手評価と同じ Hom 模型同型の逆を適用する。
規約：追加仮定なしで元入力・全区間・端点輸送を保持する。
使われ方：正本標的と入力付き四座標標的の底の適合条件を同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
lemma dgGluingDerivedLeftCoefficientInput_raw_evaluation :
    intervalMappingUncurry (dgGluingDerivedLeftCoefficientInput R C D M X Y) =
    rightMappingSpacePrism _ ≫
      pinchedHomUncurry (dgGluingLaxHomLeftRawInputIso R C D M X Y).inv ≫
        dgGluingUniverseDerivedYoneda.{u,v,w} R C := by
  rw [dgGluingDerivedLeftCoefficientInput_uncurry, dgGluingNativeLeftCoefficientInput]
  simpa only [dgGluingLaxHomLeftRawInputIso, Iso.trans_inv,
    dgGluingCommonComplexUniverse_reverse, dgGluingUniverseDerivedYoneda,
    dgGluingUniverseYoneda, Category.assoc] using!
      dgGluingModuleRawFunctorEvaluation.{u,v,w,v} R C C (dgYoneda R C) X.left Y.left
lemma dgGluingDerivedRightCoefficientInput_raw_evaluation :
    intervalMappingUncurry (dgGluingDerivedRightCoefficientInput R C D M X Y) =
    rightMappingSpacePrism _ ≫
      pinchedHomUncurry (dgGluingLaxHomRightRawInputIso R C D M X Y).inv ≫
        dgGluingUniverseDerivedCoefficient R C D M := by
  rw [dgGluingDerivedRightCoefficientInput_uncurry, dgGluingNativeRightCoefficientInput]
  simpa only [dgGluingLaxHomRightRawInputIso, Iso.trans_inv,
    dgGluingCommonComplexUniverse_reverse, dgGluingUniverseDerivedCoefficient,
    dgGluingUniverseCoefficient, Category.assoc] using!
      dgGluingModuleRawFunctorEvaluation.{u,v,w,w} R C D M.toFunctor X.right Y.right
end SerrePositivity.InfinityCategories
