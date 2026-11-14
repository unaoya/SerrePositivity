module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSemifreeHomTensorInfinity
/-!
概要：同じ二入力 Hom ∞ 関手の各頂点から、元の全 Hom end への全射準同型を回収する。
方針：同じ実分解の指定逆と augmentation を保ち、元の関手・値に照合する。
規約：始域は tensor dg 圏の nerve。元の直積上の二変数関手との比較は別工程。
使われ方：二変数導来 Hom の実出力分解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded Opposite
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 同じ二入力 Hom の実半自由値・augmentation・頂点表示を照合する。 -/
def dgSemifreeDerivedHomTensorValue (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R PUnit.{1} :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionValue R
    (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))
    PUnit.{1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTensorModuleDG R D) (_root_.Opposite.op P, Q)
/-- 同じ二入力 Hom の実半自由値・augmentation・頂点表示を照合する。 -/
def dgSemifreeDerivedHomTensorAugmentation (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (dgSemifreeDerivedHomTensorValue R D P Q).val.obj (_root_.Opposite.op PUnit.unit) ⟶
      _root_.SerrePositivity.DifferentialGraded.moduleHom R D P.val Q.val :=
  (_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R PUnit.{1} PUnit.unit).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation R
      (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))
      PUnit.{1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTensorModuleDG R D) (_root_.Opposite.op P, Q))
/-- 同じ実 Hom ∞ 関手の固定入力制限の全関手比較。 -/
lemma dgSemifreeDerivedHomTensorAugmentation_quasiIso (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    QuasiIso (dgSemifreeDerivedHomTensorAugmentation R D P Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation_quasiIso R
    (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))
    PUnit.{1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTensorModuleDG R D) (_root_.Opposite.op P, Q) PUnit.unit
/-- 同じ二入力 Hom の実半自由値・augmentation・頂点表示を照合する。 -/
lemma dgSemifreeDerivedHomTensorAugmentation_surjective (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (n : ℤ) :
    Function.Surjective ((dgSemifreeDerivedHomTensorAugmentation R D P Q).f n) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation_degree_surjective R
    (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))
    PUnit.{1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTensorModuleDG R D) (_root_.Opposite.op P, Q) PUnit.unit n
/-- 同じ二入力 Hom の実半自由値・augmentation・頂点表示を照合する。 -/
lemma dgSemifreeDerivedHomTensorInfinity_vertex (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity R D).app (_root_.Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.Opposite.op P, Q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R PUnit.{1})).obj
        (dgSemifreeDerivedHomTensorValue R D P Q)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity_vertex R
    (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))
    PUnit.{1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTensorModuleDG R D) (_root_.Opposite.op P, Q)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
