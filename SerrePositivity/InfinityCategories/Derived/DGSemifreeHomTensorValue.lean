module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomTensorInfinity
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve Opposite
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 同じ二入力 Hom の実半自由値・augmentation・頂点表示を照合する。 -/
def dgSemifreeDerivedHomTensorValue (P Q : SemifreeDGModules R D) :
    SemifreeDGModules R PUnit.{1} :=
  dgModuleOutputResolutionValue R
    (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D))
    PUnit.{1} (dgSemifreeHomTensorModuleDG R D) (op P, Q)
/-- 同じ二入力 Hom の実半自由値・augmentation・頂点表示を照合する。 -/
def dgSemifreeDerivedHomTensorAugmentation (P Q : SemifreeDGModules R D) :
    (dgSemifreeDerivedHomTensorValue R D P Q).val.obj (op PUnit.unit) ⟶
      moduleHom R D P.val Q.val :=
  (moduleEvaluation R PUnit.{1} PUnit.unit).map
    (dgModuleOutputResolutionAugmentation R
      (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D))
      PUnit.{1} (dgSemifreeHomTensorModuleDG R D) (op P, Q))
/-- 同じ実 Hom ∞ 関手の固定入力制限の全関手比較。 -/
lemma dgSemifreeDerivedHomTensorAugmentation_quasiIso (P Q : SemifreeDGModules R D) :
    QuasiIso (dgSemifreeDerivedHomTensorAugmentation R D P Q) :=
  dgModuleOutputResolutionAugmentation_quasiIso R
    (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D))
    PUnit.{1} (dgSemifreeHomTensorModuleDG R D) (op P, Q) PUnit.unit
/-- 同じ二入力 Hom の実半自由値・augmentation・頂点表示を照合する。 -/
lemma dgSemifreeDerivedHomTensorAugmentation_surjective (P Q : SemifreeDGModules R D) (n : ℤ) :
    Function.Surjective ((dgSemifreeDerivedHomTensorAugmentation R D P Q).f n) :=
  dgModuleOutputResolutionAugmentation_degree_surjective R
    (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D))
    PUnit.{1} (dgSemifreeHomTensorModuleDG R D) (op P, Q) PUnit.unit n
/-- 同じ二入力 Hom の実半自由値・augmentation・頂点表示を照合する。 -/
lemma dgSemifreeDerivedHomTensorInfinity_vertex (P Q : SemifreeDGModules R D) :
    (dgSemifreeDerivedHomTensorInfinity R D).app (op ⦋0⦌) (Simplex.vertex (op P, Q)) =
      Simplex.vertex ((dgUniverseLiftUp R (SemifreeDGModules R PUnit.{1})).obj
        (dgSemifreeDerivedHomTensorValue R D P Q)) :=
  dgModuleOutputResolutionInfinity_vertex R
    (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D))
    PUnit.{1} (dgSemifreeHomTensorModuleDG R D) (op P, Q)
end SerrePositivity.InfinityCategories
