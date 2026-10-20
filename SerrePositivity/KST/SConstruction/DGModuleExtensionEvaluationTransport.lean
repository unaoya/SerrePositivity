module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionComposition
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation

/-! # tensor の元の評価を加群対象の評価へ移す
概要：任意の左パラメータの値で、元の tensor 射と結合同型を回収する。
方針：右端の双加群はその対象値だけで決まることを、元の構成子で照合する。
規約：左パラメータの smallness は要求しない。使われ方：実延長の三重比較の評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z q
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の graph tensor 関手の射作用は、同じ恒等加群との tensor 射。 -/
lemma dgModuleGraphTensorFunctor_map (D : Type v) (T : Type w)
    [DGCategory A D] [Small.{u} D] [DGCategory A T] [Small.{u} T]
    {P P' : BimoduleCategory A T D} (f : P ⟶ P') :
    (dgModuleGraphTensorFunctor A D T).map f =
      BimoduleTensor.composeMap A T D (RightModule A D) f
        (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id _))) := rfl

/-- 後因子の恒等射を評価すると、同じ元の加群対象との tensor 作用となる。 -/
lemma dgTensor_first_value_evaluation (B : Type v) (D : Type w) (E : Type z)
    [DGCategory A B] [Small.{u} B] [DGCategory A D] [Small.{u} D] [DGCategory A E]
    {P P' : BimoduleCategory A B D} (f : P ⟶ P') (R : Bimodule A D E) (b : B) (e : E) :
    BimoduleTensor.composeValueMap A B D E f (𝟙 (BimoduleCategory.of A D E R)) b e =
      BimoduleTensor.composeValueMap A B D (RightModule A D) f
        (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id _))) b (R.obj e) := by
  simp only [BimoduleTensor.composeValueMap, CategoryTheory.Functor.map_id]
  rfl

/-- 元の結合同型の各値は、後因子を同じ元の加群対象で評価した結合同型。 -/
lemma dgTensor_associator_value_evaluation (B : Type v) (D : Type w) (E : Type z)
    (F : Type q) [DGCategory A B] [Small.{u} B] [DGCategory A D] [Small.{u} D]
    [DGCategory A E] [Small.{u} E] [DGCategory A F]
    (P : Bimodule A B D) (Q : Bimodule A D E) (R : Bimodule A E F) (b : B) (f : F) :
    BimoduleTensor.associatorValueIso A B D E F P Q R b f =
      BimoduleTensor.associatorValueIso A B D E (RightModule A E) P Q (DGFunctor.id _)
        b (R.obj f) := by
  unfold BimoduleTensor.associatorValueIso
  rfl

end SerrePositivity.KST.SConstruction
