module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedTensor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexPairOperationNaturality

/-!
# 第二因子が自由な整数テンソルからの降下写像

概要：第二因子の各基底に第一因子からの線形写像を指定してテンソルからの射を作る。
方針：自由加群の lift を二変数線形写像に反転し、テンソルの普遍性を使う。
規約：KST Definition A.3、Construction A.5、任意の宇宙。
使われ方：鎖区間の頂点と辺上でホモトピーを評価する写像。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory

/-- 概要：第二因子の各自由基底に指定された線形写像からテンソル射を作る。
方針：Finsupp の lift と TensorProduct の lift を合成する。
規約：KST A.3・A.5、第一因子の自由性を仮定しない。
使われ方：Moore 複体の任意の加群と鎖区間のテンソルの評価。 -/
def integerTensorFreeDesc {M N : ModuleCat.{u} ℤ} {X : Type u} (F : X → (M ⟶ N)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X) ⟶ N :=
  by
    letI : Module ℤ M := M.isModule
    letI : Module ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X) := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X).isModule
    let φ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X) →+ (M →+ N) :=
      (Finsupp.lift (M →+ N) ℤ X (fun x ↦ (F x).hom.toAddMonoidHom)).toAddMonoidHom
    let ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X) →+ N :=
      TensorProduct.liftAddHom φ.flip (fun a m z ↦ by
        simp only [AddMonoidHom.flip_apply]
        rw [map_zsmul, AddMonoidHom.zsmul_apply]
        letI : Module ℤ N := AddCommGroup.toIntModule N
        exact map_intCast_smul (φ z) ℤ ℤ a m)
    letI : Module ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X)) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X)).isModule
    letI : Module ℤ N := N.isModule
    exact ModuleCat.ofHom
      { toFun := ψ
        map_add' := ψ.map_add
        map_smul' := fun a z ↦ map_intCast_smul ψ ℤ ℤ a z }


/-- 概要：降下したテンソル射は第二因子の基底上で指定された線形写像に一致。
方針：二つの線形 lift の基底上の評価公式を使う。
規約：KST A.3・A.5。使われ方：区間の両端と辺の実計算。 -/
@[simp] lemma integerTensorFreeDesc_generator {M N : ModuleCat.{u} ℤ} {X : Type u}
    (F : X → (M ⟶ N)) (m : M) (x : X) :
    integerTensorFreeDesc F (TensorProduct.tmul ℤ m (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = F x m := by
  change ((Finsupp.lift (M →+ N) ℤ X (fun x ↦ (F x).hom.toAddMonoidHom))
    (Finsupp.single x 1)) m = _
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  · rw [one_smul]
    rfl
  · exact zero_smul ℤ _

/-- 概要：第二因子が自由なテンソルからの射は基底との純テンソル上で決定する。
方針：第一因子の元を固定し、第二因子に関する自由加群の外延性を使う。
規約：KST A.3・A.5。使われ方：区間の全テンソルの評価写像の等式。 -/
lemma integerTensor_free_hom_ext {M N : ModuleCat.{u} ℤ} {X : Type u}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X) ⟶ N}
    (h : ∀ m x, f (TensorProduct.tmul ℤ m (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) =
      g (TensorProduct.tmul ℤ m (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))) : f = g := by
  letI : Module ℤ M := M.isModule
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_pure_hom_ext
  intro m z
  induction z using Finsupp.induction_linear with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | single x a =>
    rw [← Finsupp.smul_single_one]
    have ht : TensorProduct.tmul ℤ m (a • _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) =
        a • TensorProduct.tmul ℤ m (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) :=
      ((TensorProduct.mk ℤ M (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X) m).toAddMonoidHom).map_zsmul a _
    change f (TensorProduct.tmul ℤ m (a • _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) =
      g (TensorProduct.tmul ℤ m (a • _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
    rw [ht]
    simpa only [map_zsmul] using congrArg (fun z ↦ a • z) (h m x)

end SerrePositivity.KST.ProExcision
