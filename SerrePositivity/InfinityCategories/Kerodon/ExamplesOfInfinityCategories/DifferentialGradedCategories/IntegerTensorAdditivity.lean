module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerTensorBifunctor

/-!
# 整数テンソル写像の有限和と符号

概要：整数テンソル写像の各変数の有限和と整数倍を明示する。
方針：各変数を加法群準同型に束ねる。
規約：KST Construction A.5、任意の加群の宇宙。
使われ方：AW の成分と全複体の交代境界和の接続。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
variable {M M' N N' : ModuleCat.{u} ℤ}

/-- 概要：第一因子が零の整数テンソル写像は零。
方針：純テンソルへの帰納法を使う。
規約：KST A.5。使われ方：境界和の加法的な展開。 -/
lemma integerTensorMap_zero_left (g : N ⟶ N') :
    integerTensorMap (0 : M ⟶ M') g = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
  · exact TensorProduct.zero_tmul _ _
  · simp only [map_add, hx, hy]

/-- 概要：第二因子が零の整数テンソル写像は零。
方針：純テンソルへの帰納法を使う。
規約：KST A.5。使われ方：境界和の加法的な展開。 -/
lemma integerTensorMap_zero_right (f : M ⟶ M') :
    integerTensorMap f (0 : N ⟶ N') = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
  · exact TensorProduct.tmul_zero _ _
  · simp only [map_add, hx, hy]

/-- 概要：整数テンソル写像は第一変数の加法群準同型。
方針：零保存と加法保存を束ねる。
規約：KST A.5。使われ方：有限和と交代符号の展開。 -/
def integerTensorMapLeftAddHom (g : N ⟶ N') :
    (M ⟶ M') →+ (integerTensor M N ⟶ integerTensor M' N') where
  toFun f := integerTensorMap f g
  map_zero' := integerTensorMap_zero_left g
  map_add' f f' := integerTensorMap_add_left f f' g

/-- 概要：整数テンソル写像は第二変数の加法群準同型。
方針：零保存と加法保存を束ねる。
規約：KST A.5。使われ方：有限和と交代符号の展開。 -/
def integerTensorMapRightAddHom (f : M ⟶ M') :
    (N ⟶ N') →+ (integerTensor M N ⟶ integerTensor M' N') where
  toFun g := integerTensorMap f g
  map_zero' := integerTensorMap_zero_right f
  map_add' g g' := integerTensorMap_add_right f g g'

/-- 概要：整数テンソル写像は第一変数の有限和を保つ。
方針：加法群準同型の有限和保存を使う。
規約：KST A.5。使われ方：第一因子の交代面写像の展開。 -/
lemma integerTensorMap_sum_left {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ M')) (g : N ⟶ N') :
    integerTensorMap (∑ i ∈ s, f i) g = ∑ i ∈ s, integerTensorMap (f i) g :=
  map_sum (integerTensorMapLeftAddHom g) f s

/-- 概要：整数テンソル写像は第二変数の有限和を保つ。
方針：加法群準同型の有限和保存を使う。
規約：KST A.5。使われ方：第二因子の交代面写像の展開。 -/
lemma integerTensorMap_sum_right {ι : Type*} (s : Finset ι) (f : M ⟶ M') (g : ι → (N ⟶ N')) :
    integerTensorMap f (∑ i ∈ s, g i) = ∑ i ∈ s, integerTensorMap f (g i) :=
  map_sum (integerTensorMapRightAddHom f) g s

/-- 概要：第一変数の整数倍はテンソル写像の整数倍に一致。
方針：加法群準同型の整数倍保存を使う。
規約：KST A.5。使われ方：交代境界の符号を和の外へ出す。 -/
lemma integerTensorMap_zsmul_left (a : ℤ) (f : M ⟶ M') (g : N ⟶ N') :
    integerTensorMap (a • f) g = a • integerTensorMap f g :=
  map_zsmul (integerTensorMapLeftAddHom g) a f

/-- 概要：第二変数の整数倍はテンソル写像の整数倍に一致。
方針：加法群準同型の整数倍保存を使う。
規約：KST A.5。使われ方：交代境界の符号を和の外へ出す。 -/
lemma integerTensorMap_zsmul_right (a : ℤ) (f : M ⟶ M') (g : N ⟶ N') :
    integerTensorMap f (a • g) = a • integerTensorMap f g :=
  map_zsmul (integerTensorMapRightAddHom f) a g

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
