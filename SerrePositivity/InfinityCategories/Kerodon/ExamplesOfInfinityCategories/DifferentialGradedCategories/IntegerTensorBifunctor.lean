module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedTensor
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# 任意の宇宙の整数加群のテンソル双関手

概要：整数加群の明示的なテンソルを加法的な双関手として束ねる。
方針：両変数の射を TensorProduct.map で送り、通常の全複体に適用する。
規約：KST Construction A.5 の正規化テンソル。環 ℤ と加群の宇宙を独立に扱うため、
ModuleCat の同宇宙の monoidal インスタンスを要求しない。
使われ方：正規化 Moore 複体の ℕ 次数の全テンソルと AW/shuffle の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory

/-- 概要：整数テンソル写像の合成則。
方針：純テンソルへの帰納法で評価する。規約：KST A.5、任意の宇宙。
使われ方：双関手の自然性と合成則。 -/
lemma integerTensorMap_comp {M M' M'' N N' N'' : ModuleCat.{u} ℤ}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    integerTensorMap (f ≫ f') (g ≫ g') = integerTensorMap f g ≫ integerTensorMap f' g' := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
  · rfl
  · simp only [map_add, hx, hy]

/-- 概要：二つの恒等写像の整数テンソルは恒等写像。
方針：純テンソルへの帰納法で評価する。規約：KST A.5。
使われ方：双関手の恒等則。 -/
lemma integerTensorMap_id (M N : ModuleCat.{u} ℤ) :
    integerTensorMap (𝟙 M) (𝟙 N) = 𝟙 (integerTensor M N) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
  · rfl
  · simp only [map_add, hx, hy]

/-- 概要：整数テンソル写像の第一変数の加法性。
方針：純テンソルで双線形性を評価する。規約：KST A.5。
使われ方：差のテンソルの展開。 -/
lemma integerTensorMap_add_left {M M' N N' : ModuleCat.{u} ℤ}
    (f f' : M ⟶ M') (g : N ⟶ N') :
    integerTensorMap (f + f') g = integerTensorMap f g + integerTensorMap f' g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
  · exact TensorProduct.add_tmul _ _ _
  · simp only [map_add, hx, hy]

/-- 概要：整数テンソル写像の第二変数の加法性。
方針：純テンソルで双線形性を評価する。規約：KST A.5。
使われ方：差のテンソルの展開。 -/
lemma integerTensorMap_add_right {M M' N N' : ModuleCat.{u} ℤ}
    (f : M ⟶ M') (g g' : N ⟶ N') :
    integerTensorMap f (g + g') = integerTensorMap f g + integerTensorMap f g' := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
  · exact TensorProduct.tmul_add _ _ _
  · simp only [map_add, hx, hy]

/-- 概要：整数加群の第二変数のテンソル関手。
方針：第一変数の写像を恒等に固定する。
規約：KST A.5、加群の宇宙は任意。使われ方：テンソル双関手の対象部分。 -/
def integerTensorRight (M : ModuleCat.{u} ℤ) : ModuleCat.{u} ℤ ⥤ ModuleCat.{u} ℤ where
  obj N := integerTensor M N
  map f := integerTensorMap (𝟙 M) f
  map_id N := integerTensorMap_id M N
  map_comp f g := by
    simpa only [Category.id_comp] using integerTensorMap_comp (𝟙 M) (𝟙 M) f g

/-- 概要：第二変数のテンソル関手は加法的。
方針：TensorProduct.map の第二変数の加法性を使う。
規約：KST A.5。使われ方：全複体の微分と射の加減法。 -/
instance integerTensorRight_additive (M : ModuleCat.{u} ℤ) :
    (integerTensorRight M).Additive where
  map_add {_X _Y f g} := integerTensorMap_add_right (𝟙 M) f g

/-- 概要：整数加群のテンソル双関手。
方針：第一変数の写像には第二変数の恒等写像をテンソルする。
規約：KST A.5、任意の加群の宇宙。
使われ方：Mathlib の通常の全複体構成へ渡す。 -/
def integerTensorBifunctor : ModuleCat.{u} ℤ ⥤ ModuleCat.{u} ℤ ⥤ ModuleCat.{u} ℤ where
  obj := integerTensorRight
  map f :=
    { app N := integerTensorMap f (𝟙 N)
      naturality N N' g := by
        change integerTensorMap (𝟙 _) g ≫ integerTensorMap f (𝟙 _) =
          integerTensorMap f (𝟙 _) ≫ integerTensorMap (𝟙 _) g
        rw [← integerTensorMap_comp, ← integerTensorMap_comp]
        simp only [Category.id_comp, Category.comp_id] }
  map_id _ := by
    apply NatTrans.ext
    funext N
    exact integerTensorMap_id _ _
  map_comp f g := by
    apply NatTrans.ext
    funext N
    change integerTensorMap (f ≫ g) (𝟙 N) =
      integerTensorMap f (𝟙 N) ≫ integerTensorMap g (𝟙 N)
    simpa only [Category.id_comp] using integerTensorMap_comp f g (𝟙 N) (𝟙 N)

/-- 概要：整数テンソル双関手は第一変数でも加法的。
方針：TensorProduct.map の第一変数の加法性を使う。
規約：KST A.5。使われ方：差のテンソルの全複体における双線形展開。 -/
instance integerTensorBifunctor_additive : integerTensorBifunctor.{u}.Additive where
  map_add {_X _Y f g} := by
    apply NatTrans.ext
    funext N
    change integerTensorMap (f + g) (𝟙 N) =
      integerTensorMap f (𝟙 N) + integerTensorMap g (𝟙 N)
    exact integerTensorMap_add_left f g (𝟙 N)

/-- 概要：整数テンソル双関手の各対象関手の加法性。
方針：第二変数の関手の加法性を明示的に公開する。
規約：KST A.5。使われ方：全複体の双関手に必要な零射保存の推論。 -/
instance integerTensorBifunctor_obj_additive (M : ModuleCat.{u} ℤ) :
    (integerTensorBifunctor.obj M).Additive := integerTensorRight_additive M

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

