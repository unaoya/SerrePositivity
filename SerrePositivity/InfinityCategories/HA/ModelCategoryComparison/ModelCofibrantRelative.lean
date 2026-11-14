module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：任意モデル圏の元の cofibrant 全部分圏を同じ宇宙の相対圏に束ねる。
方針：対象と Hom の宇宙を AsSmall で揃え、元の弱同値を引き戻す。
規約：対象の cofibrancy 以外の条件や単体集合のモデル構造は追加しない。
使われ方：一般モデル圏の hammock 局所化と実 right frame の比較。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
open _root_.CategoryTheory _root_.HomotopicalAlgebra
variable (C : Type u) [Category.{v} C] [ModelCategory C]

/-- 概要：元の cofibrant 対象の全部分圏の宇宙を揃える。
方針：元の対象と射の AsSmall 表示を使う。
規約：新しいモデル構造は置かない。使われ方：DK 相対圏の底の圏。 -/
abbrev modelCofibrantCategory := AsSmall.{max u v} (CofibrantObject C)

/-- 概要：元のモデル圏への同じ cofibrant 包含。
方針：宇宙の包みを外し、元の全部分圏の包含を合成する。
規約：元の射と対象を保持。使われ方：弱同値と元の局所化射の照合。 -/
def modelCofibrantInclusion : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantCategory C ⥤ C :=
  AsSmall.down ⋙ CofibrantObject.ι

/-- 概要：元の cofibrant 対象と元の弱同値からなる相対圏。
方針：同じ包含に沿って弱同値を引き戻す。
規約：Hom と対象は max u v に揃える。使われ方：一般モデルの Kan hammock。 -/
def modelCofibrantRelativeCategory : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{max u v} where
  category := Cat.of (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantCategory C)
  weakEquivalences := (weakEquivalences C).inverseImage (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantInclusion C)
  isMultiplicative := inferInstance

/-- 概要：cofibrant 相対圏の弱同値は元のモデル圏の同じ弱同値。
方針：逆像の定義を読む。
規約：定義上の一致。使われ方：全 frame 成分の相対性の判定。 -/
lemma modelCofibrantRelativeCategory_weak_iff
    {X Y : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).category} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).weakEquivalences f ↔
      weakEquivalences C ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantInclusion C).map f) := Iff.rfl

/-- 概要：元の cofibrant 対象を同じ相対圏の対象にする。
方針：対象の宇宙だけを揃える。
規約：元の cofibrancy の証明を保つ。使われ方：局所化頂点の指定。 -/
def modelCofibrantObject (X : CofibrantObject C) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).category := AsSmall.up.obj X

/-- 概要：同じ相対圏からの包含は元の弱同値を保つ。
方針：逆像として定めた同じ弱同値を読む。
規約：元のモデル構造を使用。使われ方：全 C の指定局所化との接続。 -/
def modelCofibrantInclusionRelative :
    LocalizerMorphism (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).weakEquivalences
      (weakEquivalences C) :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantInclusion C, fun _ _ _ hf => hf⟩

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.4.17"] _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantCategory
