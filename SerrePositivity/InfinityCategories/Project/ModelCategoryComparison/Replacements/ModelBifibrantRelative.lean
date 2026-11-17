module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.ModelCofibrantRelative
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameReplacement

/-!
概要：任意モデル圏の bifibrant 相対圏と同じ right frame による変形を束ねる。
方針：元の全部分圏に次数零の fibrant 置換を持ち上げ、元の単位を保持する。
規約：元の cofibrancy・fibrancy と弱同値を使い、新しいモデル構造を置かない。
使われ方：bifibrant 源での hammock 普遍性を cofibrant 部分圏へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory _root_.HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy
variable (C : Type u) [Category.{v} C] [ModelCategory C]

/-- 概要：元の bifibrant 全部分圏の対象と射の宇宙を揃える。
方針：元の全部分圏の AsSmall 表示を使う。
規約：元の射を保つ。使われ方：局所化普遍性の中継相対圏。 -/
abbrev modelBifibrantCategory := AsSmall.{max u v} (BifibrantObject C)

/-- 概要：元の bifibrant 全部分圏から同じモデル圏への包含。
方針：宇宙の包みを外し、元の包含を合成する。
規約：元の全射。使われ方：弱同値の判定。 -/
def modelBifibrantInclusion : modelBifibrantCategory C ⥤ C :=
  AsSmall.down ⋙ BifibrantObject.ι

/-- 概要：元の bifibrant 対象と元の弱同値からなる相対圏。
方針：同じ包含に沿って弱同値を引き戻す。
規約：単体集合のモデルを要求しない。使われ方：中継 hammock の実入力。 -/
def modelBifibrantRelativeCategory : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{max u v} where
  category := Cat.of (modelBifibrantCategory C)
  weakEquivalences := (weakEquivalences C).inverseImage (modelBifibrantInclusion C)
  isMultiplicative := inferInstance

/-- 概要：元の bifibrant 対象を同じ相対圏の対象にする。
方針：対象の宇宙だけを揃える。
規約：元の二つの性質を保つ。使われ方：局所化頂点の指定。 -/
def modelBifibrantObject (X : BifibrantObject C) :
    (modelBifibrantRelativeCategory C).category := AsSmall.up.obj X

/-- 概要：元の bifibrant 対象を cofibrant 全部分圏へ含める。
方針：元の対象の cofibrancy を読む。
規約：元の全射を保持。使われ方：変形の包含側。 -/
def bifibrantToCofibrant : BifibrantObject C ⥤ CofibrantObject C :=
  BifibrantObject.ιCofibrantObject

variable {C} (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：同じ right frame の次数零を bifibrant 全部分圏へ持ち上げる。
方針：同じ置換の fibrancy と cofibrancy の保存を使う。
規約：元の cofibrant 対象から定義。使われ方：cofibrant 圏への変形の戻し。 -/
def cofibrantToBifibrant : CofibrantObject C ⥤ BifibrantObject C :=
  (bifibrantObjects C).lift (CofibrantObject.ι ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r) (fun X => by
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement_isCofibrant r X.obj,
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement_isFibrant r X.obj⟩)

/-- 概要：同じ cofibrant 相対圏から bifibrant 相対圏への実変形関手。
方針：元の全対象と全射を同じ持ち上げへ送る。
規約：宇宙の包み以外は元の次数零。使われ方：指定局所化の源の比較。 -/
def modelCofibrantToBifibrant : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).category ⥤
    (modelBifibrantRelativeCategory C).category :=
  AsSmall.down ⋙ cofibrantToBifibrant r ⋙ AsSmall.up

/-- 概要：同じ bifibrant 相対圏の元の cofibrant 相対圏への包含。
方針：元の包含の前後で宇宙を揃える。
規約：元の全射。使われ方：変形の包含側。 -/
def modelBifibrantToCofibrant : (modelBifibrantRelativeCategory C).category ⥤
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).category :=
  AsSmall.down ⋙ bifibrantToCofibrant C ⋙ AsSmall.up

/-- 概要：同じ実変形は元の弱同値を保つ。
方針：right frame の次数零の弱同値保存を使う。
規約：元の弱同値の逆像。使われ方：相対圏の局所化への関手化。 -/
lemma modelCofibrantToBifibrant_map_weak
    {X Y : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).category} (f : X ⟶ Y)
    (hf : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).weakEquivalences f) :
    (modelBifibrantRelativeCategory C).weakEquivalences
      ((modelCofibrantToBifibrant r).map f) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement_map_weak r ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantInclusion C).map f) hf

/-- 概要：同じ相対圏の包含は元の弱同値を保つ。
方針：二つの包含像の底は同じ元の射。
規約：定義上の条件。使われ方：反転関手の制限。 -/
lemma modelBifibrantToCofibrant_map_weak
    {X Y : (modelBifibrantRelativeCategory C).category} (f : X ⟶ Y)
    (hf : (modelBifibrantRelativeCategory C).weakEquivalences f) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).weakEquivalences
      ((modelBifibrantToCofibrant (C := C)).map f) := hf

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
