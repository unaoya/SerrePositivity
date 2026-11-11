module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ModelCofibrantRelative
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom

/-!
概要：元の Reedy 解像を任意モデル圏の同じ cofibrant 相対圏へ持ち上げる。
方針：各次数の cofibrancy で全部分圏に持ち上げ、元の全作用素を保持する。
規約：元の解像と augmentation を選び直さない。
使われ方：一般モデル圏の実右 Kan 比較と局所化普遍性の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy
open scoped _root_.Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X : CofibrantObject C) (q : _root_.SerrePositivity.Reedy.CofibrantResolution (C := C) simplex X.obj)

/-- 概要：元の全解像を同じ cofibrant 全部分圏に持ち上げる。
方針：元の各次数の cofibrancy を使う。
規約：射は元の作用素自身。使われ方：実 frame の小さい添字への持ち上げ。 -/
def modelCofibrantFrame : SimplexCategory ⥤ CofibrantObject C :=
  (cofibrantObjects C).lift q.obj q.isCofibrant_obj

/-- 概要：持ち上げた frame の包含像は同じ元の解像。
方針：全部分圏の lift の定義を読む。
規約：関手の厳密な等式。使われ方：元の Hom 族との照合。 -/
lemma modelCofibrantFrame_inclusion :
    modelCofibrantFrame X q ⋙ CofibrantObject.ι = q.obj := rfl

/-- 概要：元の augmentation を同じ cofibrant 対象への自然変換にする。
方針：各成分を全部分圏の同じ射として束ねる。
規約：新しい持ち上げを選ばない。使われ方：右 Kan 錐の元の脚。 -/
def modelCofibrantFrameAugmentation :
    modelCofibrantFrame X q ⟶ (Functor.const SimplexCategory).obj X where
  app n := ObjectProperty.homMk (q.augmentation.app n)
  naturality n m f := by
    apply ObjectProperty.hom_ext
    exact q.augmentation.naturality f

/-- 概要：元の frame を同じ宇宙の cofibrant 相対圏へ送る。
方針：元の frame の前後に宇宙の包みだけを置く。
規約：全単体作用素を保持。使われ方：局所化判定の実次数比較。 -/
def modelCofibrantDKFrame : AsSmall.{max u v} SimplexCategory ⥤
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).category :=
  AsSmall.down ⋙ modelCofibrantFrame X q ⋙ AsSmall.up

/-- 概要：同じ小さい frame から元の cofibrant 対象への augmentation。
方針：元の augmentation の射を同じ宇宙へ持ち上げる。
規約：対象も射も元のまま。使われ方：実 right Kan 単位の成分の回収。 -/
def modelCofibrantDKFrameAugmentation : modelCofibrantDKFrame X q ⟶
    (Functor.const (AsSmall.{max u v} SimplexCategory)).obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantObject C X) where
  app n := AsSmall.up.map ((modelCofibrantFrameAugmentation X q).app (AsSmall.down.obj n))
  naturality n m f := by
    apply ULift.ext
    exact (modelCofibrantFrameAugmentation X q).naturality (AsSmall.down.map f)

/-- 概要：同じ小さい frame の全作用素は元の弱同値。
方針：元の解像の homotopically constant 性を読む。
規約：別の弱同値類を使わない。使われ方：全反転関手への frame の像。 -/
lemma modelCofibrantDKFrame_map_weak {n m : AsSmall.{max u v} SimplexCategory} (f : n ⟶ m) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).weakEquivalences ((modelCofibrantDKFrame X q).map f) :=
  q.homotopicallyConstant (AsSmall.down.map f)

/-- 概要：同じ小さい augmentation の全成分は元の弱同値。
方針：元の解像の augmentation の弱同値性を使う。
規約：全次数を扱う。使われ方：局所化後の元の augmentation の可逆性。 -/
lemma modelCofibrantDKFrameAugmentation_weak (n : AsSmall.{max u v} SimplexCategory) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).weakEquivalences
      ((modelCofibrantDKFrameAugmentation X q).app n) :=
  q.augmentation_weakEquivalence (AsSmall.down.obj n)

/-- 概要：持ち上げた frame Hom は元の解像 Hom に厳密に同型。
方針：全部分圏の射の包みを外して逆に束ねる。
規約：全単体の元の射を保持。使われ方：一般モデルの実 frame 比較。 -/
def modelCofibrantFrameHomIso (Y : CofibrantObject C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (modelCofibrantFrame X q)).obj Y ≅ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj where
  hom := { app _ := ↾fun f => f.hom, naturality _ _ _ := rfl }
  inv := { app _ := ↾fun f => ObjectProperty.homMk f, naturality _ _ _ := rfl }

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
