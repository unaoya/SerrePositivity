module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ModelBifibrantRelative
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-!
概要：bifibrant 対象の元の Reedy 解像を同じ bifibrant 相対圏へ持ち上げる。
方針：元の augmentation の各自明 fibration と終域の fibrancy を使う。
規約：元の解像・全作用素・augmentation と全 Hom を保持する。
使われ方：bifibrant 全部分圏での三つの実 right Kan 判定入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open scoped _root_.Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

/-- 概要：同じ bifibrant 対象の解像の各値は fibrant。
方針：元の augmentation の fibration と元の終域の fibrancy を使う。
規約：元の解像の各値自身。使われ方：bifibrant 全部分圏への持ち上げ。 -/
lemma modelBifibrantFrame_isFibrant (n : SimplexCategory) : IsFibrant (q.obj.obj n) := by
  let p : q.obj.obj n ⟶ X.obj := q.augmentation.app n
  have : Fibration p :=
    ⟨(trivialFibration_app simplex q.augmentation q.trivial n).1⟩
  exact isFibrant_of_fibration p

/-- 概要：同じ元の解像の全値と全射を bifibrant 全部分圏に持ち上げる。
方針：各値の cofibrancy と同じ augmentation からの fibrancy を使う。
規約：frame を選び直さない。使われ方：標的が全て fibrant の実 Hom 比較。 -/
def modelBifibrantFrame : SimplexCategory ⥤ BifibrantObject C :=
  (bifibrantObjects C).lift q.obj
    (fun n => ⟨q.isCofibrant_obj n, modelBifibrantFrame_isFibrant X q n⟩)

/-- 概要：元の bifibrant frame の包含像は同じ解像の全図式。
方針：lift の定義を読む。
規約：関手の厳密な等式。使われ方：元の全 Hom の回収。 -/
lemma modelBifibrantFrame_inclusion :
    modelBifibrantFrame X q ⋙ BifibrantObject.ι = q.obj := rfl

/-- 概要：元の augmentation を bifibrant 全部分圏の自然変換にする。
方針：同じ各成分を全部分圏の射として束ねる。
規約：元の実射。使われ方：右 Kan 単位の回収。 -/
def modelBifibrantFrameAugmentation :
    modelBifibrantFrame X q ⟶ (Functor.const SimplexCategory).obj X where
  app n := ObjectProperty.homMk (q.augmentation.app n)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact q.augmentation.naturality f

/-- 概要：同じ全 frame を bifibrant 相対圏の宇宙へ送る。
方針：元の対象と射の前後で宇宙を揃える。
規約：全作用素を保持。使われ方：実 right Kan 次数比較。 -/
def modelBifibrantDKFrame : AsSmall.{max u v} SimplexCategory ⥤
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category :=
  AsSmall.down ⋙ modelBifibrantFrame X q ⋙ AsSmall.up

/-- 概要：同じ小さい frame の元の augmentation。
方針：元の成分と自然性を宇宙へ持ち上げる。
規約：元の基点を保つ。使われ方：全反転関手への実比較。 -/
def modelBifibrantDKFrameAugmentation : modelBifibrantDKFrame X q ⟶
    (Functor.const (AsSmall.{max u v} SimplexCategory)).obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X) where
  app n := AsSmall.up.map ((modelBifibrantFrameAugmentation X q).app (AsSmall.down.obj n))
  naturality _ _ f := by
    apply ULift.ext
    exact (modelBifibrantFrameAugmentation X q).naturality (AsSmall.down.map f)

/-- 概要：同じ小さい frame の全作用素は元の弱同値。
方針：元の解像の homotopically constant 性を読む。
規約：元の弱同値を保持。使われ方：反転関手の全 frame の像。 -/
lemma modelBifibrantDKFrame_map_weak {n m : AsSmall.{max u v} SimplexCategory} (f : n ⟶ m) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences ((modelBifibrantDKFrame X q).map f) :=
  q.homotopicallyConstant (AsSmall.down.map f)

/-- 概要：元の小さい augmentation の全成分は元の弱同値。
方針：元の解像の実 augmentation の弱同値性を使う。
規約：元の全成分を保持。使われ方：局所化後の比較二胞体。 -/
lemma modelBifibrantDKFrameAugmentation_weak (n : AsSmall.{max u v} SimplexCategory) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
      ((modelBifibrantDKFrameAugmentation X q).app n) :=
  q.augmentation_weakEquivalence (AsSmall.down.obj n)

/-- 概要：bifibrant frame の Hom は元のモデル圏の同じ Hom と同型。
方針：全部分圏の射の包みだけを外す。
規約：全単体と全作用素で成立。使われ方：実 Hom 比較の弱同値判定。 -/
def modelBifibrantFrameHomIso (Y : BifibrantObject C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (modelBifibrantFrame X q)).obj Y ≅ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj where
  hom := { app _ := ↾fun f => f.hom, naturality _ _ _ := rfl }
  inv := { app _ := ↾fun f => ObjectProperty.homMk f, naturality _ _ _ := rfl }

/-- 概要：同じ元のモデル圏の frame Hom は Kan 複体。
方針：元の Reedy cofibrancy と同じ終域の fibrancy を使う。
規約：単体集合モデルを使わない。使われ方：実比較の QCat 同値性。 -/
lemma modelBifibrantFrameHom_kanComplex (Y : BifibrantObject C) :
    SSet.KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj) :=
  cosimplicialHom_kanComplex q.obj q.cofibrant q.homotopicallyConstant Y.obj

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
