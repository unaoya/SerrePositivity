module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.RightFrameFamily
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SourceInvariance
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-!
概要：元の right frame Hom は標的の弱同値を QCat 同値へ送る。
方針：反対圏の同じ解像射の弱同値性を始域不変性へ渡す。
規約：単体集合モデル・cofibration の単射性は仮定しない。
使われ方：全標的関手を指定した ∞ 局所化へ下ろす入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uD vD
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory Limits HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：反対 Hom への照合は全標的射と厳密に可換。
方針：各次数で元の合成を op にする。
規約：同じ解像の同じ自然変換を使う。使われ方：弱同値性の移送。 -/
lemma rightFrameHomOpIso_naturality (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).map f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHomOpIso r X Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHomOpIso r X Y).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (r.obj.map f.op)).app (op X) := by
  ext n a
  rfl

/-- 概要：標的の弱同値の像は anodyne 反転後に同型。
方針：反対圏で元の frame 射の弱同値性と始域不変性を使う。
規約：cofibrant 源だけを要求する。使われ方：元の比較射の弱同値判定。 -/
lemma rightFrameHom_map_isIso (X : C) [IsCofibrant X]
    {Y Z : C} (f : Y ⟶ Z) (hf : weakEquivalences C f)
    {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).map f)) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant X
  have hw : weakEquivalences Cᵒᵖ f.op := hf
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_weakEquivalence_isIso L hL (r.obj.map f.op)
    (r.cofibrant (op Z)) (r.cofibrant (op Y))
    (r.map_weakEquivalence f.op hw) (op X)
  have h := congrArg L.map (rightFrameHomOpIso_naturality r X f)
  simp only [Functor.map_comp] at h
  have : IsIso (L.map ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).map f) ≫
      L.map (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHomOpIso r X Z).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (L.map (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHomOpIso r X Z).hom)

/-- 概要：標的の弱同値を送った元の射は弱ホモトピー同値。
方針：anodyne 局所化での反転性を全 Kan 標的の検査へ渡す。
規約：同じ元の射を結論に残す。使われ方：QCat 同値性の判定。 -/
lemma rightFrameHom_map_isWeakHomotopyEquivalence (X : C) [IsCofibrant X]
    {Y Z : C} (f : Y ⟶ Z) (hf : weakEquivalences C f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).map f) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (rightFrameHom_map_isIso r X f hf AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions))

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex

/-- 概要：right frame Hom は標的の弱同値を実 QCat 同値へ送る。
方針：両 Hom の Kan 性と同じ射の弱ホモトピー同値性を使う。
規約：元の標的の fibrancy は不要。使われ方：指定 ∞ 局所化への全族の降下。 -/
lemma rightFrameHom_map_isQCatEquivalence (X : C) [IsCofibrant X]
    {Y Z : C} (f : Y ⟶ Z) (hf : weakEquivalences C f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).map f) := by
  have h := rightFrameHom_map_isWeakHomotopyEquivalence r X f hf
  exact h.isSimplicialHomotopyEquivalence.isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
