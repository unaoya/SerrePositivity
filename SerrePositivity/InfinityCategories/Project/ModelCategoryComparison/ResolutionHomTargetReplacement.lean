module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedQuillenTargetInvariance

/-!
概要：元の fibrant な終域族の Hom を、選択した同じ fibrant 置換の比較で標準 Hom へ写す。
方針：元の終域比較自然変換を解消 Hom に適用し、固定 Quillen 類の終域不変性を使う。
規約：全次数の比較と両変数自然性を保持。使われ方：Quillen 右導来像と標準写像空間の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory Limits HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [ModelCategory C] {E : Type w} [Category.{t} E]
  (q : CofibrantResolutionFamily (C := C) simplex) (T : E ⥤ C)
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- 元の終域族に沿う同じ fibrant 置換比較を、解消 Hom に適用した二変数自然変換。 -/
def resolutionHomTargetReplacement :
    q.obj.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (Functor.whiskeringLeft E C SSet.{u}).obj T ⟶
      q.obj.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
        (Functor.whiskeringLeft E C SSet.{u}).obj (T ⋙ fibrantTarget fib) :=
  Functor.whiskerLeft (q.obj.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor)
    ((Functor.whiskeringLeft E C SSet.{u}).map
      (Functor.whiskerLeft T (fibrantTargetComparison fib)))

/-- 各次数の比較は、元の同じ終域置換の比較射への後合成そのもの。 -/
lemma resolutionHomTargetReplacement_apply (X : Cᵒᵖ) (Y : E) (n : SimplexCategoryᵒᵖ)
    (f : (q.obj.obj X.unop).obj n.unop ⟶ T.obj Y) :
    (((resolutionHomTargetReplacement q T fib).app X).app Y).app n f =
      f ≫ (fibrantTargetComparison fib).app (T.obj Y) := rfl

/-- 元の終域族が fibrant なら、同じ自然変換は全ての元のパラメータでホモトピー同値。 -/
lemma resolutionHomTargetReplacement_homotopyEquivalence
    (X : Cᵒᵖ) (Y : E) [IsFibrant (T.obj Y)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((resolutionHomTargetReplacement q T fib).app X).app Y) := by
  have := fibrantTarget_isFibrant fib (T.obj Y)
  have : WeakEquivalence ((fibrantTargetComparison fib).app (T.obj Y)) :=
    ⟨fibrantTargetComparison_weakEquivalence fib (T.obj Y)⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameHom_target_homotopyEquivalence (Y := T.obj Y)
    (q.obj.obj X.unop) (q.cofibrant X.unop)
    (q.atObject X.unop).homotopicallyConstant ((fibrantTargetComparison fib).app (T.obj Y))

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
