module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FixedQuillenFrameInvariance

/-!
概要：標準解消 Hom を、元の始域置換の比較に沿って前合成する二変数自然変換。
方針：元の関手的解消と同じ比較自然変換を使い、全次数の式と弱同値の場合の不変性を証明する。
規約：置換を独立に選ばない。使われ方：Quillen 随伴 Hom の二重始域置換の表示を戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory Limits HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [ModelCategory C] {E : Type w} [Category.{t} E]
  (q : CofibrantResolutionFamily (C := C) simplex) (Q : C ⥤ C) (ε : Q ⟶ 𝟭 C) (T : E ⥤ C)

/-- 元の始域置換比較を解消と Hom に適用した、両変数で自然な同じ前合成。 -/
def resolutionHomSourceRestriction :
    q.obj.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (Functor.whiskeringLeft E C SSet.{u}).obj T ⟶
      (Q ⋙ q.obj).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
        (Functor.whiskeringLeft E C SSet.{u}).obj T :=
  Functor.whiskerRight
    (Functor.whiskerRight (NatTrans.op (Functor.whiskerRight ε q.obj))
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor)
    ((Functor.whiskeringLeft E C SSet.{u}).obj T)

/-- 全次数の写像は、元の解消関手による同じ比較射の像を前合成したもの。 -/
lemma resolutionHomSourceRestriction_apply (X : Cᵒᵖ) (Y : E) (n : SimplexCategoryᵒᵖ)
    (f : (q.obj.obj X.unop).obj n.unop ⟶ T.obj Y) :
    (((resolutionHomSourceRestriction q Q ε T).app X).app Y).app n f =
      (q.obj.map (ε.app X.unop)).app n.unop ≫ f := rfl

/-- 元の始域比較が弱同値なら、同じ前合成は元の fibrant 終域でホモトピー同値。 -/
lemma resolutionHomSourceRestriction_homotopyEquivalence
    (hε : ∀ X, weakEquivalences C (ε.app X)) (X : Cᵒᵖ) (Y : E) [IsFibrant (T.obj Y)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((resolutionHomSourceRestriction q Q ε T).app X).app Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameHomMap_homotopyEquivalence (q.obj.map (ε.app X.unop))
    (q.cofibrant (Q.obj X.unop)) (q.cofibrant X.unop)
    (q.atObject (Q.obj X.unop)).homotopicallyConstant (q.atObject X.unop).homotopicallyConstant
    (q.map_weakEquivalence (ε.app X.unop) (hε X.unop)) (T.obj Y)

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
