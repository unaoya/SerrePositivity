module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexProducts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality
/-!
# 元の比較射の固定頂点列の Hom 因子への作用

概要：元の底の比較を同じ対象表示で移した固定 Hom と、その有限積の射を構成する。
方針：既存の FixedObjectHom の係数自然変換と有限積の元の比較を使う。
規約：元の対象表示の保存等式を前後の eqToHom で明示する。
使われ方：DK10.4–10.5の元の部分対角の弱比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
open CategoryTheory SerrePositivity.InfinityCategories
variable {D E : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} {O : Type u}
  (p : (n : SimplexCategoryᵒᵖ) → O ≃ (D.obj n).base)
  (q : (n : SimplexCategoryᵒᵖ) → O ≃ (E.obj n).base)
  (hp : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (D.map θ).base.obj (p n o) = p m o)
  (hq : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (E.map θ).base.obj (q n o) = q m o)
  (τ : D ⟶ E) (hτ : ∀ n o, (τ.app n).base.obj (p n o) = q n o)

def homSpaceMap (X Y : O) : homSpace D p hp X Y ⟶ homSpace E q hq X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.baseFunctor) (E ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.baseFunctor)
    (fun n o => p n o) (fun n o => q n o) hp hq (Functor.whiskerRight τ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.baseFunctor)
    _root_.id hτ X Y

lemma homSpaceMap_app (X Y : O) (n : SimplexCategoryᵒᵖ) (f : p n X ⟶ p n Y) :
    (homSpaceMap p q hp hq τ hτ X Y).app n f =
      eqToHom (hτ n X).symm ≫ (τ.app n).base.map f ≫ eqToHom (hτ n Y) := rfl

def homProductMap (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O) :
    FiniteProduct.space (fun i : Fin k.unop.len => homSpace D p hp (x i.castSucc) (x i.succ)) ⟶
    FiniteProduct.space (fun i : Fin k.unop.len => homSpace E q hq (x i.castSucc) (x i.succ)) :=
  FiniteProduct.map (fun i => homSpaceMap p q hp hq τ hτ (x i.castSucc) (x i.succ))

lemma homProductMap_weak
    (h : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (homSpaceMap p q hp hq τ hτ X Y))
    (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (homProductMap p q hp hq τ hτ k x) :=
  FiniteProduct.map_weak _ (fun i => h (x i.castSucc) (x i.succ))
end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
