module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexProducts
/-!
# 元の比較射の固定対象の両係数図式への作用

概要：対象表示を保つ元の比較を、左右の係数圏とその nerve の対角の射へ移す。
方針：元の図式の自然性と係数の自然性を端点の eqToHom と合わせる。
規約：同じ元の各成分を使い、次数ごとの弱同値性は仮定しない。
使われ方：DK10.4–10.5の両端係数の元の対角比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
open CategoryTheory Opposite
lemma right_app_transport_congr {A B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} {f g : A ⟶ B} (h : f = g)
    (x : A.base) (z : B.base) (hf : f.base.obj x = z) (hg : g.base.obj x = z) :
    f.right.app x ≫ B.right.map (eqToHom hf) =
      g.right.app x ≫ B.right.map (eqToHom hg) := by
  cases h
  rfl
lemma left_app_transport_congr {A B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} {f g : A ⟶ B} (h : f = g)
    (x : A.baseᵒᵖ) (z : B.baseᵒᵖ) (hf : f.base.op.obj x = z) (hg : g.base.op.obj x = z) :
    f.left.app x ≫ B.left.map (eqToHom hf) =
      g.left.app x ≫ B.left.map (eqToHom hg) := by
  cases h
  rfl
namespace FixedVertices
variable {D E : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} {O : Type u}
  (p : (n : SimplexCategoryᵒᵖ) → O ≃ (D.obj n).base)
  (q : (n : SimplexCategoryᵒᵖ) → O ≃ (E.obj n).base)
  (hp : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (D.map θ).base.obj (p n o) = p m o)
  (hq : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (E.map θ).base.obj (q n o) = q m o)
  (τ : D ⟶ E) (hτ : ∀ n o, (τ.app n).base.obj (p n o) = q n o)

def rightDiagram (X : O) : SimplicialObject Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.objectDiagram (D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.baseFunctor)
    (fun n => p n X) (fun θ => hp θ X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.rightTransfunctor D)

def leftDiagram (X : O) : SimplicialObject Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.objectDiagram (D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.baseFunctor ⋙ Cat.opFunctor)
    (fun n => op (p n X)) (fun θ => congrArg op (hp θ X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.leftTransfunctor D)

def rightDiagramMap (X : O) : rightDiagram p hp X ⟶ rightDiagram q hq X where
  app n := (τ.app n).right.app (p n X) ≫ (E.obj n).right.map (eqToHom (hτ n X))
  naturality n m θ := by
    change ((D.map θ).right.app (p n X) ≫ (D.obj m).right.map (eqToHom (hp θ X))) ≫
        ((τ.app m).right.app (p m X) ≫ (E.obj m).right.map (eqToHom (hτ m X))) =
      ((τ.app n).right.app (p n X) ≫ (E.obj n).right.map (eqToHom (hτ n X))) ≫
        ((E.map θ).right.app (q n X) ≫ (E.obj m).right.map (eqToHom (hq θ X)))
    simp only [Category.assoc]
    rw [(τ.app m).right.naturality_assoc, (E.map θ).right.naturality_assoc]
    simp only [Functor.comp_map, eqToHom_map, eqToHom_trans]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.comp_right, NatTrans.comp_app, Functor.whiskerLeft_app,
      eqToHom_map, Category.assoc] using
      right_app_transport_congr (τ.naturality θ) (p n X) (q m X)
        ((congrArg (τ.app m).base.obj (hp θ X)).trans (hτ m X))
        ((congrArg (E.map θ).base.obj (hτ n X)).trans (hq θ X))

def leftDiagramMap (X : O) : leftDiagram p hp X ⟶ leftDiagram q hq X where
  app n := (τ.app n).left.app (op (p n X)) ≫
    (E.obj n).left.map (eqToHom (congrArg op (hτ n X)))
  naturality n m θ := by
    change ((D.map θ).left.app (op (p n X)) ≫
        (D.obj m).left.map (eqToHom (congrArg op (hp θ X)))) ≫
        ((τ.app m).left.app (op (p m X)) ≫
          (E.obj m).left.map (eqToHom (congrArg op (hτ m X)))) =
      ((τ.app n).left.app (op (p n X)) ≫
        (E.obj n).left.map (eqToHom (congrArg op (hτ n X)))) ≫
        ((E.map θ).left.app (op (q n X)) ≫
          (E.obj m).left.map (eqToHom (congrArg op (hq θ X))))
    simp only [Category.assoc]
    rw [(τ.app m).left.naturality_assoc, (E.map θ).left.naturality_assoc]
    simp only [Functor.comp_map, eqToHom_map, eqToHom_trans]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.comp_left, NatTrans.comp_app, Functor.whiskerLeft_app,
      eqToHom_map, Category.assoc] using
      left_app_transport_congr (τ.naturality θ) (op (p n X)) (op (q m X))
        (congrArg op ((congrArg (τ.app m).base.obj (hp θ X)).trans (hτ m X)))
        (congrArg op ((congrArg (E.map θ).base.obj (hτ n X)).trans (hq θ X)))

def rightSpaceMap (X : O) : rightSpace D p hp X ⟶ rightSpace E q hq X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map
    (Functor.whiskerRight (rightDiagramMap p q hp hq τ hτ X) nerveFunctor)

def leftSpaceMap (X : O) : leftSpace D p hp X ⟶ leftSpace E q hq X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map
    (Functor.whiskerRight (leftDiagramMap p q hp hq τ hτ X) nerveFunctor)

lemma rightSpaceMap_app (X : O) (n : SimplexCategoryᵒᵖ)
    (a : (rightSpace D p hp X).obj n) :
    (rightSpaceMap p q hp hq τ hτ X).app n a =
      a ⋙ ((τ.app n).right.app (p n X)).toFunctor ⋙
        ((E.obj n).right.map (eqToHom (hτ n X))).toFunctor := rfl

lemma leftSpaceMap_app (X : O) (n : SimplexCategoryᵒᵖ)
    (a : (leftSpace D p hp X).obj n) :
    (leftSpaceMap p q hp hq τ hτ X).app n a =
      a ⋙ ((τ.app n).left.app (op (p n X))).toFunctor ⋙
        ((E.obj n).left.map (eqToHom (congrArg op (hτ n X)))).toFunctor := rfl

end FixedVertices
end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
