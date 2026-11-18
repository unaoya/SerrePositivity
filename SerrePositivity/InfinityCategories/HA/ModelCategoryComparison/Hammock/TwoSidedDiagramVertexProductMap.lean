module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramVertexHomMap
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramVertexCoefficientMap
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramLabelComparison
/-!
# 元の部分対角の比較と有限 Hom 積の和の比較の一致

概要：元の chainRowMap を、Hom と両係数の元の比較の直積の和へ厳密に戻す。
方針：元の座標復元の自然性と、全因子の端点移送の式を照合する。
規約：比較射自身を保持し、弱同値性を入力にしない。
使われ方：DK10.4–10.5の元の単体的全圏の比較射の弱同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices
open _root_.CategoryTheory _root_.Opposite _root_.CategoryTheory.MonoidalCategory
variable {D E : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} {O : Type u}
  (p : (n : SimplexCategoryᵒᵖ) → O ≃ (D.obj n).base)
  (q : (n : SimplexCategoryᵒᵖ) → O ≃ (E.obj n).base)
  (hp : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (D.map θ).base.obj (p n o) = p m o)
  (hq : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (E.map θ).base.obj (q n o) = q m o)
  (τ : D ⟶ E) (hτ : ∀ n o, (τ.app n).base.obj (p n o) = q n o)

def productMap (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.product D p hp k x ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.product E q hq k x :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.homProductMap p q hp hq τ hτ k x ⊗ₘ
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.leftSpaceMap p q hp hq τ hτ (x (Fin.last k.unop.len)) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.rightSpaceMap p q hp hq τ hτ (x 0))

lemma productMap_app (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O)
    (n : SimplexCategoryᵒᵖ) (v : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.product D p hp k x).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productMap p q hp hq τ hτ k x).app n v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap (q n) (τ.app n).base
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabelComparison τ n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabelComparison τ n) (hτ n) x v := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cast_fiber (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels E n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels E n)
    (fun i => hτ n (x i))]
  rfl

lemma productsIso_inv_app (k : SimplexCategoryᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (x : Fin (k.unop.len + 1) → O) (v : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.product D p hp k x).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productsIso D p hp k).inv.app n ⟨x, v⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.decode (p n)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels D n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels D n) k.unop.len x v := rfl

lemma productsIso_inv_naturality (k : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productsIso D p hp k).inv ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.chainRowMap τ k =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productMap p q hp hq τ hτ k) ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productsIso E q hq k).inv := by
  ext n e
  rcases e with ⟨x, v⟩
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.chainRowMap τ k).app n ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productsIso D p hp k).inv.app n ⟨x, v⟩) =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productsIso E q hq k).inv.app n ⟨x, (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productMap p q hp hq τ hτ k x).app n v⟩
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productsIso_inv_app, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productsIso_inv_app, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.chainRowMap_app, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productMap_app]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.decode_naturality (q n) (τ.app n).base
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabelComparison τ n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabelComparison τ n) (hτ n) x v

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices
