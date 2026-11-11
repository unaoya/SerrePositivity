module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexHomMap
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramLabelComparison
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
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
open CategoryTheory Opposite MonoidalCategory
variable {D E : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} {O : Type u}
  (p : (n : SimplexCategoryᵒᵖ) → O ≃ (D.obj n).base)
  (q : (n : SimplexCategoryᵒᵖ) → O ≃ (E.obj n).base)
  (hp : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (D.map θ).base.obj (p n o) = p m o)
  (hq : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (E.map θ).base.obj (q n o) = q m o)
  (τ : D ⟶ E) (hτ : ∀ n o, (τ.app n).base.obj (p n o) = q n o)

def productMap (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O) :
    product D p hp k x ⟶ product E q hq k x :=
  homProductMap p q hp hq τ hτ k x ⊗ₘ
    (leftSpaceMap p q hp hq τ hτ (x (Fin.last k.unop.len)) ⊗ₘ
      rightSpaceMap p q hp hq τ hτ (x 0))

lemma productMap_app (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O)
    (n : SimplexCategoryᵒᵖ) (v : (product D p hp k x).obj n) :
    (productMap p q hp hq τ hτ k x).app n v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap (q n) (τ.app n).base
        (leftLabelComparison τ n) (rightLabelComparison τ n) (hτ n) x v := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cast_fiber (leftLabels E n) (rightLabels E n)
    (fun i => hτ n (x i))]
  rfl

lemma productsIso_inv_app (k : SimplexCategoryᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (x : Fin (k.unop.len + 1) → O) (v : (product D p hp k x).obj n) :
    (productsIso D p hp k).inv.app n ⟨x, v⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.decode (p n)
        (leftLabels D n) (rightLabels D n) k.unop.len x v := rfl

lemma productsIso_inv_naturality (k : SimplexCategoryᵒᵖ) :
    (productsIso D p hp k).inv ≫ chainRowMap τ k =
      IndexedSum.map (productMap p q hp hq τ hτ k) ≫ (productsIso E q hq k).inv := by
  ext n e
  rcases e with ⟨x, v⟩
  change (chainRowMap τ k).app n ((productsIso D p hp k).inv.app n ⟨x, v⟩) =
    (productsIso E q hq k).inv.app n ⟨x, (productMap p q hp hq τ hτ k x).app n v⟩
  rw [productsIso_inv_app, productsIso_inv_app, chainRowMap_app, productMap_app]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.decode_naturality (q n) (τ.app n).base
    (leftLabelComparison τ n) (rightLabelComparison τ n) (hτ n) x v

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
