module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexProductMap
public import SerrePositivity.EInfinity.Hammock.WeakIndexedSum
public import SerrePositivity.EInfinity.Hammock.WeakTensor
/-!
# 元の単体的二方向 Grothendieck 比較射の弱不変性

概要：底の元の固定 Hom と左右の係数対角が弱同値なら、元の全圏の対角射も弱同値。
方針：元の比較を有限 Hom 積の和へ厳密に移し、部分対角から全対角へ戻す。
規約：元の比較射自身を判定し、各通常次数の弱同値性や単体集合モデルを要求しない。
使われ方：DK10.4–10.6と元の hammock graph の弱不変性5.7。
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
  (hH : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (homSpaceMap p q hp hq τ hτ X Y))
  (hL : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (leftSpaceMap p q hp hq τ hτ X))
  (hR : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (rightSpaceMap p q hp hq τ hτ X))

include hH hL hR

lemma productMap_weak (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (productMap p q hp hq τ hτ k x) :=
  weakTensor (homProductMap_weak p q hp hq τ hτ hH k x)
    (weakTensor (hL (x (Fin.last k.unop.len))) (hR (x 0)))

lemma chainRowMap_weak (k : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (chainRowMap τ k) := by
  have hs := IndexedSum.map_weak _ (productMap_weak p q hp hq τ hτ hH hL hR k)
  have hc := hs.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (productsIso E q hq k).symm).isWeakHomotopyEquivalence
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (IndexedSum.map (productMap p q hp hq τ hτ k) ≫ (productsIso E q hq k).inv) at hc
  rw [← productsIso_inv_naturality p q hp hq τ hτ k] at hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (productsIso D p hp k).symm).isWeakHomotopyEquivalence.cancel_left hc

lemma diagonalTotalMap_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (diagonalTotalMap τ) :=
  diagonalTotalMap_weak_of_chainRows τ (chainRowMap_weak p q hp hq τ hτ hH hL hR)
end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
