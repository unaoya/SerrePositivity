module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramSimplicialWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexMapSpecializations

/-!
# 元の単体的二方向比較の固定底・底変更への特殊化

概要：充満忠実な各底での係数不変性と、同型な係数での底の Hom 弱不変性を得る。
方針：元の Hom・両係数の特殊化を同じ元の対角比較の弱同値定理へ代入する。
規約：係数は対角での弱同値性を保持し、底変更に通常の各次数の Hom 弱同値を要求しない。
使われ方：DK10.4の固定底と10.5の恒等係数による底変更。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

lemma diagonalTotalMap_weak_of_fullyFaithful_base
    (hF : ∀ n, (τ.app n).base.FullyFaithful)
    (hL : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (leftSpaceMap p q hp hq τ hτ X))
    (hR : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (rightSpaceMap p q hp hq τ hτ X)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (diagonalTotalMap τ) :=
  diagonalTotalMap_weak p q hp hq τ hτ
    (homSpaceMap_weak_of_fullyFaithful p q hp hq τ hτ hF) hL hR

lemma diagonalTotalMap_weak_of_isIso_coefficients
    (hH : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (homSpaceMap p q hp hq τ hτ X Y))
    (hL : ∀ n X, IsIso ((τ.app n).left.app (Opposite.op (p n X))))
    (hR : ∀ n X, IsIso ((τ.app n).right.app (p n X))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (diagonalTotalMap τ) :=
  diagonalTotalMap_weak p q hp hq τ hτ hH
    (fun X => leftSpaceMap_weak_of_isIso p q hp hq τ hτ X (fun n => hL n X))
    (fun X => rightSpaceMap_weak_of_isIso p q hp hq τ hτ X (fun n => hR n X))

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
