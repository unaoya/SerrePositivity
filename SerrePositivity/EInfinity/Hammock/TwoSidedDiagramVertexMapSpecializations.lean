module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexHomMap
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap
public import Mathlib.CategoryTheory.HomCongr
/-!
# 固定対象の元の Hom・係数比較の弱同値性の特殊化

概要：底が各次数で充満忠実なら元の Hom 比較は同型、係数の各成分が同型なら対角比較は弱同値。
方針：元の Hom 同値と endpoint の同型を合成し、係数には既存の対角弱同値判定を使う。
規約：元の比較射自身を判定し、単体集合モデルを要求しない。
使われ方：DK10.4の固定底と10.5の元の底の変更。
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

def homSpaceIso (hF : ∀ n, (τ.app n).base.FullyFaithful) (X Y : O) :
    homSpace D p hp X Y ≅ homSpace E q hq X Y :=
  NatIso.ofComponents (fun n => Equiv.toIso
    ((hF n).homEquiv.trans (Iso.homCongr (eqToIso (hτ n X)) (eqToIso (hτ n Y)))))
    (by intro n m θ; exact (homSpaceMap p q hp hq τ hτ X Y).naturality θ)

lemma homSpaceIso_hom (hF : ∀ n, (τ.app n).base.FullyFaithful) (X Y : O) :
    (homSpaceIso p q hp hq τ hτ hF X Y).hom = homSpaceMap p q hp hq τ hτ X Y := rfl

lemma homSpaceMap_weak_of_fullyFaithful (hF : ∀ n, (τ.app n).base.FullyFaithful) (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (homSpaceMap p q hp hq τ hτ X Y) := by
  rw [← homSpaceIso_hom p q hp hq τ hτ hF X Y]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (homSpaceIso p q hp hq τ hτ hF X Y)).isWeakHomotopyEquivalence

lemma rightSpaceMap_weak_of_isIso (X : O)
    (h : ∀ n, IsIso ((τ.app n).right.app (p n X))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (rightSpaceMap p q hp hq τ hτ X) := by
  apply DoubleSimplicial.diagonalFunctor_map_weak
  intro n
  have := h n
  have : IsIso ((rightDiagramMap p q hp hq τ hτ X).app n) := by
    change IsIso ((τ.app n).right.app (p n X) ≫ (E.obj n).right.map (eqToHom (hτ n X)))
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (nerveFunctor.mapIso
      (asIso ((rightDiagramMap p q hp hq τ hτ X).app n)))).isWeakHomotopyEquivalence

lemma leftSpaceMap_weak_of_isIso (X : O)
    (h : ∀ n, IsIso ((τ.app n).left.app (Opposite.op (p n X)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (leftSpaceMap p q hp hq τ hτ X) := by
  apply DoubleSimplicial.diagonalFunctor_map_weak
  intro n
  have := h n
  have : IsIso ((leftDiagramMap p q hp hq τ hτ X).app n) := by
    change IsIso ((τ.app n).left.app (Opposite.op (p n X)) ≫
      (E.obj n).left.map (eqToHom (congrArg Opposite.op (hτ n X))))
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (nerveFunctor.mapIso
      (asIso ((leftDiagramMap p q hp hq τ hτ X).app n)))).isWeakHomotopyEquivalence
end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
