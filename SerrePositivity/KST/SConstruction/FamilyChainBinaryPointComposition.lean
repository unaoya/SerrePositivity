module
public import SerrePositivity.KST.SConstruction.FamilyChainBinaryComposition
public import SerrePositivity.KST.SConstruction.CoherentHomotopyComponentCalculus

/-! # 全 trace の二部分の実合成三角形を元の指定点で評価する
概要：元の三つの全円柱を持つ合成三角形を、元の指定点の実三角形へ写す。
方針：内部 Hom の同じ評価写像で全二単体を写し、元の三つの実辺を回収する。
規約：全三角形は同じ元の三角形の実像であり、評価後に充填し直さない。
使われ方：元の二本の単一射円柱と元の合成補正を同じ raw 写像空間で貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の全円柱の実辺の評価像は、同じ円柱の同じ指定点での実辺。 -/
lemma familyHomotopyEdge_evaluate {U E : SSet.{u}} {f g : U ⟶ E}
    (H : SSet.Homotopy f g) (v : U _⦋0⦌) :
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H v).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) = _
  rw [← SSet.yonedaEquiv_comp]
  exact homotopyVertexEdge_yoneda H v

variable {U E : SSet.{u}} [KanComplex E] {f g h : U ⟶ E}
  {a : FamilyHomotopyChain f g} {b : FamilyHomotopyChain g h} {c : FamilyHomotopyChain f h}
  (A : FamilyChainCompositeData a) (B : FamilyChainCompositeData b) (D : FamilyChainCompositeData c)
  (ht : familyHomotopyChainTrace c = familyHomotopyChainTrace a ++ familyHomotopyChainTrace b)
  (v : U _⦋0⦌)

/-- 元の同じ全三角形を指定点で評価し、三つの元の同じ実円柱辺を保持する。 -/
def familyChainBinaryCompositionPointTriangle : SSet.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge A.homotopy v) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge B.homotopy v)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge D.homotopy v) :=
  ((familyChainBinaryCompositionTriangle A B D ht).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)).ofEq
    (familyHomotopyEdge_evaluate A.homotopy v) (familyHomotopyEdge_evaluate B.homotopy v)
    (familyHomotopyEdge_evaluate D.homotopy v)

/-- 評価後の全二単体は、元の同じ全二単体の評価像そのもの。 -/
lemma familyChainBinaryCompositionPointTriangle_realization :
    SSet.yonedaEquiv.symm (familyChainBinaryCompositionPointTriangle A B D ht v).simplex =
      SSet.yonedaEquiv.symm (familyChainBinaryCompositionTriangle A B D ht).simplex ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v :=
  (SSet.yonedaEquiv_symm_comp (familyChainBinaryCompositionTriangle A B D ht).simplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)).symm

end SerrePositivity.KST.SConstruction
