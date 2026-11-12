module
public import SerrePositivity.KST.SConstruction.FamilyChainTraceFaithfulness

/-! # 同じ全 trace の二部分を元の全円柱で合成する実三角形
概要：元の全補正列の trace を二部分へ分け、元の三つの合成円柱を実三角形の三辺にする。
方針：保存済みの全木の合成式と全 trace の忠実性から、実三角形の存在条件を証明する。
規約：三辺は元の同じ全円柱であり、各入力の全合成木を変更しない。
使われ方：合成補正を元の前後二本の単一射補正を二辺に持つ全三角形へまとめる。
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
variable {U E : SSet.{u}} {f g h : U ⟶ E}
  {a : FamilyHomotopyChain f g} {b : FamilyHomotopyChain g h} {c : FamilyHomotopyChain f h}
  (A : FamilyChainCompositeData a) (B : FamilyChainCompositeData b) (D : FamilyChainCompositeData c)
  (ht : familyHomotopyChainTrace c = familyHomotopyChainTrace a ++ familyHomotopyChainTrace b)

include ht in
/-- 同じ全 trace と元の全木の式から、元の三円柱は同じ合成関係を満たす。 -/
lemma familyChainBinaryComposition_class :
    SSet.HomotopyCategory.homMk
        (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy A.homotopy)) ≫
      SSet.HomotopyCategory.homMk
        (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy B.homotopy)) =
    SSet.HomotopyCategory.homMk
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy D.homotopy)) := by
  change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy A.homotopy) ≫
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy B.homotopy) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy D.homotopy)
  rw [familyChainCompositionWitness_class A.witness, familyChainCompositionWitness_class B.witness,
    familyChainCompositionWitness_class D.witness]
  have he : familyHomotopyChainTrace c =
      familyHomotopyChainTrace (familyHomotopyChainAppend a b) :=
    ht.trans (familyHomotopyChainAppend_trace a b).symm
  exact ((familyChainCompositeClass_eq_of_trace c _ he).trans
    (familyChainCompositeClass_append a b)).symm

/-- 元の同じ三つの全円柱を三辺に保持する実合成三角形。 -/
def familyChainBinaryCompositionTriangle [KanComplex E] : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy A.homotopy))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy B.homotopy))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy D.homotopy)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (familyChainBinaryComposition_class A B D ht)).some

/-- 第一面は、元の前半の同じ全円柱そのもの。 -/
lemma familyChainBinaryCompositionTriangle_first [KanComplex E] :
    uncurry (stdSimplex.δ 2 ≫
      SSet.yonedaEquiv.symm (familyChainBinaryCompositionTriangle A B D ht).simplex) =
        A.homotopy.h := by
  rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry A.homotopy.h))) = _
  rw [Equiv.symm_apply_apply, uncurry_curry]

/-- 第二面も、元の後半の同じ全円柱そのもの。 -/
lemma familyChainBinaryCompositionTriangle_second [KanComplex E] :
    uncurry (stdSimplex.δ 0 ≫
      SSet.yonedaEquiv.symm (familyChainBinaryCompositionTriangle A B D ht).simplex) =
        B.homotopy.h := by
  rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry B.homotopy.h))) = _
  rw [Equiv.symm_apply_apply, uncurry_curry]

/-- 対角面も、元の全列の同じ合成円柱そのもの。 -/
lemma familyChainBinaryCompositionTriangle_direct [KanComplex E] :
    uncurry (stdSimplex.δ 1 ≫
      SSet.yonedaEquiv.symm (familyChainBinaryCompositionTriangle A B D ht).simplex) =
        D.homotopy.h := by
  rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry D.homotopy.h))) = _
  rw [Equiv.symm_apply_apply, uncurry_curry]

end SerrePositivity.KST.SConstruction
