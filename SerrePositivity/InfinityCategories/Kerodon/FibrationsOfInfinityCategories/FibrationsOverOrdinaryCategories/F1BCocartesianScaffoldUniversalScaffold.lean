module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UniversalScaffoldEvaluation
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：strict transport の simplicial replacement から元の全空間への universal scaffold の射。
方針：undercategory の標準単体における係数の対角評価を全次数で束縛する。
規約：単体集合の射と底上の可換性を構成し、全空間の同値は後続で扱う。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、strict transport からの復元の比較射。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：strict transport の simplicial replacement から元の全空間への評価射。
方針：対角評価の自然性を使って次数ごとの評価を単体集合の射にする。
規約：構成自体に p の 充填性は要求しない。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、元の全空間との比較の片側の射。 -/
@[kerodon 026D]
def cocartesianUniversalScaffold {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) ⟶ E where
  app _ := ↾fun s ↦ SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianUniversalScaffoldSimplex p s)
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro s
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianUniversalScaffoldSimplex p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) α.unop s)) =
      E.map α (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianUniversalScaffoldSimplex p s))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianUniversalScaffoldSimplex_naturality]
    exact (SSet.yonedaEquiv_naturality α.unop (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianUniversalScaffoldSimplex p s)).symm

/-- 概要：universal scaffold は底の nerve 上の射。
方針：単体評価の底への合成の公式を Yoneda の自然性で各次数へ移す。
規約：元の射影 p と simplicial replacement の射影を厳密に固定する。
使われ方：Kerodon Proposition 5.3.4.8（Tag 0370）、scaffold の底に関する条件。 -/
lemma cocartesianUniversalScaffold_projection {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) :
    cocartesianUniversalScaffold p ≫ p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  change p.app d (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianUniversalScaffoldSimplex p s)) = s.1
  rw [← SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianUniversalScaffoldSimplex_projection]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
