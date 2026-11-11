module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleFunctorEdgePath
/-!
概要：一つの全関手同型で可換な脚を、両入力の可逆 path 置換の間の厳密な脚へ移す。
方針：元の可換同型と入力置換の指定同型を合成し、同じ全 path を引き戻しへ入れる。
規約：元の射影・終点を厳密に保持する。使われ方：関手同型付き cospan の strict 化。

対応節は Kerodon 5.5（Tag 01YV）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
variable {A C A' C' : SSet.{u}}
  [Quasicategory A] [Quasicategory C] [Quasicategory A'] [Quasicategory C']
  (p : A ⟶ C) (p' : A' ⟶ C') (a : A ⟶ A') (c : C ⟶ C')
  (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p ≫ c) (a ≫ p'))

def cospanPathLegIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection a ≫ p) ≫ c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap a ≫ p') := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection a ≫ p) ≫ c)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection a ≫ a) ≫ p') := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using hp.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection a)
  exact h.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementFunctorIso a).postcomp p')

def cospanPathLeg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement c :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertibleFunctorEdgePath (cospanPathLegIso p p' a c hp).edge
      (cospanPathLegIso p p' a c hp).edge_isInvertible)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection a ≫ p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertibleFunctorEdgePath_zero _ _)

lemma cospanPathLeg_projection :
    cospanPathLeg p p' a c hp ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection a ≫ p := pullback.lift_snd _ _ _

lemma cospanPathLeg_map :
    cospanPathLeg p p' a c hp ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap a ≫ p' := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap, ← Category.assoc, cospanPathLeg,
    pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertibleFunctorEdgePath_one]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
