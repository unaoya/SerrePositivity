module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCocartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory 値 weighted nerve の taut scaffold は cocartesian scaffold。
方針：射影の一致、標準水平辺、係数と fiber の厳密な同型を束ねる。
規約：全空間比較の同値性を追加仮定せず、一般の scaffold 定理から導く。
使われ方：Cat∞ 値 unstraightening の全空間比較と strict transport の復元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- taut scaffold の係数から fiber への射は既存の標準 fiber 同型と一致する。 -/
lemma tautScaffold_kanScaffoldFiberMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_projection F) c = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberMap F c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift F c
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift_tautScaffold F c

/-- quasicategory 値 weighted nerve の taut scaffold は cocartesian scaffold。 -/
@[kerodon 0379]
lemma tautScaffold_isCocartesianScaffold {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F) where
  projection := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_projection F
  horizontal f x := _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.tautScaffold_horizontal_isCocartesianEdge F f x
  fiber c := by
    rw [tautScaffold_kanScaffoldFiberMap]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberMap F c))).isQCatEquivalence

/-- 元の quasicategory 値 weighted nerve の taut scaffold は前合成同値。 -/
lemma tautScaffold_isPrecompositionEquivalence_of_quasicategory {C : Type u}
    [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F) :=
  (tautScaffold_isCocartesianScaffold F).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
