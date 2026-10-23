module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveCocartesianFibration
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementFiber
public import SerrePositivity.InfinityCategories.F1B.KanScaffoldComparison

/-!
概要：quasicategory 値 weighted nerve の taut scaffold は cocartesian scaffold。
方針：射影の一致、標準水平辺、係数と fiber の厳密な同型を束ねる。
規約：全空間比較の同値性を追加仮定せず、一般の scaffold 定理から導く。
使われ方：Cat∞ 値 unstraightening の全空間比較と strict transport の復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- taut scaffold の係数から fiber への射は既存の標準 fiber 同型と一致する。 -/
lemma tautScaffold_kanScaffoldFiberMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    kanScaffoldFiberMap (weightedNerveProjection F) F (tautScaffold F)
      (tautScaffold_projection F) c = weightedNerveFiberMap F c := by
  apply vertexFiber_hom_ext
  change simplicialReplacementConstantLift F c ≫ tautScaffold F = weightedNerveConstantLift F c
  exact simplicialReplacementConstantLift_tautScaffold F c

/-- quasicategory 値 weighted nerve の taut scaffold は cocartesian scaffold。 -/
lemma tautScaffold_isCocartesianScaffold {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    KanCocartesianScaffold (weightedNerveProjection F) F (tautScaffold F) where
  projection := tautScaffold_projection F
  horizontal f x := tautScaffold_horizontal_isCocartesianEdge F f x
  fiber c := by
    rw [tautScaffold_kanScaffoldFiberMap]
    exact (qCatEquivalenceOfIso (asIso (weightedNerveFiberMap F c))).isQCatEquivalence

/-- 元の quasicategory 値 weighted nerve の taut scaffold は前合成同値。 -/
lemma tautScaffold_isPrecompositionEquivalence_of_quasicategory {C : Type u}
    [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    IsPrecompositionEquivalence (tautScaffold F) :=
  (tautScaffold_isCocartesianScaffold F).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories
