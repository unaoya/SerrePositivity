module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.UniverseSlices
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniverseSliceProjection

/-!
概要：元の点上の全 slice を持ち上げたものと、持ち上げた同じ点上の全 slice の同型。
方針：標準零単体の二重持ち上げを制限同型で除き、元の射影を厳密に保つ。
規約：元の点の同一性と全次数の射影を保持する。
使われ方：元の局所左 Kan 添字の宇宙比較。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 固定図式の等式による slice の移送は、元の射影を保つ。 -/
lemma idemSliceOverEqIso_projection {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) :
    (eqToIso (congrArg (fun f : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver f) h)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p := by
  subst q
  exact Category.id_comp _

/-- 元の点上の全 slice の持ち上げを、持ち上げた同じ点上の全 slice と同定する。 -/
def pointSliceUniverseIso {X : SSet.{u}} (x : X _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x)) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{v, u}).obj X)).symm (ULift.up x)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_isIso ((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 0).inv
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceOverIso (SSet.yonedaEquiv.symm x) ≪≫
    asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict ((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso 0).inv) ≪≫
    eqToIso (congrArg (fun f : (Δ[0] : SSet.{max u v}) ⟶
      (SSet.uliftFunctor.{v, u}).obj X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver f) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap x))

/-- 元の点上の slice の宇宙同型は、元の点への全射影を厳密に保つ。 -/
lemma pointSliceUniverseIso_projection {X : SSet.{u}} (x : X _⦋0⦌) :
    (pointSliceUniverseIso.{u, v} x).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{v, u}).obj X)).symm (ULift.up x)) =
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)) := by
  dsimp only [pointSliceUniverseIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, Category.assoc, idemSliceOverEqIso_projection (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap.{u, v} x),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemSliceOverRestrict_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemUniverseSliceOverIso_projection]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
