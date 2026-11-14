module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniversePointSlice
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.UniverseSliceUncurry

/-!
概要：元の指定点の slice の宇宙比較は、その元の全普遍錐の展開も保つ。
方針：固定図式の等式輸送と標準零単体への制限を消去し、元の全錐族の比較へ戻す。
規約：元の点と元の全錐の射を厳密に保持する。
使われ方：元の右 Kan 標準全錐の宇宙持ち上げとの厳密な一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の固定図式の等式輸送は、同じ全 slice 錐の展開を変えない。 -/
lemma sliceOverUncurry_eqIso {A K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (f ≫ (eqToIso (congrArg (fun r : K ⟶ X => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver r) h)).hom) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f := by
  subst q
  rw [eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- 同じ点の slice 宇宙同型は、元の全普遍錐族の展開を厳密に保つ。 -/
lemma pointSliceUniverseIso_uncurry {A X : SSet.{u}} (x : X _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry ((SSet.uliftFunctor.{v, u}).map f ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointSliceUniverseIso.{u, v} x).hom) =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso.{u, v} A 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointSliceUniverseIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, ← Category.assoc, sliceOverUncurry_eqIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap.{u, v} x),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_restrict, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceOverUncurry_ulift]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
