module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.UniversePointCoslice
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.UniverseCosliceUncurry

/-!
概要：元の指定点の coslice の宇宙比較は、その元の全普遍錐の展開も保つ。
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

/-- 元の固定図式の等式輸送は、同じ全 coslice 錐の展開を変えない。 -/
lemma sliceUnderUncurry_eqIso {A K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (f ≫ (eqToIso (congrArg (fun r : K ⟶ X => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r) h)).hom) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f := by
  subst q
  rw [eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- 同じ点の coslice 宇宙同型は、元の全普遍錐族の展開を厳密に保つ。 -/
lemma pointCosliceUniverseIso_uncurry {A X : SSet.{u}} (x : X _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((SSet.uliftFunctor.{v, u}).map f ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCosliceUniverseIso.{u, v} x).hom) =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, v} A 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCosliceUniverseIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, ← Category.assoc, sliceUnderUncurry_eqIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap.{u, v} x),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceUnderUncurry_ulift]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
