module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSlices

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCurryHomExt
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：slice の元の全錐族の展開は、元の join の宇宙比較と厳密に可換。
方針：各標準単体で元の付随錐を回収し、slice の宇宙同型の全単体公式を使う。
規約：全錐族と固定図式を保持し、頂点・両端の比較だけで代用しない。
使われ方：持ち上げた局所左 Kan 添字の標準全錐の厳密な同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の join の宇宙同型は、持ち上げた同じ単体の左因子への制限を保つ。 -/
lemma uliftJoinIso_inv_left_yoneda {K A : SSet.{u}} {n : ℕ} (a : A _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm (ULift.up a)) (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso.{u, v} A K).inv =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, v} K n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap a]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso, Iso.trans_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inv_naturality (SSet.yonedaEquiv.symm a) (𝟙 K)]
  simp only [Iso.refl_inv, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  rfl

/-- 元の slice の全錐族の展開と宇宙持ち上げは、元の全写像として厳密に可換。 -/
lemma sliceOverUncurry_ulift {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry ((SSet.uliftFunctor.{v, u}).map f ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceOverIso p).hom) =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso.{u, v} A K).inv ≫
        (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed]
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{v, u}).obj A)
        ((SSet.uliftFunctor.{v, u}).obj K) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso A K).inv =
        (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K) := by
      apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso A K).hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inr]
    rw [← Category.assoc, hi, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed]
  · intro n a
    obtain ⟨⟨a⟩, rfl⟩ := SSet.yonedaEquiv.symm.surjective a
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
    change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso K n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (f.app _ a).val = _
    rw [← Category.assoc, uliftJoinIso_inv_left_yoneda, Category.assoc, ← Functor.map_comp]
    have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f =
        (f.app _ a).val := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
    rw [hs]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
