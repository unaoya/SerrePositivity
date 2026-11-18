module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoofPrefixEndpoints
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {C : Type u} [Category.{v} C] [_root_.HomotopicalAlgebra.ModelCategory C]
  (X Y : _root_.HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)
  (s : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductComma X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaPrefixHomotopy : SSet.Homotopy
    (toUnit (nerve (Under s)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaRightLeg X Y q b).app s))
    (nerveMap (Under.forget s) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluationRoofMap X Y q b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluation X Y q b).app s))
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.arrowHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
    (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f) s) rfl
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap_eq_precomp]
  exact Category.assoc _ _ _

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaPrefixHomotopy_h :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaPrefixHomotopy X Y q b s).h =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.graphHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaDiagram X Y q b)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
      (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f) s).h ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaDiagram X Y q b).obj s)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word :=
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
