module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomPinched
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomComparisonVertices

/-!
概要：元の hammock 射の pinched 零単体は元の局所化辺そのもの。
方針：原本の coherent 零単体公式へ元の豊穣源関手の射を代入する。
規約：原本を読み取り専用で再利用し、元の射と端点を変更しない。
使われ方：全 frame 比較の零単体と指定二胞体の共役の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SSet _root_.Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

/-- 概要：同じ元の通常射の Kan hammock 点は元の局所化辺を回収する。
方針：元の源関手の homTo 公式と原本の coherent Hom 零単体公式を使う。
規約：辺の厳密な等式。使われ方：frame 単位点の正規化の終端。 -/
lemma kanHammockHomPinchedMap_arrow_zero (f : X ⟶ Y) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap C X Y).app (op ⦋0⦌) PUnit.unit)).val =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap C).app (op ⦋1⦌) (ComposableArrows.mk₁ f) := by
  simp only [NatTrans.comp_app_apply, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso_hom_val]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex_zero_edge]
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_arrow]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge]
  congr 2
  apply (SimplicialCategory.homEquiv' _ _).injective
  rw [Equiv.apply_symm_apply]
  have h := congrArg (fun a => a.app (op ⦋0⦌) PUnit.unit)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor_homTo C f)
  exact h.symm

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
