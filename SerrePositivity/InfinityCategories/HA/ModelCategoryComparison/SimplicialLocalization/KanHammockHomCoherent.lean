module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.EnrichedHomRealization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.KanHomFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceRoofFamily
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ExInfinityPointActions
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockSourceFunctor

/-!
概要：元の strict Kan hammock Hom 図式を同じ豊穣 Hom 関手の coherent 実現へ同定する。
方針：元の Ex∞ 単位と lax monoidal 後合成の等式を全自然性に使う。
規約：点ごとの Hom 同値を使わず、全図式の厳密な等式を構成する。
使われ方：Yoneda 側の全比較を S (6) の終端へ代入する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SSet _root_.Opposite _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

/-- 概要：元の Kan hammock の通常の後合成は元の後合成写像の Ex∞ 像。
方針：同じ源関手の実 Hom 点と monoidal 移送の後合成を照合する。
規約：元の通常射自身。使われ方：全 Hom 図式の厳密な同定。 -/
lemma kanHammock_sHomWhiskerLeft {Y Z : C.category} (f : Y ⟶ Z) :
    eHomWhiskerLeft SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f)) := by
  change (ρ_ _).inv ≫ _ ◁ ForgetEnrichment.homTo SSet
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f) ≫
      Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences Y Z) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition C.weakEquivalences X Y Z) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor_homTo]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap, id_tensorHom] using
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.exInfinity_postcompose_point (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition C.weakEquivalences X Y Z)).symm

/-- 概要：同じ元の Kan hammock Hom 関手の coherent nerve 全体での実現。
方針：同じ元の豊穣 Hom 関手へ全単体の後合成を適用する。
規約：始点は同じ元の局所化頂点。
使われ方：正本の共変 Hom 関手への Yoneda 比較の始域。 -/
def kanHammockHomCoherent : SSet.uliftFunctor.{u + 1, u}.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve C) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomCoherent ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)

/-- 概要：元の豊穣 Hom の通常制限は元の strict Kan hammock Hom 図式そのもの。
方針：各対象の厳密な一致と同じ全後合成公式を使う。
規約：全射と全単体の実関手等式。使われ方：coherent 実現の全制限。 -/
lemma kanHammockHomOrdinaryFamily_eq :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C ⋙
        _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomOrdinaryFamily ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X) =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.hammockHomFamily C.weakEquivalences X) := by
  have ho : ∀ Y, (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C ⋙
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomOrdinaryFamily ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)).obj Y =
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.hammockHomFamily C.weakEquivalences X)).obj Y := fun _ => rfl
  apply CategoryTheory.Functor.hext ho
  intro Y Z f
  apply heq_of_eq
  exact (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomOrdinaryFamily_map (D := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C)
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f)).trans
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammock_sHomWhiskerLeft C X f)

/-- 概要：同じ全 hammock 局所化での制限は元の strict Kan Hom 図式の coherent 実現。
方針：全豊穣 Hom の通常制限と同じ局所化源関手を全次数で合成する。
規約：点ごとの比較なし。
使われ方：S (6) の終端図式から同じ Yoneda 比較への接続。 -/
lemma kanHammockHomCoherent_source :
    SSet.uliftFunctor.{u + 1, u}.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap C) ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomCoherent C X =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.hammockHomFamily C.weakEquivalences X)) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap, Functor.map_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomCoherent, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomCoherent_ordinary,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_precomp, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomOrdinaryFamily_eq]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
