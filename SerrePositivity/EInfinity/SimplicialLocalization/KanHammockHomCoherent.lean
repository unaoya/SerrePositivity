module

public import SerrePositivity.EInfinity.FrameHom.EnrichedHomRealization
public import SerrePositivity.EInfinity.FrameHom.KanHomFamily
public import SerrePositivity.EInfinity.FrameHom.SourceRoofFamily
public import SerrePositivity.EInfinity.Hammock.ExInfinityPointActions
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockSourceFunctor

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SSet Opposite MonoidalCategory Hammock
open SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.FrameHom
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

/-- 概要：元の Kan hammock の通常の後合成は元の後合成写像の Ex∞ 像。
方針：同じ源関手の実 Hom 点と monoidal 移送の後合成を照合する。
規約：元の通常射自身。使われ方：全 Hom 図式の厳密な同定。 -/
lemma kanHammock_sHomWhiskerLeft {Y Z : C.category} (f : Y ⟶ Z) :
    eHomWhiskerLeft SSet ((kanHammockSourceFunctor C).obj X)
      ((kanHammockSourceFunctor C).map f) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f)) := by
  change (ρ_ _).inv ≫ _ ◁ ForgetEnrichment.homTo SSet
    ((kanHammockSourceFunctor C).map f) ≫
      Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences Y Z) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition C.weakEquivalences X Y Z) = _
  rw [kanHammockSourceFunctor_homTo]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap, id_tensorHom] using
    (exInfinity_postcompose_point (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition C.weakEquivalences X Y Z)).symm

/-- 概要：同じ元の Kan hammock Hom 関手の coherent nerve 全体での実現。
方針：同じ元の豊穣 Hom 関手へ全単体の後合成を適用する。
規約：始点は同じ元の局所化頂点。
使われ方：正本の共変 Hom 関手への Yoneda 比較の始域。 -/
def kanHammockHomCoherent : SSet.uliftFunctor.{u + 1, u}.obj (kanHammockNerve C) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := enrichedHomCoherent ((kanHammockSourceFunctor C).obj X)

/-- 概要：元の豊穣 Hom の通常制限は元の strict Kan hammock Hom 図式そのもの。
方針：各対象の厳密な一致と同じ全後合成公式を使う。
規約：全射と全単体の実関手等式。使われ方：coherent 実現の全制限。 -/
lemma kanHammockHomOrdinaryFamily_eq :
    kanHammockSourceFunctor C ⋙
        enrichedHomOrdinaryFamily ((kanHammockSourceFunctor C).obj X) =
      kanHomFamily (hammockHomFamily C.weakEquivalences X) := by
  have ho : ∀ Y, (kanHammockSourceFunctor C ⋙
      enrichedHomOrdinaryFamily ((kanHammockSourceFunctor C).obj X)).obj Y =
        (kanHomFamily (hammockHomFamily C.weakEquivalences X)).obj Y := fun _ => rfl
  apply CategoryTheory.Functor.hext ho
  intro Y Z f
  apply heq_of_eq
  exact (enrichedHomOrdinaryFamily_map (D := KanHammockCategory C)
    ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).map f)).trans
      (kanHammock_sHomWhiskerLeft C X f)

/-- 概要：同じ全 hammock 局所化での制限は元の strict Kan Hom 図式の coherent 実現。
方針：全豊穣 Hom の通常制限と同じ局所化源関手を全次数で合成する。
規約：点ごとの比較なし。
使われ方：S (6) の終端図式から同じ Yoneda 比較への接続。 -/
lemma kanHammockHomCoherent_source :
    SSet.uliftFunctor.{u + 1, u}.map (hammockLocalizationNerveMap C) ≫
      kanHammockHomCoherent C X =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (kanHomFamily (hammockHomFamily C.weakEquivalences X)) := by
  rw [hammockLocalizationNerveMap, Functor.map_comp, Category.assoc,
    kanHammockHomCoherent, enrichedHomCoherent_ordinary,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_precomp, kanHammockHomOrdinaryFamily_eq]

end SerrePositivity.EInfinity.SimplicialLocalization
