module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RelativeHammockEnriched
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockSourceFunctor
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentUnderlyingHo

/-!
概要：同じ相対関手の全 hammock 比較は元の局所化源の射と整合する。
方針：元の通常射の一定単体と Ex∞ 単位の自然性を使う。
規約：全関手の等式と同じ零単体・辺を保持する。
使われ方：指定局所化三角形の二胞体への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.SerrePositivity.InfinityCategories
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
  (F : LocalizerMorphism C.weakEquivalences D.weakEquivalences)

/-- 概要：元の相対関手の全 Hom 比較は元の通常射の一定単体を保持する。
方針：同じ全次数の一定点の保存を使う。
規約：元の射の実像。使われ方：元の局所化辺の照合。 -/
lemma relativeHammockEnriched_arrowMap {X Y : C.category} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap D.weakEquivalences (F.functor.map f) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.arrowPoint_map F f n

/-- 概要：元の相対関手の通常射の作用は同じ Kan 豊穣作用と一致する。
方針：元の Hom の単位からの射を回収し、Ex∞ の自然性を使う。
規約：全対象・全射の関手等式。使われ方：全 coherent nerve 三角形。 -/
lemma relativeKanHammockSourceFunctor :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockFunctor F) =
        F.functor ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor D := by
  have ho (X : C.category) :
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockFunctor F)).obj X =
          (F.functor ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor D).obj X := rfl
  apply Functor.hext ho
  intro X Y f
  apply heq_of_eq
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockFunctor F)).map
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f) = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor D).map (F.functor.map f)
  apply (eHomEquiv SSet).injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedUnderlying_eHom_map]
  change (ForgetEnrichment.homTo SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y) =
      ForgetEnrichment.homTo SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor D).map (F.functor.map f))
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor_homTo, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor_homTo,
    Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality, Functor.id_map, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeHammockEnriched_arrowMap]

/-- 概要：元の局所化源は同じ全 hammock coherent nerve 比較と可換。
方針：元の通常関手等式と coherent 表示の豊穣自然性を合成する。
規約：全単体の厳密な三角形。使われ方：指定二胞体を保つ局所化比較。 -/
lemma relativeKanHammockNerve_source :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap C ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve F =
      nerveMap F.functor ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap D := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveToCoherent_enriched_naturality,
    ← Category.assoc]
  change nerveMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockFunctor F)) ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockSourceFunctor]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
