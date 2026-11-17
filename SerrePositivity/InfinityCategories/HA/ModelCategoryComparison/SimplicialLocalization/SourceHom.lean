module

public import SerrePositivity.EInfinity.Interface.Core
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationNerveSource
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockArrowPoint
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanComponents
public import SerrePositivity.EInfinity.Hammock.CoherentComponents
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveLocalObjects
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality

/-!
# 単体的局所化での厳密な射の代表

## 概要
普通の局所化において厳密射で表せる射を、
同じ厳密射による ∞ 局所化の辺の類で表す。

## 方針
Dwyer–Kan の比較で生成射を共通の自由 hammock の射に持ち上げ、
両側で評価する。

## 規約
同じ相対圏と同じ局所化源を使う。

## 使われ方
HA §3.2.2 の Barratt–Eccles 忘却関手の保存性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 厳密射から得る既存 Kan 局所化の生成射。 -/
def kanLocalizationStrictHom {X Y : C.category} (f : X ⟶ Y) :
    (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C from X) ⟶ (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C from Y) :=
  ForgetEnrichment.homOf SSet (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationObjects C)
    (X := X) (Y := Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint C f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y))

/-- 厳密射を持ち上げる既存の Kan 自由 hammock の射。 -/
def kanFreeHammockStrictHom {X Y : C.category} (f : X ⟶ Y) :
    (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockCategory C from X) ⟶ (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockCategory C from Y) :=
  ForgetEnrichment.homOf SSet (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockObjects C)
    (X := X) (Y := Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint C f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonal C X Y))

/-- 持ち上げた厳密射の DK 側の像。 -/
lemma kanFreeHammockStrictHom_comparison {X Y : C.category} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonFunctor C).forget.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom C f) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f := by
  simp only [EnrichedFunctor.forget_map, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom, ForgetEnrichment.homTo_homOf]
  change ForgetEnrichment.homOf SSet (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationObjects C) (X := X) (Y := Y)
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint C f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonEnriched C).map X Y) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonEnriched_map, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality, Functor.id_map,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint_comparison]
  rfl

/-- 持ち上げた厳密射の hammock 側の像。 -/
lemma kanFreeHammockStrictHom_augmentation {X Y : C.category} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationFunctor C).forget.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom C f) =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f := by
  apply Function.LeftInverse.injective (ForgetEnrichment.homOf_homTo SSet)
  simp only [EnrichedFunctor.forget_map, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom, ForgetEnrichment.homTo_homOf]
  change
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint C f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationEnriched C).map X Y) =
    ForgetEnrichment.homTo SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f)
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor_homTo,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationEnriched_map, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality, Functor.id_map,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint_augmentation]

/-- Kan 化した同じ生成射の成分は普通の局所化の射。 -/
lemma kanLocalizationStrictHom_components {X Y : C.category} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationHomPiZeroEquiv C X Y
      (SSet.π₀.mk (SimplicialCategory.homEquiv'
        (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C from X) (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f))) = C.weakEquivalences.Q.map f := by
  refine Eq.trans ?_ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationHomPiZeroEquiv_arrow C f)
  apply congrArg (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationHomPiZeroEquiv C X Y)
  change SSet.π₀.mk (SSet.unitHomEquiv _
    (ForgetEnrichment.homTo SSet (ForgetEnrichment.homOf SSet
      (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationObjects C) (X := X) (Y := Y)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint C f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _)))) =
    SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _).app _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowZero C f))
  apply congrArg SSet.π₀.mk
  rw [ForgetEnrichment.homTo_homOf, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.unitPointMap_comp]
  exact (SSet.unitHomEquiv _).apply_symm_apply _


/-- 同じ相対圏の対象の自由 hammock での頂点。 -/
def freeHammockVertex (X : C.category) : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockNerve C) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockCategory C from X)

/-- 自由 hammock の頂点を元の源の頂点へ合わせる。 -/
lemma freeHammockAugmentation_source (X : C.category) :
    _root_.SerrePositivity.EInfinity.atVertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationNerve C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockVertex C X) =
      _root_.SerrePositivity.EInfinity.atVertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationFunctor C)
    (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockCategory C from X)).trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_vertex C X).symm

/-- 自由 hammock の頂点を DK 局所化の頂点へ合わせる。 -/
lemma freeHammockComparison_vertex (X : C.category) :
    _root_.SerrePositivity.EInfinity.atVertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonNerve C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockVertex C X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C from X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonFunctor C)
    (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockCategory C from X)

/-- 自由 hammock の比較を、指定された局所化源の頂点で評価する。 -/
def localizationStrictSourceIso (X : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.EInfinity.atVertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C from X)) :=
  eqToIso (congrArg (fun x => SSet.HomotopyCategory.mk
    (_root_.SerrePositivity.EInfinity.atVertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationEquivalence C).hom x))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation_source C X).symm) ≪≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationComparison C).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockVertex C X) ≪≫
        eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockComparison_vertex C X))

/-- 自由 hammock の同じ辺を二つの比較関手で評価した自然性の四角形。 -/
lemma localizationStrictSourceIso_naturality {X Y : C.category} (f : X ⟶ Y) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap C)).toFunctor.map
      (SSet.HomotopyCategory.homMk (nerve.edgeMk f)) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationStrictSourceIso C Y).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationStrictSourceIso C X).hom ≫
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f)) := by
  let G := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationNerve C
  let H := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationEquivalence C).hom
  let K := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonNerve C
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom C f)
  let b := (nerve.edgeMk f).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap C)
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f)
  have ha : (a.map G).edge = ((nerve.edgeMk f).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap C)).edge := by
    change G.app (Opposite.op ⦋1⦌) a.edge =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_arrow]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationFunctor C)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom C f) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f)
      (by rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom_augmentation]; rfl)
  have hb : (a.map K).edge = c.edge :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonFunctor C)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom C f) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f)
      (by rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom_comparison]; rfl)
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport
    (congrArg (_root_.SerrePositivity.EInfinity.atVertex H ·) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation_source C X))
    (congrArg (_root_.SerrePositivity.EInfinity.atVertex H ·) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation_source C Y))
    (a.map (G ≫ H)).toTruncated b.toTruncated
    (congrArg (H.app (Opposite.op ⦋1⦌)) ha)
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockComparison_vertex C X)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockComparison_vertex C Y) (a.map K).toTruncated c.toTruncated hb
  have hn := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationComparison C).toNatIso.hom.naturality
    (SSet.HomotopyCategory.homMk a)
  change SSet.HomotopyCategory.homMk (a.map (G ≫ H)) ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationComparison C).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockVertex C Y)).hom =
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationComparison C).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockVertex C X)).hom ≫
      SSet.HomotopyCategory.homMk (a.map K) at hn
  change SSet.Truncated.HomotopyCategory.homMk b.toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationStrictSourceIso C Y).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationStrictSourceIso C X).hom ≫
      SSet.Truncated.HomotopyCategory.homMk c.toTruncated
  rw [← hs, ← ht]
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationStrictSourceIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h := congrArg (fun m =>
    eqToHom (congrArg (fun x => SSet.HomotopyCategory.mk (_root_.SerrePositivity.EInfinity.atVertex H x))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation_source C X).symm) ≫ m ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockComparison_vertex C Y))) hn
  simpa only [Category.assoc, SSet.HomotopyCategory.homMk, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap, H] using h

/-- 通常の局所化 Hom を厳密射で表せば、同じ射で ∞ 側の Hom を表せる。 -/
lemma localizationStrictHom_represent {X Y : C.category}
    (h : Function.Surjective (C.weakEquivalences.Q.map : (X ⟶ Y) → _))
    (g : SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C from X)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C from Y))) :
    ∃ f : X ⟶ Y,
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f)) = g := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ g
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (SSet.Edge.ofTruncated e)
  obtain ⟨f, hf⟩ := h (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationHomPiZeroEquiv C X Y
    (SSet.π₀.mk (SimplicialCategory.homEquiv' _ _ k)))
  refine ⟨f, ?_⟩
  have he := _root_.SerrePositivity.EInfinity.Hammock.coherentEdge_homMk_eq_of_components (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f) k
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationHomPiZeroEquiv C X Y).injective
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom_components C f).trans hf))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom] at he
  exact he

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
