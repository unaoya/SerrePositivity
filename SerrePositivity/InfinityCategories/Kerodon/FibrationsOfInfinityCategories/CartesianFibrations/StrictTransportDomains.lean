module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveStraighteningUnit

/-!
概要：strict transport の under の定義域を底上の反変図式として表示する。
方針：under の忘却を図式へ束ね、相対切断の豊穣評価を既存の strict transport と同定する。
規約：全対象と全高次の Hom の厳密な等式を使う。
使われ方：底変換した切断の共同実現と既存の分類関手を接続する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- under の忘却を、通常の圏の nerve 上の反変な定義域図式へ束ねる。 -/
def strictTransportDomains (C : Type u) [Category.{u} C] : Cᵒᵖ ⥤ Over (nerve C) where
  obj s := Over.mk (nerveMap (Under.forget s.unop))
  map f := Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f.unop) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f.unop)
  map_id s := by
    apply Over.OverMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_id s.unop
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_comp g.unop f.unop

/-- under の切断評価の豊穣関手は、既存 strict transport の豊穣関手そのもの。 -/
lemma strictTransportDomains_toEnrichedFunctor (C : Type u) [Category.{u} C] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (strictTransportDomains C)).toEnrichedFunctor =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportEnriched (C := C)).comp SSet _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportKanDiagramEnriched := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro p q
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- under の切断図式の共同実現は、既存の coherent straightening の射と厳密に一致する。 -/
lemma strictTransportDomains_realization (C : Type u) [Category.{u} C] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (strictTransportDomains C)).realization =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.realization, strictTransportDomains_toEnrichedFunctor,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportKanDiagramEnriched_realization]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportInfinityMap_realization C

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
