module

public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveStraighteningUnit

/-!
概要：strict transport の under の定義域を底上の反変図式として表示する。
方針：under の忘却を図式へ束ね、相対切断の豊穣評価を既存の strict transport と同定する。
規約：全対象と全高次の Hom の厳密な等式を使う。
使われ方：底変換した切断の共同実現と既存の分類関手を接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- under の忘却を、通常の圏の nerve 上の反変な定義域図式へ束ねる。 -/
def strictTransportDomains (C : Type u) [Category.{u} C] : Cᵒᵖ ⥤ Over (nerve C) where
  obj s := Over.mk (nerveMap (Under.forget s.unop))
  map f := Over.homMk (nerveUnderMap f.unop) (nerveUnderMap_projection f.unop)
  map_id s := by
    apply Over.OverMorphism.ext
    exact nerveUnderMap_id s.unop
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact nerveUnderMap_comp g.unop f.unop

/-- under の切断評価の豊穣関手は、既存 strict transport の豊穣関手そのもの。 -/
lemma strictTransportDomains_toEnrichedFunctor (C : Type u) [Category.{u} C] :
    (relativeSectionEnrichedDiagram (strictTransportDomains C)).toEnrichedFunctor =
      (leftStrictTransportEnriched (C := C)).comp SSet strictTransportKanDiagramEnriched := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro p q
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- under の切断図式の共同実現は、既存の coherent straightening の射と厳密に一致する。 -/
lemma strictTransportDomains_realization (C : Type u) [Category.{u} C] :
    (relativeSectionEnrichedDiagram (strictTransportDomains C)).realization =
      leftStraighteningCoherentMap C := by
  rw [KanEnrichedDiagram.realization, strictTransportDomains_toEnrichedFunctor,
    coherentNerveMap_comp, Category.assoc, strictTransportKanDiagramEnriched_realization]
  exact leftStrictTransportInfinityMap_realization C

end SerrePositivity.InfinityCategories
