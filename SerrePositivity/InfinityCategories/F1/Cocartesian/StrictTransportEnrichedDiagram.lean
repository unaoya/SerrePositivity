module

public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionsNaturality
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianStrictTransport

/-!
概要：元の全 fibration の strict transport を、底全体の quasicategory 値豊穣図式へ束ねる。
方針：under の前合成を比較とし、元の全 section 作用の自然性を使う。
規約：底と全 fibration の全 Hom を同時に保持する。
使われ方：同じ分類主写像と底変換後の主写像の coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 元の strict transport の全対象・全射・全高次 Hom を、底全体の豊穣図式として扱う。 -/
def cocartesianStrictTransportEnrichedDiagram (C : Type u) [Category.{u} C] :
    QuasicategoryEnrichedDiagram (CocartesianFibrationObject (nerve C)) C where
  obj c := cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget c)))
  map {c d} f := by
    refine ⟨fun p ↦ kanCocartesianStrictTransportMap p.val.hom f, ?_⟩
    intro p q
    change (kanCocartesianStrictTransportMap p.val.hom f ▷ _) ≫
        uncurry (cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget d))) p.val q.val) =
      uncurry (cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget c))) p.val q.val) ≫
        kanCocartesianStrictTransportMap q.val.hom f
    rw [cocartesianSectionsPostHom, uncurry_curry, cocartesianSectionsPostHom, uncurry_curry]
    exact (cocartesianSectionsAction_overPre
      (Over.homMk (nerveUnderMap f) (nerveUnderMap_projection f) :
        Over.mk (nerveMap (Under.forget d)) ⟶ Over.mk (nerveMap (Under.forget c)))
      p.val q.val).symm
  map_id c p := kanCocartesianStrictTransportMap_id p.val.hom c
  map_comp f g p := kanCocartesianStrictTransportMap_comp p.val.hom f g

end SerrePositivity.InfinityCategories
