module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseKanActionTransport

/-!
概要：豊穣 Kan 値図式の実際の作用と、同じ共同反転図式の pointed 輸送の比較。
方針：反転した左端の自然性で Hom の作用を戻し、既存の全対象の反転比較を合成する。
規約：元の豊穣圏の局所 Kan 性は不要。元の図式と同じ Hom の共通解像を保つ。
使われ方：相対 Hom の双関手の始域とテスト標的を同時に動かす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ共通解像上で、元の豊穣 Kan 値図式全体と共同反転図式全体を結ぶ関手同型。 -/
def edgewiseEnrichedKanDiagramIso {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C KanObject.{u}) :
    FunctorIso (edgewiseEnrichedInfinityMap C ≫ coherentNerveMap F)
      (coherentNerveMap (edgewiseEnrichedFunctor F) ≫ edgewiseOppositeKanInfinityMap) := by
  have e := edgewiseKanOppositeInfinityComparisonIso.precomp
    (coherentNerveMap (edgewiseEnrichedFunctor F))
  rw [edgewiseEnrichedFunctor_infinity_right F] at e
  exact e

/-- 図式の実際の Hom の作用を展開した辺は、同じ共同反転図式の辺に一致する。 -/
lemma edgewiseEnrichedKanActionInterval {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C KanObject.{u}) (X Y : C) :
    edgewiseReflectedParameter (SimplicialCategory.sHom X Y) ≫
      kanParameterizedLeftHomInterval (X := F.obj X) (Y := F.obj Y) (uncurry (F.map X Y)) =
    SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseSubdivisionMap (F.map X Y))) ≫ edgewiseKanActionInterval (F.obj X) (F.obj Y) := by
  unfold edgewiseKanActionInterval kanParameterizedLeftHomInterval
  change edgewiseReflectedParameter (SimplicialCategory.sHom X Y) ≫
      leftPointHomReverseParameter (uncurry (F.map X Y)) ≫ _ =
    SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseSubdivisionMap (F.map X Y))) ≫
      edgewiseReflectedParameter ((ihom (F.obj X).obj).obj (F.obj Y).obj) ≫
        leftPointHomReverseParameter (uncurry (𝟙 ((ihom (F.obj X).obj).obj (F.obj Y).obj))) ≫ _
  rw [← leftPointHomReverseParameter_uncurry]
  simp only [← Category.assoc]
  exact congrArg (fun k ↦ (k ≫ leftPointHomReverseParameter
    (uncurry (𝟙 ((ihom (F.obj X).obj).obj (F.obj Y).obj)))) ≫
      intervalMappingCurryOfEndpoints
        (pointedReverseKanHomInterval (kanObjectOpFunctor.obj (F.obj X))
          (kanObjectOpFunctor.obj (F.obj Y)))
        (pointedReverseKanHomInterval_zero (kanObjectOpFunctor.obj (F.obj X))
          (kanObjectOpFunctor.obj (F.obj Y)))
        (pointedReverseKanHomInterval_one (kanObjectOpFunctor.obj (F.obj X))
          (kanObjectOpFunctor.obj (F.obj Y))))
    (edgewiseReflectedParameter_naturality (F.map X Y)).symm

/-- 実際の Hom 作用の同じ辺の族は、共同反転図式全体への後合成で表される。 -/
lemma edgewiseEnrichedKanActionInterval_uncurry {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C KanObject.{u}) (X Y : C) :
    intervalMappingUncurry (edgewiseReflectedParameter (SimplicialCategory.sHom X Y) ≫
      kanParameterizedLeftHomInterval (X := F.obj X) (Y := F.obj Y) (uncurry (F.map X Y))) =
      coherentLeftHomInterval (C := EdgewiseEnrichedObject C)
        (⟨X, trivial⟩ : EdgewiseEnrichedObject C) (⟨Y, trivial⟩ : EdgewiseEnrichedObject C) ≫
      coherentNerveMap (edgewiseEnrichedFunctor F) ≫ edgewiseOppositeKanInfinityMap := by
  rw [edgewiseEnrichedKanActionInterval]
  exact edgewiseKanActionInterval_enriched_uncurry F X Y

/-- 同じ共同反転図式の辺に沿う輸送は、図式の実際の Hom の作用と関手同型。 -/
def edgewiseEnrichedKanAction_transportIso {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C KanObject.{u}) (X Y : C) {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (F.obj X).obj)
    (t : P ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom X Y))).op) :
    FunctorIso
      (lift x (t ≫ edgewiseReflectedParameter (SimplicialCategory.sHom X Y)) ≫
        (HomotopyLimits.uliftTensorIso (F.obj X).obj (SimplicialCategory.sHom X Y)).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (uncurry (F.map X Y)) ≫
          pointedSpaceLeftResolutionComparison (F.obj Y))
      (diagonalFiberTransport pointedSpaceProjection
        (x ≫ pointedSpaceLeftResolutionComparison (F.obj X))
        (t ≫ SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
          (edgewiseSubdivisionMap (F.map X Y))) ≫
            edgewiseKanActionInterval (F.obj X) (F.obj Y))) := by
  have e := pointedSpaceLeftResolution_parametrizedTransportIso
    (X := F.obj X) (Y := F.obj Y) (uncurry (F.map X Y))
      x (t ≫ edgewiseReflectedParameter (SimplicialCategory.sHom X Y))
  rw [Category.assoc t, edgewiseEnrichedKanActionInterval F X Y] at e
  exact e

end SerrePositivity.InfinityCategories
