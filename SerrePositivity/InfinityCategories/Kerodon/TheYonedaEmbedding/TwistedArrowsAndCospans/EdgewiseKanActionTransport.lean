module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseReflectedHomParameter
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.LeftIntervalNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedKanParameterizedAction
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOppositeKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEnrichedFunctor

/-!
概要：直接の Kan 作用と、Hom の共通解像上の coherent な反転図式の同じ辺の照合。
方針：左端を反転したパラメーターで作用を評価し、左 Hom の豊穣自然性を使う。
規約：共通 Hom の反転を保持し、図式の対象ごとの逆同値は仮定しない。
使われ方：pointed 自然性の輸送を、共同反転比較と同じ coherent な族へ接続する。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 直接の Kan の評価を、同じ反転した共通 Hom パラメーターで表した辺の族。 -/
def edgewiseKanActionInterval (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision ((ihom K.obj).obj L.obj))).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj L)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedHomParameter K.obj L.obj ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanParameterizedLeftHomInterval (X := K) (Y := L)
      (uncurry (𝟙 ((ihom K.obj).obj L.obj)))

/-- 同じ辺の族を展開すると、共同反転図式の実際の coherent Hom の区間族となる。 -/
lemma edgewiseKanActionInterval_uncurry (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (edgewiseKanActionInterval K L) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval (C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
        (⟨K, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
        (⟨L, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanInfinityMap := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedHomParameter K.obj L.obj ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanParameterizedLeftHomInterval (X := K) (Y := L)
      (uncurry (𝟙 ((ihom K.obj).obj L.obj)))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanParameterizedLeftHomInterval
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints,
    ← whiskerLeft_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedHomParameter_reverse,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanHomInterval_eq_left]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_enriched_naturality _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnriched
    (⟨K, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (⟨L, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})).symm

/-- 任意の豊穣 Kan 値図式でも、同じ共通 Hom の辺は図式全体への後合成と厳密に一致する。 -/
lemma edgewiseKanActionInterval_enriched_uncurry {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (F.map X Y))) ≫ edgewiseKanActionInterval (F.obj X) (F.obj Y)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval (C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C)
        (⟨X, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) (⟨Y, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseEnrichedFunctor F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanInfinityMap := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, edgewiseKanActionInterval_uncurry]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_enriched_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseEnrichedFunctor F)
    (⟨X, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) (⟨Y, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C)
  have h' := congrArg (fun k ↦ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanInfinityMap) h
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseEnrichedFunctor] using h'.symm

/-- 共通 Hom の同じ coherent な辺に沿う pointed 輸送は、元の Kan の直接の評価と比較できる。 -/
def edgewiseKanAction_transportIso {P : SSet.{u + 1}} (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
    (t : P ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision ((ihom K.obj).obj L.obj))).op) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (lift x (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedHomParameter K.obj L.obj) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K.obj ((ihom K.obj).obj L.obj)).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (uncurry (𝟙 ((ihom K.obj).obj L.obj))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionComparison L)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.diagonalFiberTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
        (x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionComparison K) (t ≫ edgewiseKanActionInterval K L)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolution_parametrizedTransportIso
    (X := K) (Y := L) (uncurry (𝟙 ((ihom K.obj).obj L.obj)))
      x (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedHomParameter K.obj L.obj)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
