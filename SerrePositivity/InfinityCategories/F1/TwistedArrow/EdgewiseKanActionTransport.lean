module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseReflectedHomParameter
public import SerrePositivity.InfinityCategories.F1.Coherent.LeftIntervalNaturality
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedKanParameterizedAction
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOppositeKanComparison
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedFunctor

/-!
概要：直接の Kan 作用と、Hom の共通解像上の coherent な反転図式の同じ辺の照合。
方針：左端を反転したパラメーターで作用を評価し、左 Hom の豊穣自然性を使う。
規約：共通 Hom の反転を保持し、図式の対象ごとの逆同値は仮定しない。
使われ方：pointed 自然性の輸送を、共同反転比較と同じ coherent な族へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 直接の Kan の評価を、同じ反転した共通 Hom パラメーターで表した辺の族。 -/
def edgewiseKanActionInterval (K L : KanObject.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision ((ihom K.obj).obj L.obj))).op ⟶
      intervalMappingSpace (spaceInfinityVertex (kanObjectOpFunctor.obj K))
        (spaceInfinityVertex (kanObjectOpFunctor.obj L)) :=
  edgewiseReflectedHomParameter K.obj L.obj ≫
    kanParameterizedLeftHomInterval (X := K) (Y := L)
      (uncurry (𝟙 ((ihom K.obj).obj L.obj)))

/-- 同じ辺の族を展開すると、共同反転図式の実際の coherent Hom の区間族となる。 -/
lemma edgewiseKanActionInterval_uncurry (K L : KanObject.{u}) :
    intervalMappingUncurry (edgewiseKanActionInterval K L) =
      coherentLeftHomInterval (C := EdgewiseEnrichedObject KanObject.{u})
        (⟨K, trivial⟩ : EdgewiseEnrichedObject KanObject.{u})
        (⟨L, trivial⟩ : EdgewiseEnrichedObject KanObject.{u}) ≫
          edgewiseOppositeKanInfinityMap := by
  change intervalMappingUncurry (edgewiseReflectedHomParameter K.obj L.obj ≫
    kanParameterizedLeftHomInterval (X := K) (Y := L)
      (uncurry (𝟙 ((ihom K.obj).obj L.obj)))) = _
  rw [intervalMappingUncurry_precomp]
  unfold kanParameterizedLeftHomInterval
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_curryOfEndpoints,
    ← whiskerLeft_comp_assoc, edgewiseReflectedHomParameter_reverse,
    pointedReverseKanHomInterval_eq_left]
  exact (coherentLeftHomInterval_enriched_naturality edgewiseOppositeKanEnriched
    (⟨K, trivial⟩ : EdgewiseEnrichedObject KanObject.{u})
    (⟨L, trivial⟩ : EdgewiseEnrichedObject KanObject.{u})).symm

/-- 任意の豊穣 Kan 値図式でも、同じ共通 Hom の辺は図式全体への後合成と厳密に一致する。 -/
lemma edgewiseKanActionInterval_enriched_uncurry {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C KanObject.{u}) (X Y : C) :
    intervalMappingUncurry
      (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
        (edgewiseSubdivisionMap (F.map X Y))) ≫ edgewiseKanActionInterval (F.obj X) (F.obj Y)) =
      coherentLeftHomInterval (C := EdgewiseEnrichedObject C)
        (⟨X, trivial⟩ : EdgewiseEnrichedObject C) (⟨Y, trivial⟩ : EdgewiseEnrichedObject C) ≫
      coherentNerveMap (edgewiseEnrichedFunctor F) ≫ edgewiseOppositeKanInfinityMap := by
  rw [intervalMappingUncurry_precomp, edgewiseKanActionInterval_uncurry]
  have h := coherentLeftHomInterval_enriched_naturality (edgewiseEnrichedFunctor F)
    (⟨X, trivial⟩ : EdgewiseEnrichedObject C) (⟨Y, trivial⟩ : EdgewiseEnrichedObject C)
  have h' := congrArg (fun k ↦ k ≫ edgewiseOppositeKanInfinityMap) h
  simpa only [Category.assoc, edgewiseEnrichedFunctor] using h'.symm

/-- 共通 Hom の同じ coherent な辺に沿う pointed 輸送は、元の Kan の直接の評価と比較できる。 -/
def edgewiseKanAction_transportIso {P : SSet.{u + 1}} (K L : KanObject.{u})
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
    (t : P ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision ((ihom K.obj).obj L.obj))).op) :
    FunctorIso
      (lift x (t ≫ edgewiseReflectedHomParameter K.obj L.obj) ≫
        (HomotopyLimits.uliftTensorIso K.obj ((ihom K.obj).obj L.obj)).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (uncurry (𝟙 ((ihom K.obj).obj L.obj))) ≫
          pointedSpaceLeftResolutionComparison L)
      (diagonalFiberTransport pointedSpaceProjection
        (x ≫ pointedSpaceLeftResolutionComparison K) (t ≫ edgewiseKanActionInterval K L)) :=
  pointedSpaceLeftResolution_parametrizedTransportIso
    (X := K) (Y := L) (uncurry (𝟙 ((ihom K.obj).obj L.obj)))
      x (t ≫ edgewiseReflectedHomParameter K.obj L.obj)

end SerrePositivity.InfinityCategories
