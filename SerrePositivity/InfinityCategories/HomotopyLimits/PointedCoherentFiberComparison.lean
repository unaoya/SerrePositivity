module

public import SerrePositivity.InfinityCategories.F1.Weighted.CosliceTransport
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedFiberTransportCoordinates

/-!
概要：元の Kan 複体の coherent 頂点上で、反転した一点 Hom と普遍 fiber を比較する。
方針：coherent な coslice 比較の始点だけを既存の一点空間の表示へ移す。
規約：終点 K と元の射 f を反転しない。使われ方：二項積の二射影の fiber 作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の K の coherent 頂点で、一点 coslice の始点表示を既存のものに揃える。 -/
def pointedCoherentFiberIso (K : KanObject.{u}) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm
      (coherentNerveVertex pointKanObject))) (coherentNerveVertex K) ≅
        vertexFiber pointedSpaceProjection (coherentNerveVertex K) :=
  cosliceFiberVerticesIso (spaceInfinityVertex_eq_coherent pointKanObject).symm rfl

/-- 元の K の反転した一点 Hom から、同じ K 上の普遍 fiber への標準比較。 -/
def pointedCoherentFiberComparison (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K).op ⟶
      vertexFiber pointedSpaceProjection (coherentNerveVertex K) :=
  coherentCosliceFiberComparison pointKanObject K ≫ (pointedCoherentFiberIso K).hom

/-- 既存の標準比較と始点表示の同型から、構成した実際の比較射は同値。 -/
lemma pointedCoherentFiberComparison_isQCatEquivalence (K : KanObject.{u}) :
    IsQCatEquivalence (pointedCoherentFiberComparison K) :=
  (coherentCosliceFiberComparison_homotopyEquivalence pointKanObject K).isQCatEquivalence.comp
    (qCatEquivalenceOfIso (pointedCoherentFiberIso K)).isQCatEquivalence

/-- 元の Kan 射の反転した一点 Hom 作用は、同じ coherent 辺の普遍輸送と可換。 -/
def pointedCoherentFiberComparison_transportIso {K L : KanObject.{u}} (f : K ⟶ L) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)) ≫
          pointedCoherentFiberComparison L)
      (pointedCoherentFiberComparison K ≫ edgeTransport pointedSpaceProjection
        (coherentNerveEdge f)) := by
  let F : ULift.{u} (Fin 2) ⥤ KanObject.{u} :=
    (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
      ComposableArrows.mk₁ f
  have e := (coherentCosliceFiberComparison_transportIso F pointKanObject
    (homOfLE (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≤ ULift.up 1
      from by decide))).postcomp (pointedCoherentFiberIso L).hom
  have h := cosliceFiberVerticesIso_transport
    (spaceInfinityVertex_eq_coherent pointKanObject).symm rfl rfl (coherentNerveEdge f)
  have he : (coherentNerveEdge f).ofEq rfl rfl = coherentNerveEdge f := by
    apply SSet.Edge.ext
    rfl
  rw [he] at h
  change (pointedCoherentFiberIso K).hom ≫ edgeTransport pointedSpaceProjection _ =
    edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
      (coherentNerveVertex pointKanObject))) _ ≫ (pointedCoherentFiberIso L).hom at h
  change FunctorIso
    (((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)) ≫
        coherentCosliceFiberComparison pointKanObject L) ≫ (pointedCoherentFiberIso L).hom)
    ((coherentCosliceFiberComparison pointKanObject K ≫
      edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex pointKanObject))) (coherentNerveEdge f)) ≫
          (pointedCoherentFiberIso L).hom) at e
  simpa only [pointedCoherentFiberComparison, Category.assoc, ← h] using e

end SerrePositivity.InfinityCategories.HomotopyLimits
