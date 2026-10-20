module

public import SerrePositivity.InfinityCategories.F1.PointedRightFiberVertices
public import SerrePositivity.InfinityCategories.F1.CoherentKanPointComposition
public import SerrePositivity.InfinityCategories.F1.DiagonalFiberTransportSourceIso

/-!
概要：右 Hom の全パラメーター上で、元の点評価と pointed 輸送を比較する。
方針：一点係数の回収と、同じ右 Hom の合成四角形の輸送則を合成する。
規約：零単体だけの比較に弱めず、全 Hom 上の関手同型を保持する。
使われ方：元の相対 coherent recovery の同値性の証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 一点係数の右区間輸送は、全パラメーター上で指定された pointed 点に定値な族と同型。 -/
def pointedRightNativeCoefficientIso (K : KanObject.{u}) {P : SSet.{u + 1}}
    (s : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌) :
    FunctorIso
      (diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
        ((SSet.const (ULift.up (functorVertex
          (SSet.yonedaEquiv.symm (pointedSpaceFiberVertexEquiv K s)))) :
            P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
              (SimplicialCategory.sHom pointKanObject K)) ≫
          coherentKanRightHomInterval pointKanObject K))
      (SSet.const s) := by
  have h := pointedRightFiberComparison_interval_vertex K s
  change (coherentKanRightHomInterval pointKanObject K).app (Opposite.op ⦋0⦌)
    (ULift.up ((pointFunctorEvaluationIso K.obj).inv.app _
      (pointedSpaceFiberVertexEquiv K s))) = _ at h
  rw [pointFunctorEvaluationIso_inv_vertex] at h
  have e := (pointedRightIntervalEvaluate_cosliceIso (spaceInfinityVertex K)).precomp
    (SSet.const s : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K))
  change FunctorIso
    (SSet.const s ≫ cosliceFiberToIntervalMappingSpace pointSpaceVertex (spaceInfinityVertex K) ≫
      pointedRightIntervalEvaluate (spaceInfinityVertex K)) (SSet.const s) at e
  have hc : (SSet.const (ULift.up (functorVertex
      (SSet.yonedaEquiv.symm (pointedSpaceFiberVertexEquiv K s)))) :
        P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
          (SimplicialCategory.sHom pointKanObject K)) ≫
      coherentKanRightHomInterval pointKanObject K =
      SSet.const s ≫ cosliceFiberToIntervalMappingSpace pointSpaceVertex
        (spaceInfinityVertex K) := by
    rw [SSet.const_comp, SSet.const_comp]
    exact congrArg (fun z => (SSet.const z : P ⟶
      intervalMappingSpace (spaceInfinityVertex pointKanObject) (spaceInfinityVertex K))) h
  have he : (SSet.const s : P ⟶ _) ≫
      cosliceFiberToIntervalMappingSpace pointSpaceVertex (spaceInfinityVertex K) ≫
      pointedRightIntervalEvaluate (spaceInfinityVertex K) =
      diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
        (SSet.const s ≫ cosliceFiberToIntervalMappingSpace pointSpaceVertex
          (spaceInfinityVertex K)) := by
    simp only [pointedRightIntervalEvaluate, diagonalFiberTransport, ← Category.assoc,
      comp_lift, SSet.comp_const, Category.comp_id]
  rw [he] at e
  rw [hc]
  exact e

/-- 元の Kan Hom 全体上で、右 Hom 輸送は元の点評価と同じ fiber 比較を通して同型。 -/
def pointedRightNativeEvaluationIso (K L : KanObject.{u})
    (s : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌) :
    FunctorIso
      (diagonalFiberTransport pointedSpaceProjection (SSet.const s)
        (coherentKanRightHomInterval K L))
      ((SSet.uliftFunctor.{u + 1, u}).map
        (evaluateFunctorAt (pointedSpaceFiberVertexEquiv K s)) ≫
        pointedRightFiberComparison L) := by
  let x : (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K) :=
    SSet.const (ULift.up (functorVertex
      (SSet.yonedaEquiv.symm (pointedSpaceFiberVertexEquiv K s))))
  have e := coherentKanRightCompositionTransport_diagonalIso pointKanObject K L
    pointedSpaceIdentityPoint x (𝟙 _)
  have hc := coherentKanPointComposition_evaluate K L (pointedSpaceFiberVertexEquiv K s)
  change lift x (𝟙 _) ≫ coherentHomComposition pointKanObject K L = _ at hc
  have hp : lift x (𝟙 _) ≫ coherentHomComposition pointKanObject K L ≫
      coherentKanRightHomInterval pointKanObject L =
      (SSet.uliftFunctor.{u + 1, u}).map
        (evaluateFunctorAt (pointedSpaceFiberVertexEquiv K s) ≫
          (pointFunctorEvaluationIso L.obj).inv) ≫
        coherentKanRightHomInterval pointKanObject L := by
    rw [← Category.assoc, hc]
  rw [Category.id_comp, hp] at e
  have e₀ := diagonalFiberTransport_sourceIso pointedSpaceProjection
    (pointedRightNativeCoefficientIso K (P :=
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)) s)
    (coherentKanRightHomInterval K L)
  have h : (SSet.uliftFunctor.{u + 1, u}).map
      (evaluateFunctorAt (pointedSpaceFiberVertexEquiv K s)) ≫ pointedRightFiberComparison L =
      diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
        ((SSet.uliftFunctor.{u + 1, u}).map
          (evaluateFunctorAt (pointedSpaceFiberVertexEquiv K s) ≫
            (pointFunctorEvaluationIso L.obj).inv) ≫
          coherentKanRightHomInterval pointKanObject L) := by
    change _ ≫ ((_ ≫ coherentKanRightHomInterval pointKanObject L) ≫
      pointedRightIntervalEvaluate (spaceInfinityVertex L)) = _
    simp only [pointedRightIntervalEvaluate, diagonalFiberTransport, ← Category.assoc,
      comp_lift, SSet.comp_const, Functor.map_comp]
    rfl
  rw [h]
  exact e₀.symm ≪≫ e

end SerrePositivity.InfinityCategories
