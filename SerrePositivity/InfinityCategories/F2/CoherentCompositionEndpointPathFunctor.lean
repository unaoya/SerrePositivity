module

public import SerrePositivity.InfinityCategories.F2.CoherentCompositionEndpointPaths
public import SerrePositivity.InfinityCategories.F2.CoherentTrianglePathMinimum

/-!
概要：実終点円柱の長辺の全 path 作用を、反転最小点から元の精密化へ因子化する。
方針：長辺 path の二種類を分類し、関手の対象の一致から全射の一致を得る。
規約：元の実 path と指定精密化を保持する。
使われ方：標準の反転 Hom 比較と実 coslice 終点辺の全次数での照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の指定精密化を ULift された二点順序圏上の関手として表す。 -/
def coherentTriangleRefinementFunctor :
    ULift.{u} (Fin 2) ⥤ Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
    ComposableArrows.mk₁ coherentTriangleRefinement

/-- 実終点円柱の長辺の全 path 作用は、同じ指定精密化の反転最小点による作用。 -/
lemma coherentCompositionEndpoint_path_functor :
    coherentPrefixPathDeformationFunctor coherentCompositionEndpointObjects
      coherentCompositionEndpointTime (ULift.up 0) (ULift.up 2) ⋙
        coherentPathDeformationFunctor coherentCompositionTetrahedronObjects
          coherentCompositionTetrahedronTime _ _ =
      pathFirstMinimumReverseFunctor (1 : Fin 2) ⋙ coherentTriangleRefinementFunctor.{u} := by
  apply CategoryTheory.Functor.ext (fun P ↦ ?_)
  rcases coherentTrianglePath02_cases P with rfl | rfl
  · change _ = (coherentTriangleRefinementFunctor.obj
      ((pathFirstMinimumReverseFunctor (1 : Fin 2)).obj coherentTrianglePath02))
    rw [coherentTrianglePath02_reverseMinimum]
    exact coherentCompositionEndpoint_path_source
  · change _ = (coherentTriangleRefinementFunctor.obj
      ((pathFirstMinimumReverseFunctor (1 : Fin 2)).obj coherentTriangleCompositePath))
    rw [coherentTriangleCompositePath_reverseMinimum]
    exact coherentCompositionEndpoint_path_target

end SerrePositivity.InfinityCategories.F2
