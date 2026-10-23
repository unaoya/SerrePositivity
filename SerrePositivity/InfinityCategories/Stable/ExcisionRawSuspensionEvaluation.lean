module
public import SerrePositivity.InfinityCategories.Stable.ExcisionRawSuspensionSquare
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSuspensionFamily
public import SerrePositivity.InfinityCategories.F2.Compact.FlipEvaluation

/-!
概要：同じ実比較辺を元の θ と照合し、対角の可逆性から入力面の普遍性へ戻す。
方針：全錐の写像と射影辺を保つ等号輸送、錐の圏の終性、右 fibration の反映を使う。
規約：一般安定性は仮定しない。使われ方：HA 1.4.2.15 の二条件からの切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionRawSuspensionSquare_evaluate {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X) (i j : Fin 2) :
    excisionRawSuspensionSquare F ≫ evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
        excisionGridSuspensionAt i j ≫ F := by
  apply functorVertex_injective
  rw [excisionRawSuspensionSquare, F2.Compact.flipFamily_evaluate_vertex]
  exact excisionGridSuspensionFamily_vertex F i j

lemma excisionRawSuspensionSquare_sourceConeAt_val {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X) (i j : Fin 2) :
    (mapJoinCone (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i,
      stdSimplex.obj₀Equiv.symm j)) (pullbackCone (excisionRawSuspensionSquare F))).val =
        (pullbackCone (excisionGridSuspensionAt i j ≫ F)).val := by
  change (cospanConeSquareIso.hom ≫ excisionRawSuspensionSquare F) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
      cospanConeSquareIso.hom ≫ (excisionGridSuspensionAt i j ≫ F)
  rw [Category.assoc, excisionRawSuspensionSquare_evaluate]

end SerrePositivity.InfinityCategories
