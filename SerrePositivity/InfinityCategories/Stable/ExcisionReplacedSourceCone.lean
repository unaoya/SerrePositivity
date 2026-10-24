module
public import SerrePositivity.InfinityCategories.Stable.ExcisionRawSuspensionEvaluation
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullCoreConeChoice

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

lemma excisionRawSuspensionSquare_replaced_sourceConeAt_core_val {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X)
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (d : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫
      (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)))
    (hr : (restrictJoinCone c (nerveMap excisionCorePuncturedToFull.toFunctor)).val =
      d.val) :
    (mapJoinCone (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2),
      stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (pullbackCone (excisionRawSuspensionSquare (excisionReplaceInitial c)))).val =
        (excisionCorePuncturedOuterCone d).val := by
  rw [excisionRawSuspensionSquare_sourceConeAt_val]
  exact excisionReplaceInitial_coreOuterCone_val F c d hr

end SerrePositivity.InfinityCategories
