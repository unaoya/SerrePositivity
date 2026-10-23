module
public import SerrePositivity.InfinityCategories.Stable.FunctorPullbackComparisonConeAt
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreComparisonArrowReadback
public import SerrePositivity.InfinityCategories.Stable.ExcisionReplacedSourceCone

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

lemma excisionRawSuspensionComparison_source_theta {X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] (F : nerve ExcisionGridIndex.{u} ⟶ X)
    (i : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫
      (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)) 2 2)))
    (hi : IsLimitCone i)
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (hr : (F2.restrictJoinCone c (nerveMap excisionCorePuncturedToFull.toFunctor)).val =
      (excisionCorePuncturedLimitCone
        (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)
        i hi).val)
    (d : JoinCone (pullbackCospan (excisionRawSuspensionSquare (excisionReplaceInitial c))))
    (hd : IsLimitCone d) :
    ∃ (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫
        (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)) 1 1)))
      (he : IsLimitCone e),
      Arrow.mk (Truncated.HomotopyCategory.homMk
        ((functorPullbackComparisonEdge
          (excisionRawSuspensionSquare (excisionReplaceInitial c)) d hd).map
            ((truncation 2).map (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2),
              stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (excisionCoreComparisonEdge
        (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)
        i hi e he)) := by
  let G := nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F
  let Q := excisionRawSuspensionSquare (excisionReplaceInitial c)
  let k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)
  let a := mapJoinCone (evaluateFunctorAt k) (pullbackCone Q)
  let b := mapJoinCone (evaluateFunctorAt k) d
  let n := excisionCorePuncturedOuterCone (excisionCorePuncturedLimitCone G i hi)
  have ha : a.val = n.val :=
    excisionRawSuspensionSquare_replaced_sourceConeAt_core_val F c _ hr
  have hp : pullbackCospan Q ≫ evaluateFunctorAt k =
      pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ G) 1 1) :=
    a.property.symm.trans
      ((congrArg (fun v ↦ joinInr (Δ[0] : SSet.{u}) (horn 2 2) ≫ v) ha).trans n.property)
  let e := b.cast hp
  have he : IsLimitCone e :=
    (F2.isLimitCone_iff_of_cone_val_eq b e rfl).mp
      (functorPullbackComparison_target_pointwise Q d hd k)
  refine ⟨e, he, ?_⟩
  have h := excisionCoreComparisonEdge_arrowMk_of_coneEdge G i hi e he
    (functorPullbackComparisonConeAt Q d hd k) ha rfl
  have hs := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
    (functorPullbackComparisonConeAt_projected_edge Q d hd k).symm
  exact hs.trans h

end SerrePositivity.InfinityCategories
