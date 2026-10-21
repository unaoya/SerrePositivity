module

public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteConeArrowFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.ArrowVertexEndpoints
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoconeImageLegs

/-!
概要：矢印関手圏にまとめた同じ全錐の両端評価を、元の二つの全錐へ厳密に戻す。
方針：元の頂点辺と全脚の評価を使い、離散全錐の外延性で全錐を回収する。
規約：元の全図式と全脚を保持する。有限性は不要。
使われ方：元の全錐の間の可逆円柱と極限性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {J : Type u} {X : SSet.{u + 1}} [Quasicategory X]
  {p q : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X}
  (c : JoinCone p) (d : JoinCone q) (e : SSet.Edge c.vertex d.vertex)
  (f : (j : J) → SSet.Edge
    (p.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j))))
    (q.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j)))))
  (h : ∀ j, homMk e.toTruncated ≫
    homMk (F2.nativeConeLeg d (ULift.up (nerveVertex (Discrete.mk j)))) =
    homMk (F2.nativeConeLeg c (ULift.up (nerveVertex (Discrete.mk j)))) ≫
      homMk (f j).toTruncated)

omit [Quasicategory X] in
/-- 元の成分比較の矢印図式の始点評価は、元の始点図式そのもの。 -/
lemma discreteConeArrowDiagram_zero :
    discreteConeArrowDiagram f ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = p := by
  apply liftedDiscreteDiagram_ext
  intro j
  change (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _
    ((discreteConeArrowDiagram f).app _ _) = _
  rw [discreteConeArrowDiagram, liftedDiscreteVertexMap_vertex]
  exact arrowFunctorVertex_zero (f j.as)

omit [Quasicategory X] in
/-- 元の成分比較の矢印図式の終点評価は、元の終点図式そのもの。 -/
lemma discreteConeArrowDiagram_one :
    discreteConeArrowDiagram f ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = q := by
  apply liftedDiscreteDiagram_ext
  intro j
  change (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app _
    ((discreteConeArrowDiagram f).app _ _) = _
  rw [discreteConeArrowDiagram, liftedDiscreteVertexMap_vertex]
  exact arrowFunctorVertex_one (f j.as)

/-- 同じ元の矢印全錐の始点評価を、元の始点全錐そのものへ厳密に回収する。 -/
lemma discreteConeArrowCone_zero :
    (evaluateFunctorCone (discreteConeArrowCone c d e f h)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).cast (discreteConeArrowDiagram_zero f) = c := by
  apply discreteCone_ext_of_vertex_leg
  · rw [JoinCone.vertex_cast, evaluateFunctorCone_vertex, discreteConeArrowCone_vertex]
    exact arrowFunctorVertex_zero e
  · intro j
    change (F2.nativeConeLeg (mapJoinCone
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (discreteConeArrowCone c d e f h)) (ULift.up (nerveVertex (Discrete.mk j)))).edge = _
    rw [nativeConeLeg_mapJoinCone_edge]
    exact discreteConeArrowCone_leg_zero c d e f h j

/-- 同じ元の矢印全錐の終点評価を、元の終点全錐そのものへ厳密に回収する。 -/
lemma discreteConeArrowCone_one :
    (evaluateFunctorCone (discreteConeArrowCone c d e f h)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).cast (discreteConeArrowDiagram_one f) = d := by
  apply discreteCone_ext_of_vertex_leg
  · rw [JoinCone.vertex_cast, evaluateFunctorCone_vertex, discreteConeArrowCone_vertex]
    exact arrowFunctorVertex_one e
  · intro j
    change (F2.nativeConeLeg (mapJoinCone
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (discreteConeArrowCone c d e f h)) (ULift.up (nerveVertex (Discrete.mk j)))).edge = _
    rw [nativeConeLeg_mapJoinCone_edge]
    exact discreteConeArrowCone_leg_one c d e f h j

end SerrePositivity.InfinityCategories.HomotopyLimits
