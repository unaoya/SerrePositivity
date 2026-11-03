module
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeReindexRestrictions

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentFunctorProductLimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyProductCone

/-!
概要：任意の元の非空有限関手族に、元の反復積関手と全射影を持つ native 積錐を与える。
方針：同じ有限添字表示で元の関手圏の極限錐を再添字し、元の図式を厳密に回収する。
規約：元の関手・全錐・頂点・各射影辺を保持する。
使われ方：元の評価極限錐の族と、sifted 積比較の積関手の coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} {J : Type u}
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))

/-- 元の一般添字の関手族を、元の関手 ∞ 圏内の同じ離散図式にする。 -/
def finiteFamilyFunctorDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} :=
  liftedDiscreteVertexMap (fun j ↦ functorVertex (G j))

/-- 元の関手図式の各頂点は元の関手そのもの。 -/
lemma finiteFamilyFunctorDiagram_vertex (j : J) :
    (finiteFamilyFunctorDiagram G).app (Opposite.op ⦋0⦌)
      (ULift.up (nerveVertex (Discrete.mk j))) = functorVertex (G j) :=
  liftedDiscreteVertexMap_vertex _ _

/-- 元の関手図式は、同じ有限表示を再添字して厳密に回収される。 -/
lemma finiteFamilyFunctorDiagram_reindex_eq (n : ℕ) (e : J ≃ ULift.{u} (Fin (n + 1))) :
    (liftedDiscreteIndexIso e).hom ≫
      finiteCoherentFunctorDiagram n (fun i ↦ G (e.symm (ULift.up i))) =
        finiteFamilyFunctorDiagram G := by
  apply liftedDiscreteDiagram_ext
  intro j
  change (finiteCoherentFunctorDiagram n (fun i ↦ G (e.symm (ULift.up i)))).app _
    ((liftedDiscreteIndexIso e).hom.app _ (ULift.up (nerveVertex j))) = _
  rw [liftedDiscreteIndexIso_vertex, finiteCoherentFunctorDiagram_vertex,
    finiteFamilyFunctorDiagram_vertex, ULift.up_down, e.symm_apply_apply]

/-- 元の任意の非空有限関手族の反復積関手を頂点とする native 全錐。 -/
def finiteFamilyFunctorProductCone [Finite J] [Nonempty J] :
    JoinCone (finiteFamilyFunctorDiagram G) :=
  let P := nonemptyFiniteIndexPresentation J
  ((finiteCoherentFunctorCone P.1 (fun i ↦ G (P.2.symm (ULift.up i))))).reindexIso
    (liftedDiscreteIndexIso P.2) |>.cast (finiteFamilyFunctorDiagram_reindex_eq G P.1 P.2)

/-- 元の一般非空有限関手族の全錐は、元の関手 ∞ 圏の積錐。 -/
lemma finiteFamilyFunctorProductCone_isLimit [Finite J] [Nonempty J] :
    IsLimitCone (finiteFamilyFunctorProductCone G) := by
  let P := nonemptyFiniteIndexPresentation J
  exact ((isLimitCone_iff_reindexIso _ _).mp
    (finiteCoherentFunctorCone_isLimit P.1 (fun i ↦ G (P.2.symm (ULift.up i))))).cast
      (finiteFamilyFunctorDiagram_reindex_eq G P.1 P.2)

/-- 元の全錐の頂点は、同じ有限表示による元の反復積関手そのもの。 -/
lemma finiteFamilyFunctorProductCone_vertex [Finite J] [Nonempty J] :
    (finiteFamilyFunctorProductCone G).vertex = functorVertex (finiteFamilyCoherentProduct G) := by
  rw [finiteFamilyFunctorProductCone, JoinCone.vertex_cast, joinCone_reindexIso_vertex,
    finiteCoherentFunctorCone_vertex]
  rfl

/-- 元の一般有限全錐の各脚も、同じ元の反復射影変換の全一単体を保持する。 -/
lemma finiteFamilyFunctorProductCone_leg_edge [Finite J] [Nonempty J] (j : J) :
    (F2.nativeConeLeg (finiteFamilyFunctorProductCone G)
      (ULift.up (nerveVertex (Discrete.mk j)))).edge =
        let P := nonemptyFiniteIndexPresentation J
        (intervalMappingEdgeOfVertex (finiteCoherentProjectionVertex P.1
          (fun i ↦ G (P.2.symm (ULift.up i))) (P.2 j).down)).edge := by
  change (F2.nativeConeLeg ((finiteCoherentFunctorCone _ _).reindexIso
    (liftedDiscreteIndexIso (nonemptyFiniteIndexPresentation J).2)) _).edge = _
  rw [nativeConeLeg_reindexIso_edge, liftedDiscreteIndexIso_vertex,
    finiteCoherentFunctorCone_leg_edge]

end SerrePositivity.InfinityCategories.HomotopyLimits
