module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteFamilyColimitNativeCone
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaPresheafFamilyComparison

/-!
概要：元の P_Σ 評価全脚の Kan 像を持つ余極限全錐を、元の一般有限添字で回収する。
方針：同じ有限表示の形状同型で元の全錐を戻し、元の全図式と全脚を保持する。
規約：元の族・有限極限錐・余極限頂点を保持。非空有限添字を扱う。
使われ方：P_Σ の sifted 閉性で、元の有限錐の像の全脚と極限性を供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  (c : JoinCone (finiteFamilyFunctorDiagram G))
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hA : c.vertex = functorVertex A)

/-- 元の一般有限添字の全評価脚の Kan 像を持つ、元の余極限頂点からの全錐。 -/
def finiteFamilyOriginalColimitFamilyCone : JoinCone (kanDiagramCoherentNerve
    (Discrete.functor (fun j ↦ F2.coherentDiagramTotalKanObject (G j)))) :=
  let Q := nonemptyFiniteIndexPresentation J
  ((finiteFamilyOriginalColimitNativeCone G c A hA).reindexIso
    (liftedDiscreteIndexIso Q.2)).cast
      ((reindexedFiniteProductDiagram_eq Q.1 (fun k ↦ G (Q.2.symm (ULift.up k))) Q.2).trans
        (reindexedFiniteProductDiagram_original Q.1 Q.2 G))

/-- 元の一般有限全錐の頂点は、元の評価錐頂点の余極限 Kan 模型そのもの。 -/
lemma finiteFamilyOriginalColimitFamilyCone_vertex :
    (finiteFamilyOriginalColimitFamilyCone G c A hA).vertex =
      coherentNerveVertex (F2.coherentDiagramTotalKanObject A) := by
  rw [finiteFamilyOriginalColimitFamilyCone, JoinCone.vertex_cast, joinCone_reindexIso_vertex,
    finiteFamilyOriginalColimitNativeCone_vertex]

/-- 再添字しても、元の各評価脚の Kan 像の native な全一単体を保持する。 -/
lemma finiteFamilyOriginalColimitFamilyCone_leg_edge (j : Discrete J) :
    (F2.nativeConeLeg (finiteFamilyOriginalColimitFamilyCone G c A hA)
      (ULift.up (ComposableArrows.mk₀ j))).edge =
      let Q := nonemptyFiniteIndexPresentation J
      (F2.nativeConeLeg (finiteFamilyOriginalColimitNativeCone G c A hA)
        (ULift.up (ComposableArrows.mk₀ (Discrete.mk (Q.2 j.as))))).edge := by
  change (F2.nativeConeLeg ((finiteFamilyOriginalColimitNativeCone G c A hA).reindexIso
    (liftedDiscreteIndexIso (nonemptyFiniteIndexPresentation J).2)) _).edge = _
  rw [nativeConeLeg_reindexIso_edge]
  rfl

/-- sifted な底上で、元の全評価脚を持つ元の一般有限全錐は極限錐。 -/
lemma finiteFamilyOriginalColimitFamilyCone_isLimit [IsSiftedInfinity B] (hc : IsLimitCone c) :
    IsLimitCone (finiteFamilyOriginalColimitFamilyCone G c A hA) := by
  let Q := nonemptyFiniteIndexPresentation J
  exact ((isLimitCone_iff_reindexIso _ _).mp
    (finiteFamilyOriginalColimitNativeCone_isLimit G c A hA hc)).cast
      ((reindexedFiniteProductDiagram_eq Q.1 (fun k ↦ G (Q.2.symm (ULift.up k))) Q.2).trans
        (reindexedFiniteProductDiagram_original Q.1 Q.2 G))

variable {C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  {p : nerve (Discrete J) ⟶ C.op} (d : JoinCone p)

/-- 元の P_Σ の族と元の有限極限錐から得る、元の評価全脚の余極限全錐。 -/
def sigmaPresheafColimitFiniteCone :=
  finiteFamilyOriginalColimitFamilyCone (sigmaPresheafFiniteEvaluationFamily r (p := p))
    (sigmaPresheafFamilyComparisonCone r d)
    (sigmaPresheafVertexEvaluation r (JoinCone.ulift.{u, u + 1} d).vertex)
    (sigmaPresheafFamilyComparisonCone_vertex r d)

/-- 元の P_Σ 条件が供給した同じ全評価脚の余極限全錐は、sifted な底で有限積錐。 -/
lemma sigmaPresheafColimitFiniteCone_isLimit [IsSiftedInfinity B] (hd : IsLimitCone d) :
    IsLimitCone (sigmaPresheafColimitFiniteCone r d) :=
  finiteFamilyOriginalColimitFamilyCone_isLimit _ _ _ _
    (sigmaPresheafFamilyComparisonCone_isLimit r d hd)

end SerrePositivity.InfinityCategories.HomotopyLimits
