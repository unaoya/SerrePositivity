module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteProductIndexTransport

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteFamilyColimitNativeCone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaPresheafFamilyComparison

/-!
概要：元の P_Σ 評価全脚の Kan 像を持つ余極限全錐を、元の一般有限添字で回収する。
方針：同じ有限表示の形状同型で元の全錐を戻し、元の全図式と全脚を保持する。
規約：元の族・有限極限錐・余極限頂点を保持。非空有限添字を扱う。
使われ方：P_Σ の sifted 閉性で、元の有限錐の像の全脚と極限性を供給する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G))
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hA : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A)

/-- 元の一般有限添字の全評価脚の Kan 像を持つ、元の余極限頂点からの全錐。 -/
def finiteFamilyOriginalColimitFamilyCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
    (Discrete.functor (fun j ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (G j)))) :=
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteFamilyOriginalColimitNativeCone G c A hA).reindexIso
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteIndexIso Q.2)).cast
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductDiagram_eq Q.1 (fun k ↦ G (Q.2.symm (ULift.up k))) Q.2).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductDiagram_original Q.1 Q.2 G))

/-- 元の一般有限全錐の頂点は、元の評価錐頂点の余極限 Kan 模型そのもの。 -/
lemma finiteFamilyOriginalColimitFamilyCone_vertex :
    (finiteFamilyOriginalColimitFamilyCone G c A hA).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject A) := by
  rw [finiteFamilyOriginalColimitFamilyCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCone_reindexIso_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteFamilyOriginalColimitNativeCone_vertex]

/-- 再添字しても、元の各評価脚の Kan 像の native な全一単体を保持する。 -/
lemma finiteFamilyOriginalColimitFamilyCone_leg_edge (j : Discrete J) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (finiteFamilyOriginalColimitFamilyCone G c A hA)
      (ULift.up (ComposableArrows.mk₀ j))).edge =
      let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteFamilyOriginalColimitNativeCone G c A hA)
        (ULift.up (ComposableArrows.mk₀ (Discrete.mk (Q.2 j.as))))).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteFamilyOriginalColimitNativeCone G c A hA).reindexIso
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteIndexIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J).2)) _).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeConeLeg_reindexIso_edge]
  rfl

/-- sifted な底上で、元の全評価脚を持つ元の一般有限全錐は極限錐。 -/
lemma finiteFamilyOriginalColimitFamilyCone_isLimit [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (finiteFamilyOriginalColimitFamilyCone G c A hA) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  exact ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_reindexIso _ _).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteFamilyOriginalColimitNativeCone_isLimit G c A hA hc)).cast
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductDiagram_eq Q.1 (fun k ↦ G (Q.2.symm (ULift.up k))) Q.2).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reindexedFiniteProductDiagram_original Q.1 Q.2 G))

variable {C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
  {p : nerve (Discrete J) ⟶ C.op} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)

/-- 元の P_Σ の族と元の有限極限錐から得る、元の評価全脚の余極限全錐。 -/
def sigmaPresheafColimitFiniteCone :=
  finiteFamilyOriginalColimitFamilyCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFiniteEvaluationFamily r (p := p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFamilyComparisonCone r d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} d).vertex)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFamilyComparisonCone_vertex r d)

/-- 元の P_Σ 条件が供給した同じ全評価脚の余極限全錐は、sifted な底で有限積錐。 -/
lemma sigmaPresheafColimitFiniteCone_isLimit [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (sigmaPresheafColimitFiniteCone r d) :=
  finiteFamilyOriginalColimitFamilyCone_isLimit _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFamilyComparisonCone_isLimit r d hd)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
