module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.PartialColimitApexSpan
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictCoconeVertexLegs
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.TransportedCoconeGluing

/-!
概要：部分余極限対象の実際の span の余錐から、元の押し出し図式の余錐を構成する。
方針：二つの合成三角形を共通の脚で比較し、輸送と境界の厳密化へ渡す。
規約：元の図式の余極限性は別途必要。使われ方：coherent 図式のセル付加の頂点候補。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C : SSet.{u + 1}} {p : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (i : A ⟶ B) (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hi : i ≫ F = p) (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
  (j : A ⟶ C) (G : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hj : j ≫ G = p) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G)

/-- 部分余極限対象の span の余錐を strict 図式上で表示する。 -/
def partialColimitStrictSpanCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan c hc i F hi dB j G hj dC)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram _).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitPushoutCocone c hc i F hi dB j G hj dC)

/-- 左部分余錐の実際の頂点から、span の余極限頂点への脚。 -/
def partialColimitSpanLeftLeg :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.Edge dB.vertex (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeVertexLeg _ (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC)
    (AsSmall.up.obj WalkingSpan.left) dB.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object dB.vertex)

/-- 右部分余錐の実際の頂点から、span の余極限頂点への脚。 -/
def partialColimitSpanRightLeg :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.Edge dC.vertex (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeVertexLeg _ (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC)
    (AsSmall.up.obj WalkingSpan.right) dC.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object dC.vertex)

/-- span の二つの脚は、実際の付加比較辺との後合成がホモトピー圏で一致する。 -/
lemma partialColimitSpanLegs_composites :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc i F hi dB) ≫
        SSet.Truncated.HomotopyCategory.homMk
          (partialColimitSpanLeftLeg c hc i F hi dB j G hj dC).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc j G hj dC) ≫
        SSet.Truncated.HomotopyCategory.homMk
          (partialColimitSpanRightLeg c hc i F hi dB j G hj dC).toTruncated := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan c hc i F hi dB j G hj dC
  let t := partialColimitStrictSpanCocone c hc i F hi dB j G hj dC
  have hB := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeVertexLeg_comp H t (AsSmall.up.map WalkingSpan.Hom.fst)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object c.vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object dB.vertex)
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc i F hi dB))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexHom_edge c hc i F hi dB).symm
  have hC := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeVertexLeg_comp H t (AsSmall.up.map WalkingSpan.Hom.snd)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object c.vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object dC.vertex)
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc j G hj dC))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexHom_edge c hc j G hj dC).symm
  exact hB.trans hC.symm

/-- 押し出し形状の元の coherent 図式に、部分余極限 span の余極限を頂点とする余錐が存在。 -/
lemma exists_cocone_vertex_partialColimitPushout {A B C D : SSet.{u + 1}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, e.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitPushoutObject c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC) := by
  let eB := partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
  let eC := partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
  obtain ⟨e, _, _, _, hv, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_cocone_glue_of_apex_composites hp p c hc dB dC eB eC
    (partialColimitSpanLegs_composites c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
  refine ⟨e, hv.trans ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitPushoutCocone_vertex c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
