module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAssociatorRightPair

/-!
概要：余錐全体の下の余錐を、元の余錐圏での実際の比較辺として表示する。
方針：二重 coslice の同型を零単体で評価し、元の図式への制限と頂点射影を計算する。
規約：余極限性や quasicategory 性は不要。全体の比較余錐を元の辺に厳密に戻す。
使われ方：部分余極限の比較と、始対象を持つ left fibration の Hom 表示の照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)

/-- 二重 coslice の同型は、任意のパラメータからの比較同値そのものを与える。 -/
lemma nestedCosliceIso_hom_comp {T : SSet.{u}} (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder c.val) :
    f ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceIso c).hom = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceHomEquiv c T f := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceIso, Category.comp_id] using
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceHomEquiv_naturality c f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder c.val))).symm

/-- 錐全体の下の余錐の、元の図式上の終点となる余錐。 -/
def coconeComparisonTarget (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone c.val) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCosliceRestriction c).app (Opposite.op ⦋0⦌) d

/-- 錐全体の下の余錐は、元の余錐圏における c からその制限への実際の辺になる。 -/
def coconeComparisonEdge (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone c.val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).Edge c (coconeComparisonTarget c d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberVertexToEdge
    ⟨(_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceIso c).hom.app (Opposite.op ⦋0⦌) d,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩

/-- 比較辺の終点は、元の部分図式へ制限した同じ余錐である。 -/
lemma coconeComparisonTarget_eq (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone c.val) :
    coconeComparisonTarget c d =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq c.property (d.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0])) := by
  apply Subtype.ext
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCosliceRestriction_uncurry c (SSet.yonedaEquiv.symm d)
  rw [SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_val]
  exact h

/-- 比較辺の終点の余錐は、元の比較余錐と同じ頂点を持つ。 -/
lemma coconeComparisonTarget_vertex (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone c.val) :
    (coconeComparisonTarget c d).vertex = d.vertex := by
  rw [coconeComparisonTarget_eq, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict]

/-- 比較辺を頂点へ射影すると、錐の頂点から出る元の比較余錐の脚になる。 -/
lemma coconeComparisonEdge_projection (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone c.val) :
    ((coconeComparisonEdge c d).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)).edge =
      (d.leg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0])).edge := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceHomEquiv_doubleUncurry c (SSet.yonedaEquiv.symm d)
  rw [← nestedCosliceIso_hom_comp, SSet.yonedaEquiv_symm_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda] at hn
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceIso c).hom.app (Opposite.op ⦋0⦌) d).val)) = _
  rw [← SSet.yonedaEquiv_comp, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, hn,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] Δ[0])) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinAssociator K Δ[0] Δ[0]).inv,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinAssociator_rightPair_inv]
  rfl

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
