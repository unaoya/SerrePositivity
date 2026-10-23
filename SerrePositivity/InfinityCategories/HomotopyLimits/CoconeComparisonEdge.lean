module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberVertices
public import SerrePositivity.InfinityCategories.Stable.JoinAssociatorRightPair

/-!
概要：余錐全体の下の余錐を、元の余錐圏での実際の比較辺として表示する。
方針：二重 coslice の同型を零単体で評価し、元の図式への制限と頂点射影を計算する。
規約：余極限性や quasicategory 性は不要。全体の比較余錐を元の辺に厳密に戻す。
使われ方：部分余極限の比較と、始対象を持つ left fibration の Hom 表示の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p)

/-- 二重 coslice の同型は、任意のパラメータからの比較同値そのものを与える。 -/
lemma nestedCosliceIso_hom_comp {T : SSet.{u}} (f : T ⟶ sliceUnder c.val) :
    f ≫ (nestedCosliceIso c).hom = nestedCosliceHomEquiv c T f := by
  simpa only [nestedCosliceIso, Category.comp_id] using
    (nestedCosliceHomEquiv_naturality c f (𝟙 (sliceUnder c.val))).symm

/-- 錐全体の下の余錐の、元の図式上の終点となる余錐。 -/
def coconeComparisonTarget (d : JoinCocone c.val) : JoinCocone p :=
  (colimitCosliceRestriction c).app (Opposite.op ⦋0⦌) d

/-- 錐全体の下の余錐は、元の余錐圏における c からその制限への実際の辺になる。 -/
def coconeComparisonEdge (d : JoinCocone c.val) :
    (sliceUnder p).Edge c (coconeComparisonTarget c d) :=
  cosliceFiberVertexToEdge
    ⟨(nestedCosliceIso c).hom.app (Opposite.op ⦋0⦌) d,
      (pinchedConstant_zero _).symm⟩

/-- 比較辺の終点は、元の部分図式へ制限した同じ余錐である。 -/
lemma coconeComparisonTarget_eq (d : JoinCocone c.val) :
    coconeComparisonTarget c d =
      coherentCoconeOfDiagramEq c.property (d.restrict (joinInl K Δ[0])) := by
  apply Subtype.ext
  have h := colimitCosliceRestriction_uncurry c (SSet.yonedaEquiv.symm d)
  rw [SSet.yonedaEquiv_symm_comp, sliceUnderUncurry_yoneda,
    sliceUnderUncurry_yoneda] at h
  rw [coherentCoconeOfDiagramEq_val]
  exact h

/-- 比較辺の終点の余錐は、元の比較余錐と同じ頂点を持つ。 -/
lemma coconeComparisonTarget_vertex (d : JoinCocone c.val) :
    (coconeComparisonTarget c d).vertex = d.vertex := by
  rw [coconeComparisonTarget_eq, coherentCoconeOfDiagramEq_vertex,
    JoinCocone.vertex_restrict]

/-- 比較辺を頂点へ射影すると、錐の頂点から出る元の比較余錐の脚になる。 -/
lemma coconeComparisonEdge_projection (d : JoinCocone c.val) :
    ((coconeComparisonEdge c d).map (sliceUnderProjection p)).edge =
      (d.leg (joinInr K Δ[0])).edge := by
  have hn := nestedCosliceHomEquiv_doubleUncurry c (SSet.yonedaEquiv.symm d)
  rw [← nestedCosliceIso_hom_comp, SSet.yonedaEquiv_symm_comp,
    sliceUnderUncurry_yoneda, sliceUnderUncurry_yoneda] at hn
  change (sliceUnderProjection p).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      ((nestedCosliceIso c).hom.app (Opposite.op ⦋0⦌) d).val)) = _
  rw [← SSet.yonedaEquiv_comp, Category.assoc, ← sliceUnderUncurry_projection, hn,
    ← Category.assoc (joinInr K (join Δ[0] Δ[0])) (stableJoinAssociator K Δ[0] Δ[0]).inv,
    stableJoinAssociator_rightPair_inv]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
