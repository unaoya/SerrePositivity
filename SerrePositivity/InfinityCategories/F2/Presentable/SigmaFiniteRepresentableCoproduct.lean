module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFiniteCoproductExistence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredClosure

/-!
概要：P_Σ 内の表現可能対象の有限余積は同じ底の表現可能対象と同型。
方針：底の有限余積の Yoneda 像と元の指定余錐を比較する。
規約：元の全余錐と空添字を保持する。
使われ方：小余積の有限部分集合上の各段が Ind に属することの証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：表現可能の指定有限余積の頂点は表現可能と同型。
方針：底の有限余積を選び、その像との余極限の一意性を使う。
規約：元の有限図式の全高次の作用を保持する。
使われ方：filtered 表示の各有限段の表現可能性。 -/
lemma sigmaYoneda_finiteCoproduct_representable {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {I : Type u} [Finite I] (p : nerve (Discrete I) ⟶ C)
    (c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C))
    (hc : IsColimitCone c) :
    ∃ x : C _⦋0⦌, Nonempty (VertexIso c.vertex
      ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x))) := by
  obtain ⟨d, hd⟩ := hasFiniteCoproducts_of_op_finiteProducts hC p
  let d' := mapJoinCocone (sigmaYonedaInfinityMap C) (JoinCocone.ulift.{u, u + 1} d)
  have hd' : IsColimitCone d' := sigmaYoneda_finiteCoproduct_isColimit d hd
  have hv : d'.vertex =
      (sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up d.vertex) := by
    rw [Ind.mapJoinCocone_vertex, JoinCocone.ulift_vertex]
  exact ⟨d.vertex, ⟨VertexIso.map (colimitConeIso c d' hc hd') (sliceUnderProjection _) ≪≫
    eqToIso (congrArg HomotopyCategory.mk hv)⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
