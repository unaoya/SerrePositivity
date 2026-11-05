module

public import SerrePositivity.InfinityCategories.Stable.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ExactFunctorSpanCospanPreservation
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitPreservationGeneration
public import SerrePositivity.InfinityCategories.F2.Ind.LimitPreservationShapeIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.EmptyShapeLimitCriterion
public import SerrePositivity.InfinityCategories.Stable.StableFiniteLimitsColimits
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-!
概要：安定圏間の元の完全関手は、有限形状の指定した全極限錐を保つ。
方針：零対象と引き戻しの保存を、空形状・点 cospan による有限生成へ渡す。
規約：有限極限保存を完全関手の追加入力にしない。
使われ方：実分母の有限図式の共通精密化を商側で検査する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の完全関手は、任意の有限図式の同じ全極限錐を保存する。 -/
lemma exactMap_map_isLimit_finite {B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C)
    {K : SSet.{u}} [K.Finite] {p : K ⟶ B.obj}
    (c : JoinCone p) (hc : IsLimitCone c) : IsLimitCone (mapJoinCone q.hom c) := by
  let : HasFiniteLimits B.obj := hasFiniteLimits_of_isStable B.obj
  apply F2.Ind.map_isLimit_finite_of_empty_pointCospan q.hom ?_ ?_ c hc
  · intro T p d hd
    let : IsEmpty (((⊥ : T.Subcomplex) : SSet.{u}) _⦋0⦌) :=
      ⟨fun v => v.property⟩
    have ht : IsTerminalVertex d.vertex :=
      (HomotopyLimits.isLimitCone_iff_terminal_of_emptyVertices d).mp hd
    let z := chosenZeroVertex B.obj
    have hz : IsZeroVertex d.vertex :=
      z.isZero.of_vertexIso (terminalVertexIso z.isTerminal ht)
    apply (HomotopyLimits.isLimitCone_iff_terminal_of_emptyVertices
      (mapJoinCone q.hom d)).mpr
    rw [mapJoinCone_vertex]
    exact (IsExactFunctor.preservesZero (F := q.hom) _ hz).2
  · intro p d hd
    apply F2.Ind.map_isLimit_of_shapeIso q.hom
      (hornReverseIso 2 0 ≪≫ (SSet.opFunctor.mapIso pointConeSpanIso).symm)
      (fun _ a ha => F2.exactFunctor_preserves_cospan_limit q.hom a ha) d hd

end SerrePositivity.KST.LocalizingInvariants
