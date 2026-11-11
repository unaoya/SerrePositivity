module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.NativeCosliceRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentationEdgeFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CosliceIdentityRetraction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Fiber

/-!
概要：元の coslice 表現が指定余錐を余極限へ写すなら、元の頂点は一つの元の項の retract。
方針：元の恒等点への実辺を全空間で回収し、同じ辺を元の宇宙へ戻して分裂三角形を読む。
規約：元の余錐頂点・元の図式の項・元の coslice の恒等点を保持する。
使われ方：compact 対象の任意の小さい filtered 生成表示から retract を回収する。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の指定全余錐像の余極限性から、同じ頂点の一つの元の項への retract を構成する。 -/
lemma nativeCosliceCocone_retract {I C : SSet.{u}} [Quasicategory C]
    (D : I ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.nativeCosliceRepresentation c.vertex).diagram
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u, u + 1} c))) :
    ∃ i : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf c.vertex (D.app (Opposite.op ⦋0⦌) i) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex)
  let t := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, u + 1} p c.vertex).hom.app (Opposite.op ⦋0⦌)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.cosliceIdentityFiberPoint c.vertex))
  obtain ⟨i, w, k, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.representationCocone_edge_factorization
    ((SSet.uliftFunctor.{u + 1, u}).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.nativeCosliceRepresentation c.vertex)
    ((SSet.uliftFunctor.{u + 1, u}).map D) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c) hc t
  let w₀ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, u + 1} p (D.app (Opposite.op ⦋0⦌) i.down)).inv.app
    (Opposite.op ⦋0⦌) w).down
  let k₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm c.vertex)).Edge w₀.val
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone c.vertex) :=
    ⟨k.edge.down, congrArg ULift.down k.src_eq, congrArg ULift.down k.tgt_eq⟩
  exact ⟨i.down, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.cosliceIdentityEdge_retract w₀ k₀⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
