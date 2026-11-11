module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CarrierConeVertices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrierBound

/-!
概要：元の実現図式と同じ指定頂点への余錐は、全鎖の実現条件を満たす。
方針：元の単体では元の条件を使い、新しい単体では最後の添字と共通部分複体を使う。
規約：値・添字・指定頂点の元の等式を全て保持する。
使われ方：有限 coslice 余錐の二成分を実現空間内へ貼り合わせる。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {X K : SSet.{u}}
  (A : I → X.Subcomplex) (z : I → X _⦋0⦌)
  (a : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).toSSet)
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⟶ X) (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⟶ nerve I) (i : I)
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ F = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A z)
  (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ q = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A z)
  (hbound : Subcomplex.range F ≤ A i)
  (hFapex : F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K) = z i) (hqapex : q.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)
include hF hq hbound hFapex hqapex

/-- 元の余錐の二成分は、各単体の所属と元の頂点の条件を同時に満たす。 -/
lemma terminalCarrierCone_conditions :
    (∀ (n : SimplexCategoryᵒᵖ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})).obj n),
      F.app n s ∈ (A ((q.app n s).obj (Fin.last n.unop.len))).obj n) ∧
    ∀ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋0⦌, F.app _ v = z ((q.app _ v).obj 0) := by
  constructor
  · rintro ⟨⟨n⟩⟩ s
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplex_inl_or_last_apex s with ⟨x, rfl⟩ | hs
    · have hf := congrArg (fun f : K ⟶ X => f.app _ x) hF
      have hqq := congrArg (fun f : K ⟶ nerve I => f.app _ x) hq
      change F.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]).app _ x) = (a.app _ x).val.1 at hf
      change q.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]).app _ x) = (a.app _ x).val.2 at hqq
      rw [hf, hqq]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition_mem_last (a.app _ x).property
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneMap_last_index q i hqapex s hs]
      exact hbound _ ⟨s, rfl⟩
  · intro v
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplex_inl_or_last_apex v with ⟨x, rfl⟩ | hs
    · have hf := congrArg (fun f : K ⟶ X => f.app _ x) hF
      have hqq := congrArg (fun f : K ⟶ nerve I => f.app _ x) hq
      change F.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]).app _ x) = (a.app _ x).val.1 at hf
      change q.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]).app _ x) = (a.app _ x).val.2 at hqq
      rw [hf, hqq]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier_vertex_value (a.app _ x)
    · have hv : v = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K := by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneVertex_eq_apex_iff v).mpr
        have hh := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexVertex_eq_apex_iff v (Fin.last 0)).mp hs
        change v.1.val ≤ 0 at hh
        omega
      rw [hv, hFapex, hqapex]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
