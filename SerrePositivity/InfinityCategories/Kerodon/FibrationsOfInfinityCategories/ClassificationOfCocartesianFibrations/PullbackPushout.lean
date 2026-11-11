module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverPullbackColimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackDomainMarks
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：底上の pushout を全空間へ引き戻し、その元の cocartesian 辺を両部分で覆う。
方針：pullback の余極限保存と、一次単体の pushout の全射性を使う。
規約：可変の底に quasicategory 性は不要。
使われ方：元の cocartesian Hom の pushout による貼り合わせ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 底上の pushout を固定全空間へ引き戻した図式も、同じ誘導射の pushout。 -/
lemma overPullbackUnderlying_isPushout {E B : SSet.{u}} (p : E ⟶ B)
    {a b c d : Over B} (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
    (hp : IsPushout f.left g.left i.left j.left) :
    IsPushout ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map f) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map g)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map i) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map j) := by
  have h : IsPushout f g i j := hp.of_map_of_faithful (Over.forget B)
  exact h.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p)

/-- 両部分の引き戻しの指定辺は、pushout 上の同じ元の cocartesian 辺を全て覆う。 -/
lemma cocartesianPullback_pushout_markCover {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {a b c d : Over B}
    (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
    (hp : IsPushout f.left g.left i.left j.left)
    (e : (pullback d.hom p) _⦋1⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst d.hom p) e) :
    (∃ v : (pullback b.hom p) _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst b.hom p) v ∧
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map i).app (Opposite.op ⦋1⦌) v = e) ∨
    (∃ w : (pullback c.hom p) _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst c.hom p) w ∧
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map j).app (Opposite.op ⦋1⦌) w = e) := by
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋1⦌)
  have h := (overPullbackUnderlying_isPushout p f g i j hp).map ev
  have he' := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_overPullback_iff p d e).mp he
  rcases Types.eq_or_eq_of_isPushout h e with ⟨v, hv⟩ | ⟨w, hw⟩
  · refine Or.inl ⟨v, ?_, hv⟩
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_overPullback_iff p b v).mpr
    have hs := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) v)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_snd p i)
    change (pullback.snd d.hom p).app (Opposite.op ⦋1⦌)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map i).app (Opposite.op ⦋1⦌) v) = _ at hs
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map i).app (Opposite.op ⦋1⦌) v = e at hv
    rw [hv] at hs
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p) hs).mp he'
  · refine Or.inr ⟨w, ?_, hw⟩
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_overPullback_iff p c w).mpr
    have hs := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) w)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_snd p j)
    change (pullback.snd d.hom p).app (Opposite.op ⦋1⦌)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map j).app (Opposite.op ⦋1⦌) w) = _ at hs
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map j).app (Opposite.op ⦋1⦌) w = e at hw
    rw [hw] at hs
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p) hs).mp he'

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
