module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackDomainCocone
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：底を覆う余極限の引き戻しで、元の全 cocartesian 辺を回収する。
方針：底の辺を一つの項から選び、元の全空間の辺と pullback で組み合わせる。
規約：元の辺そのものを第一・第二射影で厳密に保持する。
使われ方：cocartesian Hom の降下に必要な指定辺の被覆条件の供給。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 底を覆う各引き戻しの cocartesian 辺は、元の全空間の cocartesian 辺を全て覆う。 -/
lemma exists_cocartesianPullbackEdge_of_base_colimit
    {J : Type v} [Category.{w} J] [Small.{u} J] {E B : SSet.{u}}
    (p : E ⟶ B) (D : J ⥤ Over B) (hc : IsColimit ((Over.forgetCocone B).whisker D))
    (e : E _⦋1⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e) :
    ∃ j, ∃ t : (pullback (D.obj j).hom p) _⦋1⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst (D.obj j).hom p) t ∧
        (pullback.snd (D.obj j).hom p).app (Opposite.op ⦋1⦌) t = e := by
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋1⦌)
  obtain ⟨j, b, hb⟩ := Types.jointly_surjective _ (isColimitOfPreserves ev hc)
    (p.app (Opposite.op ⦋1⦌) e)
  change (D.obj j).hom.app (Opposite.op ⦋1⦌) b = p.app (Opposite.op ⦋1⦌) e at hb
  have hbg : SSet.yonedaEquiv.symm b ≫ (D.obj j).hom = SSet.yonedaEquiv.symm e ≫ p := by
    exact (SSet.yonedaEquiv_symm_comp b (D.obj j).hom).trans
      ((congrArg (SSet.yonedaEquiv (X := B) (n := ⦋1⦌)).symm hb).trans
        (SSet.yonedaEquiv_symm_comp e p).symm)
  let l := pullback.lift (SSet.yonedaEquiv.symm b) (SSet.yonedaEquiv.symm e) hbg
  let t := SSet.yonedaEquiv l
  have ht : (pullback.snd (D.obj j).hom p).app (Opposite.op ⦋1⦌) t = e := by
    rw [← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]
  refine ⟨j, t, ?_, ht⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_isPullback (IsPullback.of_hasPullback (D.obj j).hom p).flip
  rw [ht]
  exact he

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
