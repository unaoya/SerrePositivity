module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackDomainMarks

/-!
概要：底の全辺を覆う底変換は、元の cocartesian 辺も同じ辺として覆う。
方針：底の辺を一つ選び、元の辺と Yoneda の pullback で組み合わせる。
規約：元の cocartesian 辺を別の選択 lift に置き換えない。
使われ方：高次内ホーン上の元の Hom の指定辺保存条件の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 底の同じ辺が回収できれば、元の cocartesian 辺を同じ像を持つ辺で回収できる。 -/
lemma exists_cocartesianPullbackEdge_of_base_edge
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (a : Over B) (e : E _⦋1⦌) (he : IsCocartesianEdge p e)
    (b : a.left _⦋1⦌) (hb : a.hom.app (Opposite.op ⦋1⦌) b = p.app (Opposite.op ⦋1⦌) e) :
    ∃ d : (pullback a.hom p) _⦋1⦌,
      IsCocartesianEdge (pullback.fst a.hom p) d ∧
        (pullback.snd a.hom p).app (Opposite.op ⦋1⦌) d = e := by
  have hw : SSet.yonedaEquiv.symm b ≫ a.hom = SSet.yonedaEquiv.symm e ≫ p := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hb
  let L := pullback.lift (SSet.yonedaEquiv.symm b) (SSet.yonedaEquiv.symm e) hw
  have hL : (pullback.snd a.hom p).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv L) = e := by
    rw [← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]
  refine ⟨SSet.yonedaEquiv L, ?_, hL⟩
  apply (isCocartesianEdge_overPullback_iff p a _).mpr
  rwa [hL]

/-- 底の全辺を覆う底変換は、元の cocartesian 辺を同じ像を持つ cocartesian 辺で覆う。 -/
lemma exists_cocartesianPullbackEdge_of_base_edgeSurjective
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (a : Over B) (ha : Function.Surjective (a.hom.app (Opposite.op ⦋1⦌)))
    (e : E _⦋1⦌) (he : IsCocartesianEdge p e) :
    ∃ d : (pullback a.hom p) _⦋1⦌,
      IsCocartesianEdge (pullback.fst a.hom p) d ∧
        (pullback.snd a.hom p).app (Opposite.op ⦋1⦌) d = e := by
  obtain ⟨b, hb⟩ := ha (p.app (Opposite.op ⦋1⦌) e)
  exact exists_cocartesianPullbackEdge_of_base_edge p a e he b hb

end SerrePositivity.InfinityCategories
