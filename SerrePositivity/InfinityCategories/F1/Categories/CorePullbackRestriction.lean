module

public import SerrePositivity.InfinityCategories.F1.CatInfinity.CorePullbackIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の pullback の二射影を保持して core の pullback を回収する。
方針：指定された pullback を標準の pullback と同定し、既存の core 比較を合成する。
規約：一方の下辺の inner fibration 性を明示する。
使われ方：元の指定辺保存 Hom の貼り合わせを core に移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 元の二射影を変えず、inner fibration に沿う pullback の core を貼り合わせる。 -/
@[kerodon 01H6]
lemma quasicategoryCoreMap_isPullback_of_isPullback
    {A B C D : SSet.{u}} [Quasicategory B] [Quasicategory C] [Quasicategory D]
    {p : A ⟶ B} {q : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D}
    [InnerFibration f] (h : IsPullback p q f g) :
    IsPullback (quasicategoryCoreMap p) (quasicategoryCoreMap q)
      (quasicategoryCoreMap f) (quasicategoryCoreMap g) := by
  have hw : quasicategoryCoreMap p ≫ quasicategoryCoreMap f =
      quasicategoryCoreMap q ≫ quasicategoryCoreMap g := by
    change quasicategoryCoreFunctor.map p ≫ quasicategoryCoreFunctor.map f =
      quasicategoryCoreFunctor.map q ≫ quasicategoryCoreFunctor.map g
    rw [← Functor.map_comp, ← Functor.map_comp, h.w]
  let e := quasicategoryCoreFunctor.mapIso h.isoPullback ≪≫ F2.corePullbackIso f g
  apply IsPullback.of_iso_pullback ⟨hw⟩ e
  · change quasicategoryCoreMap h.isoPullback.hom ≫
        F2.corePullbackMap f g ≫ pullback.fst _ _ = quasicategoryCoreMap p
    rw [F2.corePullbackMap_fst]
    change quasicategoryCoreFunctor.map h.isoPullback.hom ≫
      quasicategoryCoreFunctor.map (pullback.fst f g) = quasicategoryCoreFunctor.map p
    rw [← Functor.map_comp, h.isoPullback_hom_fst]
  · change quasicategoryCoreMap h.isoPullback.hom ≫
        F2.corePullbackMap f g ≫ pullback.snd _ _ = quasicategoryCoreMap q
    rw [F2.corePullbackMap_snd]
    change quasicategoryCoreFunctor.map h.isoPullback.hom ≫
      quasicategoryCoreFunctor.map (pullback.snd f g) = quasicategoryCoreFunctor.map q
    rw [← Functor.map_comp, h.isoPullback_hom_snd]

end SerrePositivity.InfinityCategories
