module

public import SerrePositivity.InfinityCategories.F2.PullbackConeComponentCriterion
public import SerrePositivity.InfinityCategories.F2.ConeValEquality
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits

/-!
概要：任意の厳密な引き戻し正方形内での指定錐の極限判定。
方針：標準引き戻しとの同型へ元の錐を移し、元の脚との一致を照合する。
規約：元の正方形の頂点と脚を変更しない。
使われ方：反対圏による余極限側への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：引き戻し正方形の二射影と底の錐が極限なら元の錐も極限。
方針：標準引き戻しへの同型は元の射影を保ち、極限性を保存・反映する。
規約：一方の関手 p だけを inner fibration と仮定する。
使われ方：双対化で余極限の成分判定を得る。 -/
lemma isLimitCone_of_isPullback_of_components {J W E D B : SSet.{u}}
    [Quasicategory W] [Quasicategory E] [Quasicategory D] [Quasicategory B]
    {a : W ⟶ E} {b : W ⟶ D} {p : E ⟶ B} {q : D ⟶ B}
    (s : IsPullback a b p q) [InnerFibration p] {r : J ⟶ W} (c : JoinCone r)
    (ha : IsLimitCone (mapJoinCone a c)) (hb : IsLimitCone (mapJoinCone b c))
    (hp : IsLimitCone (mapJoinCone p (mapJoinCone a c))) : IsLimitCone c := by
  apply ((qCatEquivalenceOfIso s.isoPullback).isLimitCone_iff c).2
  apply isLimitCone_pullback_of_components p q (mapJoinCone s.isoPullback.hom c)
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 ha
    change (c.val ≫ s.isoPullback.hom) ≫ pullback.fst p q = c.val ≫ a
    rw [Category.assoc, s.isoPullback_hom_fst]
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 hb
    change (c.val ≫ s.isoPullback.hom) ≫ pullback.snd p q = c.val ≫ b
    rw [Category.assoc, s.isoPullback_hom_snd]
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 hp
    change ((c.val ≫ s.isoPullback.hom) ≫ pullback.fst p q) ≫ p = (c.val ≫ a) ≫ p
    rw [Category.assoc c.val, s.isoPullback_hom_fst]

end SerrePositivity.InfinityCategories.F2
