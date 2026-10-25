module

public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedCocone

/-!
概要：共終な途中段の下へ制限した元の filtered 表示は、同じ固定始域上でも余極限となる。
方針：元の全余錐の射影等式と、fixed-source coslice の filtered 余極限判定を使う。
規約：途中段の構造射を保持し、別の表示頂点を選ばない。
使われ方：coslice 内の compact 切断を元の表示の一段へ因子化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：任意の一点写像で表示した fixed-source coslice の filtered 余極限も底で判定できる。
方針：Yoneda の全単射により元の一点写像を頂点表示にする。
規約：元の一点写像と全余錐を変更しない。
使われ方：後合成された指定段の点写像への filtered 判定。 -/
lemma pointSourceCoslice_isColimitCone_iff_projection {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {C : SSet.{u + 1}} [Quasicategory C]
    (p : (Δ[0] : SSet.{u + 1}) ⟶ C)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceUnder p) (c : JoinCocone D) :
    IsColimitCone c ↔ IsColimitCone (mapJoinCocone (sliceUnderProjection p) c) := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  exact sourceCoslice_isColimitCone_iff_projection_kappaFiltered hκ x D c

/-- 概要：指定始域からの共終な filtered 部分表示に、元の余極限性が移る。
方針：構成した全余錐の射影を元の共終制限と同定する。
規約：始域と元の全余錐を固定する。
使われ方：元の表示段を保った相対 compact 因子化の余極限入力。 -/
lemma sourceCosliceRestrictedCocone_isColimit_of_rightCofinal
    {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {I A : SSet.{u}} [Quasicategory I] [Quasicategory A] [IsKappaFiltered κ A]
    {C : SSet.{u + 1}} [Quasicategory C]
    (a : (Δ[0] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj I)
    (s : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder a)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hs : IsRightCofinal (s ≫ sliceUnderProjection a)) :
    IsColimitCone (sourceCosliceRestrictedCocone a s D c) := by
  apply (pointSourceCoslice_isColimitCone_iff_projection hκ (a ≫ D) _ _).mpr
  apply (isColimitCone_iff_of_cocone_val_eq _ (c.restrict (s ≫ sliceUnderProjection a))
    (sourceCosliceRestrictedCocone_projection a s D c)).mpr
  exact (Ind.isColimitCone_iff_restrict_rightCofinal (s ≫ sliceUnderProjection a) hs c).mp hc

end SerrePositivity.InfinityCategories.F2.Presentable
