module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PresheafOverArrows

/-!
概要：前層の slice の同値は引き戻しを制限関手へ移す。
方針：Yoneda 射上の fiber の全単射を、図式と射影の二変数で自然に貼る。
規約：小圏の Hom と前層の値の宇宙は同じ。
使われ方：制限関手の右 Kan 拡張から依存積を構成する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open OverPresheafAux

/-- 概要：通常の前層の引き戻しは slice の前層表示のもとで制限関手に対応する。
方針：各成分の fiber の全単射を使い、第一射影の自然性で二変数の自然性を検査する。
規約：標準 pullback と既存の slice の同値を使う。
使われ方：依存積の右随伴の構成。 -/
noncomputable def cofinalPresheafPullbackRestrictionIso {C : Type u} [SmallCategory C]
    {E B : Cᵒᵖ ⥤ Type u} (p : E ⟶ B) :
    Over.pullback p ⋙ (overEquivPresheafCostructuredArrow E).functor ≅
      (overEquivPresheafCostructuredArrow B).functor ⋙
        (Functor.whiskeringLeft _ _ (Type u)).obj (CostructuredArrow.map p).op :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun s ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackFiberEquiv p X s.unop).toIso)
    (by
      intro s t f
      apply ConcreteCategory.hom_ext
      intro a
      apply Subtype.ext
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackFiberEquiv p X t.unop _).val =
        (X.left.map f.unop.left.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackFiberEquiv p X s.unop a).val
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackFiberEquiv_val, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackFiberEquiv_val]
      exact (pullback.fst X.hom p).naturality_apply f.unop.left.op a.val))
    (by
      intro X Y f
      apply NatTrans.ext
      funext s
      apply ConcreteCategory.hom_ext
      intro a
      apply Subtype.ext
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackFiberEquiv p Y s.unop _).val =
        f.left.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackFiberEquiv p X s.unop a).val
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackFiberEquiv_val, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackFiberEquiv_val]
      have he : ((Over.pullback p).map f).left ≫ pullback.fst Y.hom p =
          pullback.fst X.hom p ≫ f.left := by
        change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
        exact pullback.lift_fst _ _ _
      exact ConcreteCategory.congr_hom (NatTrans.congr_app he (op s.unop.left)) a.val)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
