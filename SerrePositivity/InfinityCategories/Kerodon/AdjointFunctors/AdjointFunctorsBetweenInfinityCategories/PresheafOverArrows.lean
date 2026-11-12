module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
概要：前層の通常の slice の表示と引き戻しの対応。
方針：小さい OverArrows を Yoneda 射による slice の Hom と同定する。
規約：添字圏は Type u の小圏、前層も Type u 値。単体集合への適用は圏同値で移す。
使われ方：引き戻し関手の右随伴を制限関手の右 Kan 拡張から構成する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open OverPresheafAux

/-- 概要：Yoneda 射の上の小さい fiber は通常の slice の Hom と全単射。
方針：Yoneda 対応の両方向に底との可換性を添える。
規約：小圏の Hom と前層の値を同じ宇宙に取る。
使われ方：引き戻し随伴の Hom 対応を前層の slice 表示へ移す。 -/
def cofinalOverArrowEquiv {C : Type u} [SmallCategory C] {B : Cᵒᵖ ⥤ Type u}
    (X : Over B) {c : C} (s : yoneda.obj c ⟶ B) :
    OverArrows X.hom s ≃ (Over.mk s ⟶ X) where
  toFun a := Over.homMk (yonedaEquiv.symm a.val) (by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact a.property.app)
  invFun f := ⟨yonedaEquiv f.left, MakesOverArrow.of_arrow f.w⟩
  left_inv a := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _
  right_inv f := by apply Over.OverMorphism.ext; exact Equiv.symm_apply_apply _ _

/-- 概要：小さい fiber の射を Yoneda の対応で slice の射へ移すと、その左辺は元の Yoneda 射。
方針：全単射の定義を読む。
規約：厳密な等式。
使われ方：fiber の射の自然性の検査。 -/
lemma cofinalOverArrowEquiv_left {C : Type u} [SmallCategory C] {B : Cᵒᵖ ⥤ Type u}
    (X : Over B) {c : C} (s : yoneda.obj c ⟶ B) (a : OverArrows X.hom s) :
    (cofinalOverArrowEquiv X s a).left = yonedaEquiv.symm a.val := rfl

/-- 概要：引き戻し前層の小さい fiber は、底図式を合成した元の fiber と全単射。
方針：slice の引き戻し随伴の Hom 全単射と Yoneda 対応を合成する。
規約：これは通常の前層の圏の随伴であり、straightening を使わない。
使われ方：slice の同値による引き戻しと制限関手の自然同型。 -/
noncomputable def cofinalPresheafPullbackFiberEquiv {C : Type u} [SmallCategory C]
    {E B : Cᵒᵖ ⥤ Type u} (p : E ⟶ B) (X : Over B) (s : CostructuredArrow yoneda E) :
    OverArrows ((Over.pullback p).obj X).hom s.hom ≃ OverArrows X.hom (s.hom ≫ p) :=
  (cofinalOverArrowEquiv _ _).trans
    (((Over.mapPullbackAdj p).homEquiv (Over.mk s.hom) X).symm.trans
      (cofinalOverArrowEquiv X (s.hom ≫ p)).symm)

/-- 概要：引き戻しの fiber の全単射は第一射影の各成分で与えられる。
方針：引き戻し随伴の逆の Hom 対応を計算して Yoneda 対応を消去する。
規約：標準 pullback の第一射影との厳密な一致。
使われ方：二変数の自然性の検査。 -/
lemma cofinalPresheafPullbackFiberEquiv_val {C : Type u} [SmallCategory C]
    {E B : Cᵒᵖ ⥤ Type u} (p : E ⟶ B) (X : Over B) (s : CostructuredArrow yoneda E)
    (a : OverArrows ((Over.pullback p).obj X).hom s.hom) :
    (cofinalPresheafPullbackFiberEquiv p X s a).val =
      (pullback.fst X.hom p).app (op s.left) a.val := by
  change yonedaEquiv (yonedaEquiv.symm a.val ≫ pullback.fst X.hom p) = _
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
