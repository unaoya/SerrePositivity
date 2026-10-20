module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingHomDescentSpace
public import SerrePositivity.InfinityCategories.Derived.WeakRoofDescentRestriction

/-! # 選択空間全体上の商 Hom 作用

概要：商 Hom 上の作用と元の Hom 作用との比較を、可縮な選択空間全体上に束ねる。
方針：商の固定 Hom 包含と元・任意標的の屋根比較の二つの可換正方形を使う。
規約：対象対を固定した全高次族であり、異なる対象対の合成の整合性は別に構成する。
使われ方：任意の反転関手の coherent な延長の写像空間データ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 可縮な選択空間全体上で動く、商の実 Hom への作用。 -/
def dgInvertingHomActionFamily (P : Set D) (x y : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) :
    dgInvertingHomDescentSpace A D P x y F ⟶
      (ihom (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
        ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y))).obj
      (pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
        (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))) :=
  weakRoofDescentAction (dgRoofCorrespondenceMap A D P x y)
    (dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingRoofFunctorMap A D P x y F) (dgQuotientFixedHomRoofMap A D P x y)

/-- 全高次の作用の元の Hom への制限は、元の作用と一つの関手同型で比較される。 -/
def dgInvertingHomActionFamilyRestrictionIso (P : Set D) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y) :
    FunctorIso (dgInvertingHomActionFamily A D P x y F ≫
      (pre (pinchedHomChainMap ((DGQuotient.inclusion A D P).map x y))).app _)
      (SSet.const (functorVertex (pinchedHomMap F (Simplex.vertex x) (Simplex.vertex y)))) :=
  weakRoofDescentRestrictionIso (dgRoofCorrespondenceMap A D P x y)
    (dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingRoofFunctorMap A D P x y F)
    (dgOriginalFixedHomRoofMap A D P x y)
    (pinchedHomChainMap ((DGQuotient.inclusion A D P).map x y))
    (dgQuotientFixedHomRoofMap A D P x y)
    (pinchedHomMap F (Simplex.vertex x) (Simplex.vertex y))
    (dgFixedHomRoofMap_comparison A D P x y) (dgInvertingRoofFunctorMap_fixedHom A D P x y F)

end SerrePositivity.InfinityCategories
