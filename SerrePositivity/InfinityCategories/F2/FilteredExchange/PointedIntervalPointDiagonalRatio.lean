module

public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedIntervalPointPrismDiagonal
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoValueRatioDiagonal
/-!
概要：指定一点の実対角値の比を同じ普遍比較の比へ戻す。
方針：一般の区間族のまま native 終点と指定比較の値を照合する。
規約：区間族・指定点・全初期値・辺値因子を保持する。
使われ方：raw 余極限辺の比の作用表示への接続。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable {C K : SSet.{u + 1}} [Quasicategory C]
  {x y : SpaceInfinity.{u} _⦋0⦌} (a : C ⟶ intervalMappingSpace x y)
  (l : C _⦋0⦌) (f : K ⟶ vertexFiber pointedSpaceProjection x)
local notation "p" => pointedSpaceProjection
local notation "v" => (SSet.const (a.app (Opposite.op ⦋0⦌) l) : K ⟶ intervalMappingSpace x y)
local notation "β" => intervalMappingUncurry v
local notation "h₀" => intervalMappingUncurry_zero v
local notation "h₁" => intervalMappingUncurry_one v
local notation "P" => pointedIntervalTransportPointPrism a l f
local notation "D" =>
  leftFibrationPrism_diagonalTransportIso p f (f ≫ pointedIntervalTransportAt a l)
        β h₀ h₁ P (pointedIntervalTransportPointPrism_start a l f)
        (pointedIntervalTransportPointPrism_finish a l f)
        (Eq.trans (pointedIntervalTransportPointPrism_projection a l f)
          (intervalMappingPoint_uncurry a l))
/-- 概要：元の指定一点対角値と辺値の逆の比。方針：同じ指定二因子を保持。
規約：再選択しない。使われ方：raw 比の一般区間表示。 -/
def pointedIntervalPointDiagonalValueRatio {Y Z : SSet.{u + 1}}
    (v₁ : vertexFiber p x ⟶ Y) (v₂ : vertexFiber p y ⟶ Z) (g : Y ⟶ Z)
    (e : FunctorIso (pointedIntervalTransportAt a l ≫ v₂) (v₁ ≫ g)) :=
    ((functorIsoOfEq (e.precomp f)
          (Category.assoc f (pointedIntervalTransportAt a l) v₂).symm rfl).symm ≪≫
      FunctorIso.postcomp D v₂)
/-- 概要：元の指定対角値の比は同じ一点普遍比較の比。
方針：同じ native 終点と元の二因子を保持して合成する。
規約：値を再選択しない。使われ方：最後辺の raw 比の照合。 -/
lemma pointedIntervalPointDiagonal_ratio_heq_factors {Y Z : SSet.{u + 1}}
    (v₁ : vertexFiber p x ⟶ Y) (v₂ : vertexFiber p y ⟶ Z) (g : Y ⟶ Z)
    (e : FunctorIso (pointedIntervalTransportAt a l ≫ v₂) (v₁ ≫ g)) :
    HEq (pointedIntervalPointDiagonalValueRatio a l f v₁ v₂ g e)
      ((e.precomp f).symm ≪≫
        ((pointedIntervalTransportAt_universalIso a l).precomp f).postcomp v₂) := by
  have hc : intervalMappingCurryOfEndpoints β h₀ h₁ = v := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints β h₀ h₁
  have ht := congrArg (fun k => functorVertex (k ≫ v₂))
    ((congrArg (diagonalFiberTransport p f) hc).trans
      (diagonalFiberTransport_constant_interval p f (a.app (Opposite.op ⦋0⦌) l)))
  exact functorIso_value_ratio_heq_vertices (pointedIntervalTransportAt a l)
    v₁ v₂ g e f _ (((pointedIntervalTransportAt_universalIso a l).precomp f).postcomp v₂)
    ht (pointedIntervalTransportAt_universalIso_precomp_postcomp_heq_point_diagonal a l f v₂).symm
/-- 概要：同じ指定区間の比への表示変更を普遍比較の比へ接続する。
方針：一般区間で二つの指定値照合を先に合成する。
規約：元の比を保持。使われ方：raw 辺への代入時の照合。 -/
lemma pointedIntervalPointDiagonal_ratio_heq_factors_of_heq {Y Z : SSet.{u + 1}}
    (v₁ : vertexFiber p x ⟶ Y) (v₂ : vertexFiber p y ⟶ Z) (g : Y ⟶ Z)
    (e : FunctorIso (pointedIntervalTransportAt a l ≫ v₂) (v₁ ≫ g))
    {W : Sort _} (R : W) (hR : HEq R (pointedIntervalPointDiagonalValueRatio a l f v₁ v₂ g e)) :
    HEq R ((e.precomp f).symm ≪≫
      ((pointedIntervalTransportAt_universalIso a l).precomp f).postcomp v₂) :=
  hR.trans (pointedIntervalPointDiagonal_ratio_heq_factors a l f v₁ v₂ g e)
end
end SerrePositivity.InfinityCategories.F2
