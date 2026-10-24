module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitCapCoefficientFace
/-! # 指定係数対角変形の正本端点での全 prism 回収

概要：指定済み係数対角変形の全時間族を、正本端点表示の同じ係数 path へ同定する。
方針：区間 uncurry の逆の評価を戻し、元の pinched 端点輸送を全区間評価で消去する。
規約：指定変形と全時間の代表を保持する。
使われ方：明示 augmentation prism の両端固定正規化を指定係数辺へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "K" => dgGluingModelUnitCollarParameter R C D M X Y
lemma dgGluingHomDerivedCompositionDiagonalHomotopy_canonical_prism :
    (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h =
      (β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
        uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) ≫
          pinchedHomToIntervalMappingSpace _ _ := by
  apply intervalMappingUncurry_injective _ _
  calc
    _ = (α_ (Δ[1] : SSet.{max (u + 1) v w}) K Δ[1]).inv ≫
        (dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y).h := by
      have he := congrArg
        (fun q => (α_ (Δ[1] : SSet.{max (u + 1) v w}) K Δ[1]).inv ≫ q)
        (dgGluingHomDerivedCompositionDiagonalHomotopy_evaluate R C D M X Y)
      simpa only [dgGluingModelUnitCollarParameter, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp] using he
    _ = intervalMappingUncurry (dgGluingHomDerivedCoefficientIntervalHomotopy R C D M X Y).h := by
      rw [dgGluingHomDerivedCoefficientDiagonalHomotopy, dgGluingHomotopyRetarget_h]
      change _ ≫ (α_ (Δ[1] : SSet.{max (u + 1) v w}) K Δ[1]).hom ≫ _ = _
      rw [Iso.inv_hom_id_assoc]
    _ = _ := by
      have he := dgGluingPinchedIntervalEndpointTransport_uncurry
        (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C X.left).symm
        (dgGluingUniverseDerivedCoefficient_vertex R C D M Y.right).symm
        ((β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
          uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y))
      simpa only [dgGluingModelUnitCollarParameter,
        dgGluingHomDerivedCoefficientIntervalHomotopy, functorHomotopyPostcomp,
        dgGluingIntervalPathHomotopy, dgGluingDerivedCoefficientEndpointIso,
        Category.assoc] using he
end SerrePositivity.InfinityCategories
