module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModelUnitCapCoefficientFace
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarParameter R C D M X Y
lemma dgGluingHomDerivedCompositionDiagonalHomotopy_canonical_prism :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h =
      (β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
        uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  calc
    _ = (α_ (Δ[1] : SSet.{max (u + 1) v w}) K Δ[1]).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y).h := by
      have he := congrArg
        (fun q => (α_ (Δ[1] : SSet.{max (u + 1) v w}) K Δ[1]).inv ≫ q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionDiagonalHomotopy_evaluate R C D M X Y)
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarParameter, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp] using he
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientIntervalHomotopy R C D M X Y).h := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientDiagonalHomotopy, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyRetarget_h]
      change _ ≫ (α_ (Δ[1] : SSet.{max (u + 1) v w}) K Δ[1]).hom ≫ _ = _
      rw [Iso.inv_hom_id_assoc]
    _ = _ := by
      have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedIntervalEndpointTransport_uncurry
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C X.left).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_vertex R C D M Y.right).symm
        ((β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
          uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientIntervalPath R C D M X Y))
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarParameter,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientIntervalHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathHomotopy, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientEndpointIso,
        Category.assoc] using he
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
