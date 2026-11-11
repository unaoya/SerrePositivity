module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.OrdinaryPullbackRetracts
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGThickKernelNativeRetract
/-!
概要：通常 pullback の元対象条件は D-16 の実 thick 閉包と一致する。
方針：公開された native 安定 retract 判定を、既存の安定閉包と retract 閉性へ渡す。
規約：tria と nerve の輸送は D の公開入口を使い、元の対象条件を保持する。
使われ方：同じ平坦商の thick 核を元の充満 dg 包含へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackProperty_thickClosure_iff (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M) X ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M X := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty_iff_nativeStableRetract]
  constructor
  · rintro ⟨Y, hY, hr⟩
    have hy := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty_stableClosure_iff R C D M hC hD Y).mp hY
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty_of_retract R C D M hC hD X Y _ hy
    exact Classical.choice ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyRetract_ulift_iff _ _).mpr hr)
  · intro hx
    exact ⟨X, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨X, hx, rfl⟩, ⟨Retract.refl _⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
