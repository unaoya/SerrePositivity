module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackRetracts
public import SerrePositivity.InfinityCategories.Derived.DGThickKernelNativeRetract
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackProperty_thickClosure_iff (X : DGGluingObject R C D M) :
    let := dgGluing_isDGPretriangulated R C D M hC hD
    dgThickClosureProperty R (DGGluingObject R C D M)
      (dgGluingPullbackProperty R C D M) X ↔ dgGluingPullbackProperty R C D M X := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  rw [dgThickClosureProperty_iff_nativeStableRetract]
  constructor
  · rintro ⟨Y, hY, hr⟩
    have hy := (dgGluingPullbackProperty_stableClosure_iff R C D M hC hD Y).mp hY
    apply dgGluingPullbackProperty_of_retract R C D M hC hD X Y _ hy
    exact Classical.choice ((homotopyRetract_ulift_iff _ _).mpr hr)
  · intro hx
    exact ⟨X, StableVertexClosure.of_mem ⟨X, hx, rfl⟩, ⟨Retract.refl _⟩⟩
end SerrePositivity.InfinityCategories
