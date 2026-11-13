module

public import SerrePositivity.AlgebraicGeometry.AugmentedCechConeMap
public import SerrePositivity.AlgebraicGeometry.CechZeroTermExtensionMap

/-!
概要：実際の増大写像と制限からなる Čech 四角形のデータと、その全複体。
方針：元の二つの複体、基底・中心、三つの辺と可換性を保持する。
規約：acyclicity はデータの仮定にしない。全複体の構成だけを自然にする。
使われ方：F8 の全複体に共通細分・底変換等の射を入れる共通の入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable (R : Type v) [CommRing R]

/-- 二つの Čech 複体と基底・中心の増大写像を持つ可換な四角形。 -/
structure CechAugmentedSquare where
  C : CochainComplex (ModuleCat.{u} R) ℕ
  E : CochainComplex (ModuleCat.{u} R) ℕ
  restriction : C ⟶ E
  base : ModuleCat.{u} R
  centerBase : ModuleCat.{u} R
  scalar : base →ₗ[R] C.X 0
  quotient : base →ₗ[R] centerBase
  center : centerBase →ₗ[R] E.X 0
  scalar_cycle : ∀ x, (C.d 0 1).hom (scalar x) = 0
  center_cycle : ∀ x, (E.d 0 1).hom (center x) = 0
  commutes : (restriction.f 0).hom.comp scalar = center.comp quotient

namespace CechAugmentedSquare
variable {R} (s : CechAugmentedSquare.{u} R)

/-- 中心の零次項を加えた複体。 -/
def source : CochainComplex (ModuleCat.{u} R) ℕ := cechZeroTermExtension s.C s.centerBase

/-- 実際の二つの辺の差の余鎖写像。 -/
def difference : s.source ⟶ s.E :=
  cechZeroTermDifference s.C s.E s.restriction s.centerBase s.center s.center_cycle

/-- 基底の二つの辺の組の増大写像。 -/
def augmentation : s.base →ₗ[R] s.source.X 0 := s.scalar.prod s.quotient

/-- 可換性とスカラーの閉性により、増大写像は cone のサイクルへ入る。 -/
theorem augmentation_cycle :
    (cechRefinementConeDifferential s.source s.E s.difference 0).comp s.augmentation = 0 := by
  apply LinearMap.ext
  intro x
  change ((s.restriction.f 0).hom (s.scalar x) - s.center (s.quotient x),
    -(s.C.d 0 1).hom (s.scalar x)) = (0, 0)
  apply Prod.ext
  · exact sub_eq_zero.mpr (LinearMap.congr_fun s.commutes x)
  · rw [s.scalar_cycle, neg_zero]

/-- 四角形から作る明示的な増大全複体。 -/
def totalComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  augmentedCechCone s.source s.E s.difference s.base s.augmentation s.augmentation_cycle

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
