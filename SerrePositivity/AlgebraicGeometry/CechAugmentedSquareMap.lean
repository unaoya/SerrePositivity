module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquare

/-!
概要：可換な Čech 四角形の射と全複体の余鎖写像。
方針：四つの成分と辺の可換性を使い、既存の増大項付き cone の射を適用する。
規約：完全性の仮定は使わず、恒等・合成まで保つ。
使われ方：F8 の共通細分・底変換・閉厚化・Frobenius・余極限の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare

/-- 基底・中心・二つの複体の射で全ての辺を保つ四角形の射。 -/
structure Map (s t : CechAugmentedSquare.{u} R) where
  left : s.C ⟶ t.C
  right : s.E ⟶ t.E
  base : s.base →ₗ[R] t.base
  center : s.centerBase →ₗ[R] t.centerBase
  restriction : s.restriction ≫ right = left ≫ t.restriction
  scalar : (left.f 0).hom.comp s.scalar = t.scalar.comp base
  quotient : center.comp s.quotient = t.quotient.comp base
  center_naturality : (right.f 0).hom.comp s.center = t.center.comp center

namespace Map
variable {s t r : CechAugmentedSquare.{u} R}

/-- 四角形の射は基底の増大写像を保つ。 -/
theorem augmentation (m : Map s t) :
    ((cechZeroTermExtensionMap m.left m.center).f 0).hom.comp s.augmentation =
      t.augmentation.comp m.base := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact LinearMap.congr_fun m.scalar x
  · exact LinearMap.congr_fun m.quotient x

/-- 可換な四角形の射から、全複体の余鎖写像を作る。 -/
def totalComplexMap (m : Map s t) : s.totalComplex ⟶ t.totalComplex :=
  augmentedCechConeMap s.augmentation_cycle t.augmentation_cycle
    (cechZeroTermExtensionMap m.left m.center) m.right m.base
    (cechZeroTermDifference_naturality s.restriction t.restriction s.center t.center
      s.center_cycle t.center_cycle m.left m.right m.center m.restriction m.center_naturality)
    m.augmentation

/-- 四角形の恒等射。 -/
def id (s : CechAugmentedSquare.{u} R) : Map s s where
  left := 𝟙 _
  right := 𝟙 _
  base := LinearMap.id
  center := LinearMap.id
  restriction := by simp
  scalar := by simp
  quotient := by simp
  center_naturality := by simp

/-- 四角形の射の合成。 -/
def comp (m : Map s t) (n : Map t r) : Map s r where
  left := m.left ≫ n.left
  right := m.right ≫ n.right
  base := n.base.comp m.base
  center := n.center.comp m.center
  restriction := by
    rw [← Category.assoc, m.restriction, Category.assoc, n.restriction, Category.assoc]
  scalar := by
    change (n.left.f 0).hom.comp ((m.left.f 0).hom.comp s.scalar) = _
    rw [m.scalar, ← LinearMap.comp_assoc, n.scalar, LinearMap.comp_assoc]
  quotient := by
    rw [LinearMap.comp_assoc, m.quotient, ← LinearMap.comp_assoc, n.quotient,
      LinearMap.comp_assoc]
  center_naturality := by
    change (n.right.f 0).hom.comp ((m.right.f 0).hom.comp s.center) = _
    rw [m.center_naturality, ← LinearMap.comp_assoc, n.center_naturality, LinearMap.comp_assoc]

/-- 全複体への写像は四角形の恒等射を保つ。 -/
theorem totalComplexMap_id (s : CechAugmentedSquare.{u} R) :
    (id s).totalComplexMap = 𝟙 s.totalComplex := by
  ext n x
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

/-- 全複体への写像は四角形の射の合成を保つ。 -/
theorem totalComplexMap_comp (m : Map s t) (n : Map t r) :
    (m.comp n).totalComplexMap = m.totalComplexMap ≫ n.totalComplexMap := by
  ext n x
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

end Map
end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
