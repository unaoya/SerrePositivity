module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareMap

/-!
概要：同じ四角形の中心側とY側の包含・射影。
方針：一方の複体と対応する基底を零にし、既存の四角形の射を使う。
規約：残す複体・基底と実際の増大写像を保つ。
使われ方：F8の全複体を中心側とY側に分ける短完全列。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped ZeroObject
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare
variable (s : CechAugmentedSquare.{u} R)

/-- 元のC・基底・スカラーを保ち、Eと中心基底を零にした四角形。 -/
def leftSquare : CechAugmentedSquare.{u} R where
  C := s.C
  E := HomologicalComplex.zero
  restriction := 0
  base := s.base
  centerBase := 0
  scalar := s.scalar
  quotient := 0
  center := 0
  scalar_cycle := s.scalar_cycle
  center_cycle := by intro x; simp
  commutes := by ext x; rfl

/-- 元のE・中心基底・中心の増大を保ち、Cと基底を零にした四角形。 -/
def rightSquare : CechAugmentedSquare.{u} R where
  C := HomologicalComplex.zero
  E := s.E
  restriction := 0
  base := 0
  centerBase := s.centerBase
  scalar := 0
  quotient := 0
  center := s.center
  scalar_cycle := by intro x; simp
  center_cycle := s.center_cycle
  commutes := by ext x; simp

/-- 元の四角形から同じY側への射影。 -/
def Map.leftProjection : Map s s.leftSquare where
  left := 𝟙 _
  right := 0
  base := LinearMap.id
  center := 0
  restriction := by ext n x; rfl
  scalar := by ext x; rfl
  quotient := by ext x; rfl
  center_naturality := by ext x; rfl

/-- 同じ中心側から元の四角形への包含。 -/
def Map.rightInclusion : Map s.rightSquare s where
  left := 0
  right := 𝟙 _
  base := 0
  center := LinearMap.id
  restriction := by
    change (0 : _ ⟶ s.E) ≫ 𝟙 _ = 0 ≫ s.restriction
    simp only [Category.comp_id, Limits.zero_comp]
  scalar := by ext x; simp
  quotient := by
    ext x
    change (0 : s.centerBase) = s.quotient 0
    exact s.quotient.map_zero.symm
  center_naturality := by ext x; rfl

/-- 元の同じ全複体の包含と射影の合成は零。 -/
theorem rightInclusion_leftProjection :
    (Map.rightInclusion s).totalComplexMap ≫ (Map.leftProjection s).totalComplexMap = 0 := by
  ext n x
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
