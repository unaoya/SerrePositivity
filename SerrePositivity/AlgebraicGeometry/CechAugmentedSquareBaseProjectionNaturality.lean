module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareBaseProjection

/-!
概要：同じ基底と中心への射影を、元の四角形の射に自然にする。
方針：二つの複体の射を零にし、基底と中心の実際の射を保持する。
規約：元の四角形の射と合成の向きを変えない。
使われ方：実際の余単体図式から同じ定数基底図式への射。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare
variable {s t : CechAugmentedSquare.{u} R}

/-- 元の四角形の射の基底と中心を、そのまま基底四角形へ渡す。 -/
def Map.onBaseSquare (m : Map s t) : Map s.baseSquare t.baseSquare where
  left := 0
  right := 0
  base := m.base
  center := m.center
  restriction := by ext n x; rfl
  scalar := by ext x; rfl
  quotient := m.quotient
  center_naturality := by ext x; rfl

/-- 基底と中心への同じ射影は、元の四角形の射に自然。 -/
theorem baseProjection_naturality (m : Map s t) :
    m.comp (Map.baseProjection t) = (Map.baseProjection s).comp m.onBaseSquare := by
  rfl

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
