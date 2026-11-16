module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareLeftRight
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareMap

/-!
概要：同じ左右の四角形への包含と射影の自然性。
方針：元の四角形の四成分の外延性と、元の射の単位・合成を使う。
規約：元のC/baseまたはE/centerの射を保持する。
使われ方：F8の同じ短完全列を余単体図式にまとめる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare
variable {s t r : CechAugmentedSquare.{u} R}

/-- 元の射のCと基底の射を、そのままY側へ渡す。 -/
def Map.onLeftSquare (m : Map s t) : Map s.leftSquare t.leftSquare where
  left := m.left
  right := 0
  base := m.base
  center := 0
  restriction := by ext n x; rfl
  scalar := m.scalar
  quotient := by ext x; rfl
  center_naturality := by ext x; rfl

/-- 元の射のEと中心の射を、そのまま中心側へ渡す。 -/
def Map.onRightSquare (m : Map s t) : Map s.rightSquare t.rightSquare where
  left := 0
  right := m.right
  base := 0
  center := m.center
  restriction := by
    change 0 ≫ m.right = (0 : _ ⟶ _) ≫ 0
    simp only [zero_comp]
  scalar := by ext x; rfl
  quotient := by
    ext x
    change m.center 0 = (0 : t.centerBase)
    exact m.center.map_zero
  center_naturality := m.center_naturality

/-- 同じY側への射は単位を保つ。 -/
theorem Map.onLeftSquare_id (s : CechAugmentedSquare.{u} R) :
    (Map.id s).onLeftSquare = Map.id s.leftSquare := by
  apply Map.ext_components
  · rfl
  · have h : IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} R) ℕ) :=
      HomologicalComplex.isZero_zero
    exact h.eq_of_src _ _
  · rfl
  · apply LinearMap.ext
    intro x
    exact (ModuleCat.subsingleton_of_isZero (isZero_zero (ModuleCat.{u} R))).elim _ _

/-- 同じ中心側への射は単位を保つ。 -/
theorem Map.onRightSquare_id (s : CechAugmentedSquare.{u} R) :
    (Map.id s).onRightSquare = Map.id s.rightSquare := by
  apply Map.ext_components
  · have h : IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} R) ℕ) :=
      HomologicalComplex.isZero_zero
    exact h.eq_of_src _ _
  · rfl
  · apply LinearMap.ext
    intro x
    exact (ModuleCat.subsingleton_of_isZero (isZero_zero (ModuleCat.{u} R))).elim _ _
  · rfl

/-- 同じY側への射は合成を保つ。 -/
theorem Map.onLeftSquare_comp (m : Map s t) (n : Map t r) :
    (m.comp n).onLeftSquare = m.onLeftSquare.comp n.onLeftSquare := by
  apply Map.ext_components
  · rfl
  · exact (comp_zero).symm
  · rfl
  · exact (LinearMap.zero_comp _).symm

/-- 同じ中心側への射は合成を保つ。 -/
theorem Map.onRightSquare_comp (m : Map s t) (n : Map t r) :
    (m.comp n).onRightSquare = m.onRightSquare.comp n.onRightSquare := by
  apply Map.ext_components
  · exact (comp_zero).symm
  · rfl
  · exact (LinearMap.zero_comp _).symm
  · rfl

/-- 元の四角形から同じY側への射影は、元の射に自然。 -/
theorem leftProjection_naturality (m : Map s t) :
    m.comp (Map.leftProjection t) = (Map.leftProjection s).comp m.onLeftSquare := by
  apply Map.ext_components
  · change m.left ≫ 𝟙 _ = 𝟙 _ ≫ m.left
    rw [Category.comp_id, Category.id_comp]
  · change m.right ≫ 0 = (0 : _ ⟶ _) ≫ 0
    rw [comp_zero, zero_comp]
  · ext x; rfl
  · ext x; rfl

/-- 同じ中心側からの包含は、元の四角形の射に自然。 -/
theorem rightInclusion_naturality (m : Map s t) :
    m.onRightSquare.comp (Map.rightInclusion t) = (Map.rightInclusion s).comp m := by
  apply Map.ext_components
  · change 0 ≫ (0 : _ ⟶ _) = 0 ≫ m.left
    rw [zero_comp, zero_comp]
  · change m.right ≫ 𝟙 _ = 𝟙 _ ≫ m.right
    rw [Category.comp_id, Category.id_comp]
  · ext x
    change (0 : t.base) = m.base 0
    exact m.base.map_zero.symm
  · ext x; rfl

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
