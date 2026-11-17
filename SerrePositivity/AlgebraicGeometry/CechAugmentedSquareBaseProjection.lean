module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareMap

/-!
概要：同じ四角形の基底と中心だけを残す射影。
方針：二つの複体を零にし、元の四角形の射のtotalComplexMapを使う。
規約：基底・中心・その間の実際の写像を保つ。
使われ方：F8の全複体の余分な定数基底列を除く比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare
variable (s : CechAugmentedSquare.{u} R)

/-- 基底・中心と元の商写像を保持し、二つの複体を零にした四角形。 -/
def baseSquare : CechAugmentedSquare.{u} R where
  C := 0
  E := 0
  restriction := 0
  base := s.base
  centerBase := s.centerBase
  scalar := 0
  quotient := s.quotient
  center := 0
  scalar_cycle := by intro x; simp
  center_cycle := by intro x; simp
  commutes := by simp

/-- 元の四角形から同じ基底・中心への射影。 -/
def Map.baseProjection : Map s s.baseSquare where
  left := 0
  right := 0
  base := LinearMap.id
  center := LinearMap.id
  restriction := by ext n x; rfl
  scalar := by ext x; rfl
  quotient := by ext x; rfl
  center_naturality := by ext x; rfl

set_option backward.isDefEq.respectTransparency false in
/-- 同じ射影の既存の全複体の射は、各次数で全射。 -/
theorem baseProjection_totalComplexMap_surjective (n : ℕ) :
    Function.Surjective (((Map.baseProjection s).totalComplexMap).f n).hom := by
  have hz (k : ℕ) : Subsingleton ((0 : CochainComplex (ModuleCat.{u} R) ℕ).X k) :=
    ModuleCat.subsingleton_of_isZero
      ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) k).map_isZero (isZero_zero _))
  cases n with
  | zero =>
    change Function.Surjective (LinearMap.id : s.base →ₗ[R] s.base)
    exact Function.surjective_id
  | succ n =>
    cases n with
    | zero =>
      intro x
      refine ⟨(0, x.2), ?_⟩
      apply Prod.ext
      · exact (hz 0).elim _ _
      · rfl
    | succ n =>
      intro x
      exact ⟨0, Prod.ext ((hz n).elim _ _) ((hz (n + 1)).elim _ _)⟩

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
