module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareBaseProjection
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareLeftRightNaturality

/-!
概要：左右へ取った同じ基底射影の全成分は全射。
方針：元の基底・中心の恒等と、零対象の要素の一意性を使う。
規約：baseProjectionに同じ左右の射の操作を適用する。
使われ方：実際のF8の核の短完全列。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare
variable (s : CechAugmentedSquare.{u} R)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ基底射影のY側の全複体の各成分は全射。 -/
theorem baseProjection_onLeftSquare_totalComplexMap_surjective (n : ℕ) :
    Function.Surjective ((((Map.baseProjection s).onLeftSquare).totalComplexMap).f n).hom := by
  have h0 : Subsingleton (0 : ModuleCat.{u} R) := ModuleCat.subsingleton_of_isZero (isZero_zero _)
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
      exact ⟨0, Prod.ext ((hz 0).elim _ _) (h0.elim _ _)⟩
    | succ n =>
      intro x
      exact ⟨0, Prod.ext (h0.elim _ _) ((hz (n + 1)).elim _ _)⟩

set_option backward.isDefEq.respectTransparency false in
/-- 同じ基底射影の中心側の全複体の各成分は全射。 -/
theorem baseProjection_onRightSquare_totalComplexMap_surjective (n : ℕ) :
    Function.Surjective ((((Map.baseProjection s).onRightSquare).totalComplexMap).f n).hom := by
  have h0 : Subsingleton (0 : ModuleCat.{u} R) := ModuleCat.subsingleton_of_isZero (isZero_zero _)
  have hz (k : ℕ) : Subsingleton ((0 : CochainComplex (ModuleCat.{u} R) ℕ).X k) :=
    ModuleCat.subsingleton_of_isZero
      ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) k).map_isZero (isZero_zero _))
  cases n with
  | zero =>
    intro x
    exact ⟨0, h0.elim _ _⟩
  | succ n =>
    cases n with
    | zero =>
      intro x
      refine ⟨(0, x.2), ?_⟩
      exact Prod.ext (h0.elim _ _) rfl
    | succ n =>
      intro x
      exact ⟨0, Prod.ext ((hz n).elim _ _) (h0.elim _ _)⟩

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
