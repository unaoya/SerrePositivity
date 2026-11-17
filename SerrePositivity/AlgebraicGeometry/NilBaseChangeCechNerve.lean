module

public import SerrePositivity.AlgebraicGeometry.CechNerveCartesianBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：Cartesian な Arrow の射の実際の Čech nerve は各項で nil 閉厚化。
方針：同じ nerve の Cartesian square に二つの底変換安定性を適用する。
規約：閉埋め込みと全射性を同じ元の写像について示す。
使われ方：nil 閉厚化のタプル増大図式の係数移送（計画 N04）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- nil 閉厚化の底変換として、元の nerve の射も各項で閉埋め込みかつ全射。 -/
theorem nilBaseChange_cechNerve_map
    {f g : Arrow Scheme.{u}} (F : f ⟶ g)
    (H : IsPullback F.left f.hom g.hom F.right)
    [IsClosedImmersion F.right] [Surjective F.right] (n : SimplexCategoryᵒᵖ) :
    IsClosedImmersion ((Arrow.mapCechNerve F).app n) ∧
      Surjective ((Arrow.mapCechNerve F).app n) := by
  have h := (isPullback_cechNerve_base F H n).flip
  exact ⟨MorphismProperty.of_isPullback h (inferInstance : IsClosedImmersion F.right),
    MorphismProperty.of_isPullback h (inferInstance : Surjective F.right)⟩

end SerrePositivity.AlgebraicGeometry
