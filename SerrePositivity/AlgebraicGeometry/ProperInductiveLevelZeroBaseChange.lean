module

public import SerrePositivity.AlgebraicGeometry.ProperInductiveLevel
public import SerrePositivity.AlgebraicGeometry.ClosedRestrictionBaseChange

/-!
概要：帰納的レベル0の任意の底変換と、始域の同型による移送。
方針：二段の実際の pullback を作り、Cartesian な正方形で各射の性質を移す。
規約：底変換に平坦性を仮定しない。レベルの有限性は別途示す。
使われ方：G3 の nilimmersion と proper fppf の零段の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
namespace ProperInductiveLevel

/-- 帰納的レベルは始域の同型で不変。 -/
theorem iso_source_iff {X X' Y : Scheme.{u}} (e : X' ≅ X) (f : X ⟶ Y) (n : ℕ) :
    ProperInductiveLevel n (e.hom ≫ f) ↔ ProperInductiveLevel n f := by
  constructor
  · intro h
    exact h.of_refinement e.hom f rfl
  · intro h
    exact h.of_refinement e.inv (e.hom ≫ f) (by simp)

/-- レベル0の実際の細分を任意の基底変更に沿って移す。 -/
theorem zero_baseChange {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (hf : ProperInductiveLevel 0 f) : ProperInductiveLevel 0 (pullback.snd f g) := by
  obtain ⟨X', Y', i, q, a, hi, his, hif, hq, hqf, hqs, hqfp, ha⟩ := hf
  letI := hi
  letI := his
  letI := hif
  letI := hq
  letI := hqf
  letI := hqs
  letI := hqfp
  let Y₁ := pullback i g
  let X₁ := pullback (q ≫ i) g
  let i₁ : Y₁ ⟶ T := pullback.snd i g
  let q₁ : X₁ ⟶ Y₁ := closedRestrictionBaseChangeMap i q g
  have H := isPullback_closedRestrictionBaseChangeMap i q g
  letI : IsProper q₁ := MorphismProperty.of_isPullback H inferInstance
  letI : Flat q₁ := MorphismProperty.of_isPullback H inferInstance
  letI : Surjective q₁ := MorphismProperty.of_isPullback H inferInstance
  letI : LocallyOfFinitePresentation q₁ := MorphismProperty.of_isPullback H inferInstance
  let a₁ : X₁ ⟶ pullback f g :=
    pullback.lift (pullback.fst (q ≫ i) g ≫ a) (pullback.snd (q ≫ i) g) (by
      rw [Category.assoc, ha]
      exact pullback.condition)
  refine ⟨X₁, Y₁, i₁, q₁, a₁, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  dsimp [a₁, i₁, q₁]
  simp

end ProperInductiveLevel
end SerrePositivity.AlgebraicGeometry
