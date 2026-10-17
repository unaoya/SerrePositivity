module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Composition
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # 自由path連結の右単位と単位pathの比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

lemma pathComposition_right_unit (K : ComplexQuiver A D) {x y : D} (p : PathIndex D x y) :
    pathComposition A D K p (.inl ⟨rfl⟩) =
      (ρ_ (pathTensor A D K p)).hom ≫ pathInclusion A D K x y p := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    change (λ_ (𝟙_ (Complex A))).hom ≫ _ = (ρ_ (𝟙_ (Complex A))).hom ≫ _
    rw [unitors_equal]
  | inr w => rfl

lemma composition_path_unit (K : ComplexQuiver A D) (x y : D) (p : PathIndex D x y) :
    (pathInclusion A D K x y p ⊗ₘ unitInclusion A D K y) ≫ composition A D K x y y =
      (ρ_ (pathTensor A D K p)).hom ≫ pathInclusion A D K x y p :=
  (composition_pathInclusion A D K x y y p (.inl ⟨rfl⟩)).trans
    (pathComposition_right_unit A D K p)

lemma composition_right_unit (K : ComplexQuiver A D) (x y : D) :
    (homComplex A D K x y ◁ unitInclusion A D K y) ≫ composition A D K x y y =
      (ρ_ (homComplex A D K x y)).hom := by
  apply (tensorRightCoproductIsColimit (𝟙_ (Complex A))
    (pathTensor A D K (x := x) (y := y))).hom_ext
  rintro ⟨p⟩
  change (pathInclusion A D K x y p ▷ 𝟙_ (Complex A)) ≫
      ((homComplex A D K x y ◁ unitInclusion A D K y) ≫ composition A D K x y y) = _
  rw [← Category.assoc, ← tensorHom_def, composition_path_unit]
  exact (rightUnitor_naturality (pathInclusion A D K x y p)).symm

end SerrePositivity.DifferentialGraded.FreeDGCategory
