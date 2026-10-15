module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Module.LeftRepresentable

/-! # 対角Homを値とする単位dg bimodule -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Hom_D(b,c)を値とする対角bimodule。 -/
def diagonal : Bimodule A D D := dgYoneda A D

lemma diagonal_rightAt (c : D) : (diagonal A D).rightAt c = representable A c := rfl

lemma diagonal_value (b c : D) : (diagonal A D).value b c = (b ⟶[Complex A] c) := rfl

lemma diagonal_leftAt (b : D) : (diagonal A D).leftAt b = leftRepresentable A b := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (diagonal A D).leftAt b) (G := leftRepresentable A b) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change (((moduleHomπ A D (representable A x) (representable A y) b).f p
      ((yonedaHom A D x y).f p f)).v r n hn) h =
    leftAction A (leftRepresentable A b) f h hn
  rw [yonedaHom_element, leftRepresentable_action]

end SerrePositivity.DifferentialGraded.Bimodule
