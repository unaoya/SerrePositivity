module

public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor
public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison

/-! # Derived inversion of a map computed on a specified cofibrant approximation

Any ordinary left derived functor of a left Quillen functor sends a map
to an isomorphism exactly when its specified cofibrant approximation has
weak image. Both homotopy categories and their universes are arbitrary.
-/

@[expose] public section
universe vC uC vD uD vHC uHC vHD uHD
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Quillen
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {HC : Type uHC} [Category.{vHC} HC] {HD : Type uHD} [Category.{vHD} HD]
  (QC : C ⥤ HC) [QC.IsLocalization (weakEquivalences C)]
  (QD : D ⥤ HD) [QD.IsLocalization (weakEquivalences D)]
  {L : C ⥤ D} [IsLeftQuillen L] {LF : HC ⥤ HD}
  (α : QC ⋙ LF ⟶ L ⋙ QD) [LF.IsLeftDerivedFunctor α (weakEquivalences C)]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include α in
lemma derived_map_isIso_iff_cofibrant_image {X Y : C} (f : X ⟶ Y) :
    IsIso (LF.map (QC.map f)) ↔ weakEquivalences D (L.map ((cofibrantSource cof).map f)) := by
  let Q := cofibrantSource cof
  let q := cofibrantSourceComparison cof
  let H := QC ⋙ LF
  have hq (Z : C) : IsIso (H.map (q.app Z)) := by
    have : IsIso (QC.map (q.app Z)) := Localization.inverts QC (weakEquivalences C) _
      (cofibrantSourceComparison_trivialFibration cof Z).2
    exact inferInstanceAs (IsIso (LF.map (QC.map (q.app Z))))
  have := hq X
  have := hq Y
  have hn : H.map (Q.map f) ≫ H.map (q.app Y) = H.map (q.app X) ≫ H.map f := by
    simpa only [Functor.map_comp, Functor.id_map] using congrArg H.map (q.naturality f)
  have hi : IsIso (H.map (Q.map f)) ↔ IsIso (H.map f) := by
    rw [← isIso_comp_right_iff (H.map (Q.map f)) (H.map (q.app Y)), hn, isIso_comp_left_iff]
  have := cofibrantSource_isCofibrant cof X
  have := cofibrantSource_isCofibrant cof Y
  have := leftComparison_isIso QC QD α (Q.obj X)
  have := leftComparison_isIso QC QD α (Q.obj Y)
  have hα : H.map (Q.map f) ≫ α.app (Q.obj Y) =
      α.app (Q.obj X) ≫ QD.map (L.map (Q.map f)) := α.naturality (Q.map f)
  have hj : IsIso (H.map (Q.map f)) ↔ IsIso (QD.map (L.map (Q.map f))) := by
    rw [← isIso_comp_right_iff (H.map (Q.map f)) (α.app (Q.obj Y)), hα, isIso_comp_left_iff]
  exact hi.symm.trans (hj.trans (weakEquivalences_iff_isIso_map QD _).symm)

end SerrePositivity.Quillen
