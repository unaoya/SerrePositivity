module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # The image–coimage short exact sequence of an exact pair -/
@[expose] public section
noncomputable section
universe v u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The image of the first map and coimage of the second map meet at the middle object. -/
abbrev imageCoimageShortComplex (S : ShortComplex A) : ShortComplex A :=
  ShortComplex.mk (Abelian.image.ι S.f) (Abelian.coimage.π S.g)
    (Abelian.comp_coimage_π_eq_zero (Abelian.image_ι_comp_eq_zero S.zero))

/-- Exactness of the original pair makes the image–coimage sequence short exact. -/
lemma imageCoimageShortComplex_shortExact {S : ShortComplex A} (hS : S.Exact) :
    (imageCoimageShortComplex S).ShortExact := by
  let S' := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
  have hS' : S'.Exact := S.exact_iff_exact_image_ι.mp hS
  exact { exact := S'.exact_iff_exact_coimage_π.mp hS' }

end SerrePositivity
