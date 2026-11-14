module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CochainIdentityCommaLift

/-! 実比較 cochain の後合成は、後合成した同じ二鎖写像の境界式を満たす。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L Q : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (q : L ⟶ Q)

include he in
lemma dgGluingCochainPost_boundary :
    δ (-1) 0 (h.comp (Cochain.ofHom q) (add_zero (-1))) =
      Cochain.ofHom (g ≫ q - f ≫ q) := by
  rw [δ_comp_ofHom, he, ← Cochain.ofHom_comp, Preadditive.sub_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
