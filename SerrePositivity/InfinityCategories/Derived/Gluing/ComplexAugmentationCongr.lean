module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainAugmentationHomotopy

/-! 二端・比較 cochain の厳密な照合を、複体上の明示的全 prism の厳密な照合へ移す。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (f' g' : K ⟶ L) (h' : Cochain K L (-1)) (he' : δ (-1) 0 h' = Cochain.ofHom (g' - f'))

lemma dgGluingComplexCochainAugmentationPrism_congr (hf : f = f') (hg : g = g') (hh : h = h') :
    dgGluingComplexCochainAugmentationPrism.{u, v} f g h he =
      dgGluingComplexCochainAugmentationPrism.{u, v} f' g' h' he' := by
  cases hf
  cases hg
  cases hh
  rfl

end SerrePositivity.InfinityCategories
