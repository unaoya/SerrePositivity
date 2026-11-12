module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainAugmentationHomotopy

/-! 同じ二鎖写像と比較 cochain の表示替えは、元 augmentation の全区間族を変えない。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E] (x y : E)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (f' g' : K ⟶ homObject R E x y) (h' : Cochain K (homObject R E x y) (-1))
  (he' : δ (-1) 0 h' = Cochain.ofHom (g' - f'))

lemma dgGluingCochainAugmentationPrism_congr (hf : f = f') (hg : g = g') (hh : h = h') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism R E x y K f g h he =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism R E x y K f' g' h' he' := by
  cases hf
  cases hg
  cases hh
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
