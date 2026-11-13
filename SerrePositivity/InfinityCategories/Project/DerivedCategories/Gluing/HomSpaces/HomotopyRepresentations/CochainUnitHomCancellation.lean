module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.ComplexPinchedUnitModel

/-! 複体の単位 Hom への移送とその逆は、全次数の元・全比較 cochain を厳密に回収する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex HomologicalComplex
variable {R : Type u} [CommRing R]

lemma dgGluingComplexUnitHom_inv_apply (L : Complex R) (k : ℤ) (a : L.X k) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).inv.f k ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom.f k a) = a :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom_inv_id k) a

lemma dgGluingCochainUnitHom_cancel {K L : Complex R} (h : Cochain K L (-1)) :
    (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1))).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).inv) (add_zero (-1)) = h := by
  rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, Iso.hom_inv_id]
  exact Cochain.comp_id h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
