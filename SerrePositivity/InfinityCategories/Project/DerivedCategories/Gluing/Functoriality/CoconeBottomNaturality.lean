module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ConeComparisons.CoconeBottomComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMapIso

/-! 標準 bottom 包含は、可換正方形に伴う同じ cocone 鎖写像と可換する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q P' Q' : Complex R}
  (d : P ⟶ Q) (d' : P' ⟶ Q') (a : P ⟶ P') (b : Q ⟶ Q')
  (comm : d ≫ b = a ≫ d')

lemma dgGluingCoconeBottomInclusion_naturality :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion d ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d d' a b comm =
      b⟦(-1 : ℤ)⟧' ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion d' := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext d'
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion_fst, zero_comp,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion_fst, comp_zero]
  · apply Cochain.ext
    intro n k hnk
    obtain rfl : k = n - 1 := by omega
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.comp_f]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_snd_v,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion_snd, Category.id_comp,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion_snd, Category.comp_id]
    rw [CochainComplex.shiftFunctor_map_f']
    rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
