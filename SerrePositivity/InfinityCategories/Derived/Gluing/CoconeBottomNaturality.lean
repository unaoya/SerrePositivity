module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconeBottomComponents
public import SerrePositivity.InfinityCategories.Derived.ComplexMappingCoconeMapIso

/-! 標準 bottom 包含は、可換正方形に伴う同じ cocone 鎖写像と可換する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q P' Q' : Complex R}
  (d : P ⟶ Q) (d' : P' ⟶ Q') (a : P ⟶ P') (b : Q ⟶ Q')
  (comm : d ≫ b = a ≫ d')

lemma dgGluingCoconeBottomInclusion_naturality :
    dgGluingCoconeBottomInclusion d ≫ complexMappingCoconeMap d d' a b comm =
      b⟦(-1 : ℤ)⟧' ≫ dgGluingCoconeBottomInclusion d' := by
  apply dgMappingCocone_hom_ext d'
  · rw [Category.assoc, complexMappingCoconeMap_fst,
      ← Category.assoc, dgGluingCoconeBottomInclusion_fst, zero_comp,
      Category.assoc, dgGluingCoconeBottomInclusion_fst, comp_zero]
  · apply Cochain.ext
    intro n k hnk
    obtain rfl : k = n - 1 := by omega
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.comp_f]
    rw [Category.assoc, complexMappingCoconeMap_f_snd_v,
      ← Category.assoc, dgGluingCoconeBottomInclusion_snd, Category.id_comp,
      Category.assoc, dgGluingCoconeBottomInclusion_snd, Category.comp_id]
    rw [CochainComplex.shiftFunctor_map_f']
    rfl

end SerrePositivity.InfinityCategories
