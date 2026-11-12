module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconeBottomInclusion

/-! 標準 bottom 包含の二成分：上への射影は零、同じ第三成分は恒等。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q : Complex R} (d : P ⟶ Q)

lemma dgGluingCoconeBottomInclusion_f (n : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion d).f n =
      (mappingCocone.inr d).val.v (n - 1) n (by omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion, CochainComplex.shiftFunctor_map_f']
  simp only [mappingCocone.inr, Cocycle.rightShift_coe, Cocycle.ofHom_coe]
  rw [Cochain.rightShift_v _ (-1) 1 (by omega) (n - 1) n (by omega)
    (n - 1) (add_zero _)]
  simp only [Cochain.ofHom_v, shiftFunctorObjXIso, XIsoOfEq_rfl,
    Iso.refl_inv]
  change (mappingCone.inr d).f (n - 1) =
    (mappingCone.inr d).f (n - 1) ≫ 𝟙 _
  rw [Category.comp_id]

lemma dgGluingCoconeBottomInclusion_fst :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion d ≫ mappingCocone.fst d = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f, dgGluingCoconeBottomInclusion_f]
  exact mappingCocone.inr_v_fst_f d (n - 1) n (by omega)

lemma dgGluingCoconeBottomInclusion_snd (n : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion d).f n ≫
      (mappingCocone.snd d).v n (n - 1) (by omega) = 𝟙 _ := by
  rw [dgGluingCoconeBottomInclusion_f]
  exact mappingCocone.inr_v_snd_v d (n - 1) n (by omega)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
