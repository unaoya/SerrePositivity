module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMapIso

/-! 同じ mapping cocone を、恒等写像の cocone を経由する path 引き戻しとして表示する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q K : Complex R} (d : P ⟶ Q)

def dgGluingCoconePathMap : mappingCocone d ⟶ mappingCocone (𝟙 Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d (𝟙 Q) d (𝟙 Q) rfl

lemma dgGluingCoconePathMap_fst :
    dgGluingCoconePathMap d ≫ mappingCocone.fst (𝟙 Q) = mappingCocone.fst d ≫ d :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst _ _ _ _ _

lemma dgGluingCoconePathMap_snd :
    (Cochain.ofHom (dgGluingCoconePathMap d)).comp
      (mappingCocone.snd (𝟙 Q)) (zero_add (-1)) = mappingCocone.snd d := by
  rw [dgGluingCoconePathMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd]
  apply Cochain.ext
  intro n k hnk
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.comp_id]

lemma dgGluingCoconePathLift_boundary (f : K ⟶ mappingCocone (𝟙 Q)) (g : K ⟶ P)
    (h : f ≫ mappingCocone.fst (𝟙 Q) = g ≫ d) :
    δ (-1) 0 ((Cochain.ofHom f).comp (mappingCocone.snd (𝟙 Q)) (zero_add (-1))) +
      Cochain.ofHom (g ≫ d) = 0 := by
  rw [δ_ofHom_comp, ← h]
  have hb := congrArg (fun k : Cochain (mappingCocone (𝟙 Q)) Q 0 =>
    (Cochain.ofHom f).comp k (zero_add 0)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary (𝟙 Q))
  simpa only [Cochain.comp_add, Cochain.comp_zero, ← Cochain.ofHom_comp,
    Category.comp_id] using hb

def dgGluingCoconePathLift (f : K ⟶ mappingCocone (𝟙 Q)) (g : K ⟶ P)
    (h : f ≫ mappingCocone.fst (𝟙 Q) = g ≫ d) : K ⟶ mappingCocone d :=
  mappingCocone.lift d g
    ((Cochain.ofHom f).comp (mappingCocone.snd (𝟙 Q)) (zero_add (-1)))
    (dgGluingCoconePathLift_boundary d f g h)

lemma dgGluingCoconePathLift_fst (f : K ⟶ mappingCocone (𝟙 Q)) (g : K ⟶ P)
    (h : f ≫ mappingCocone.fst (𝟙 Q) = g ≫ d) :
    dgGluingCoconePathLift d f g h ≫ mappingCocone.fst d = g :=
  mappingCocone.lift_fst _ _ _ _

lemma dgGluingCoconePathLift_snd (f : K ⟶ mappingCocone (𝟙 Q)) (g : K ⟶ P)
    (h : f ≫ mappingCocone.fst (𝟙 Q) = g ≫ d) :
    (Cochain.ofHom (dgGluingCoconePathLift d f g h)).comp
      (mappingCocone.snd d) (zero_add (-1)) =
    (Cochain.ofHom f).comp (mappingCocone.snd (𝟙 Q)) (zero_add (-1)) := by
  apply Cochain.ext
  intro n k hnk
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  simpa only [dgGluingCoconePathLift, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    mappingCocone.lift_f_snd_v d g
      ((Cochain.ofHom f).comp (mappingCocone.snd (𝟙 Q)) (zero_add (-1)))
      (dgGluingCoconePathLift_boundary d f g h) n k hnk

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
