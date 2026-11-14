module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cylinders.CochainCylinder

/-! 元の鎖写像を二端と基底を保つ実 cochain 円柱間の鎖写像へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {K L : Complex R} (a : K ⟶ L)

lemma dgGluingCochainCylinderConeMap_condition :
    δ (-1) 0 ((Cochain.ofHom a).comp (mappingCone.inl (𝟙 L)) (zero_add (-1))) =
      Cochain.ofHom ((𝟙 K) ≫ a ≫ mappingCone.inr (𝟙 L)) := by
  rw [δ_ofHom_comp, mappingCone.δ_inl, ← Cochain.ofHom_comp]
  simp only [Category.id_comp]

def dgGluingCochainCylinderConeMap : mappingCone (𝟙 K) ⟶ mappingCone (𝟙 L) :=
  mappingCone.desc (𝟙 K)
    ((Cochain.ofHom a).comp (mappingCone.inl (𝟙 L)) (zero_add (-1)))
    (a ≫ mappingCone.inr (𝟙 L)) (dgGluingCochainCylinderConeMap_condition a)

lemma dgGluingCochainCylinderConeMap_inr :
    mappingCone.inr (𝟙 K) ≫ dgGluingCochainCylinderConeMap a = a ≫ mappingCone.inr (𝟙 L) :=
  mappingCone.inr_desc _ _ _ _

lemma dgGluingCochainCylinderConeMap_inl :
    (mappingCone.inl (𝟙 K)).comp (Cochain.ofHom (dgGluingCochainCylinderConeMap a))
        (add_zero (-1)) =
      (Cochain.ofHom a).comp (mappingCone.inl (𝟙 L)) (zero_add (-1)) :=
  mappingCone.inl_desc _ _ _ _

def dgGluingCochainCylinderMap : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinder K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinder L :=
  biprod.map a (dgGluingCochainCylinderConeMap a)

lemma dgGluingCochainCylinderMap_projection :
    dgGluingCochainCylinderMap a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection K ≫ a := by
  exact biprod.map_fst _ _

lemma dgGluingCochainCylinderMap_zero :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderZero K ≫ dgGluingCochainCylinderMap a =
      a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderZero L := by
  exact biprod.inl_map _ _

lemma dgGluingCochainCylinderMap_one :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne K ≫ dgGluingCochainCylinderMap a =
      a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne L := by
  apply biprod.hom_ext
  · simp only [Category.assoc, dgGluingCochainCylinderMap, biprod.map_fst]
    simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne, biprod.lift_fst,
      Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, dgGluingCochainCylinderMap, biprod.map_snd]
    simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne, biprod.lift_snd]
    exact dgGluingCochainCylinderConeMap_inr a

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
