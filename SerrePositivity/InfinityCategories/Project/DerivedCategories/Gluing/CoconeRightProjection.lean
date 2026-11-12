module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeBiprodQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeMapIso

/-! 直和の第一成分が擬同型であるとき、同じ mapping cocone の右射影も擬同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q T : Complex R}

lemma dgGluingCoconeRightProjection_quasiIso
    (d : P ⊞ Q ⟶ T) (a : P ⟶ T) (b : Q ⟶ T)
    (hd : d = biprod.desc a b) (ha : QuasiIso a) :
    QuasiIso (mappingCocone.fst d ≫ (biprod.snd : P ⊞ Q ⟶ Q)) := by
  let d' := biprod.desc b a
  let s := biprod.braiding Q P
  have hs : d' ≫ (Iso.refl T).hom = s.hom ≫ d := by
    rw [hd]
    apply biprod.hom_ext'
    · simp [d', s, biprod.braiding]
    · simp [d', s, biprod.braiding]
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso d' d s (Iso.refl T) hs
  have hp : QuasiIso
      (mappingCocone.fst d' ≫ (biprod.fst : Q ⊞ P ⟶ Q)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeProjection_quasiIso_of_eq d' b a rfl ha
  have he : e.hom ≫ (mappingCocone.fst d ≫ (biprod.snd : P ⊞ Q ⟶ Q)) =
      mappingCocone.fst d' ≫ (biprod.fst : Q ⊞ P ⟶ Q) := by
    change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d' d s.hom (Iso.refl T).hom hs ≫
      (mappingCocone.fst d ≫ biprod.snd) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, Category.assoc]
    simp only [s, biprod.braiding_hom, biprod.lift_snd]
  apply (quasiIso_iff_comp_left e.hom _).1
  rw [he]
  exact hp

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
