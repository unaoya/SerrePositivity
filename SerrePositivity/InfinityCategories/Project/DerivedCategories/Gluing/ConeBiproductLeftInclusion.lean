module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeBiproduct

/-! 直和円錐の分解は、次数 −1 の左包含を両射影で保持する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (f : P ⟶ Q) (g : S ⟶ T)

/-- 分解後の左円錐への射影は、元の左射影と同じ左包含。 -/
lemma dgGluingConeBiproductIso_inl_fst :
    (mappingCone.inl (biprod.map f g)).comp
      (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso f g).hom ≫ biprod.fst))
      (add_zero (-1)) =
    (Cochain.ofHom biprod.fst).comp (mappingCone.inl f) (zero_add (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso, biprod.lift_fst]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftProjection, mappingCone.map, mappingCone.inl_desc]

/-- 分解後の右円錐への射影も、元の右射影と同じ左包含。 -/
lemma dgGluingConeBiproductIso_inl_snd :
    (mappingCone.inl (biprod.map f g)).comp
      (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso f g).hom ≫ biprod.snd))
      (add_zero (-1)) =
    (Cochain.ofHom biprod.snd).comp (mappingCone.inl g) (zero_add (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso, biprod.lift_snd]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightProjection, mappingCone.map, mappingCone.inl_desc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
