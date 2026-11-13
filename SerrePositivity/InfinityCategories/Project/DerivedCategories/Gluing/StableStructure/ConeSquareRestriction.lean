module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeSquare
/-! 厳密な始域の正方形に沿い、比較ホモトピーを保持して cone 係数を制限する。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable {R : Type u} [CommRing R] {P₀ Q₀ P Q S T : Complex R}
  (f₀ : P₀ ⟶ Q₀) (f : P ⟶ Q) (g : S ⟶ T) (a : P₀ ⟶ P) (b : Q₀ ⟶ Q)
  (comm : f₀ ≫ b = a ≫ f) (μ : P ⟶ S) (ν : Q ⟶ T) (h : Cochain P T (-1))
  (hh : δ (-1) 0 h + Cochain.ofHom (μ ≫ g - f ≫ ν) = 0)

include hh comm in
lemma dgGluingConeSquareRestriction_boundary :
    δ (-1) 0 ((Cochain.ofHom a).comp h (zero_add (-1))) +
      Cochain.ofHom ((a ≫ μ) ≫ g - f₀ ≫ (b ≫ ν)) = 0 := by
  have he := congrArg (fun c : Cochain P T 0 => (Cochain.ofHom a).comp c (zero_add 0)) hh
  rw [δ_ofHom_comp, ← Category.assoc f₀ b ν, comm]
  simpa only [Cochain.comp_add, Cochain.comp_zero,
    Cochain.ofHom_sub, Cochain.comp_sub, ← Cochain.ofHom_comp,
    Category.assoc] using he

lemma dgGluingConeSquareRestriction :
    mappingCone.map f₀ f a b comm ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g μ ν h hh =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f₀ g (a ≫ μ) (b ≫ ν)
      ((Cochain.ofHom a).comp h (zero_add (-1)))
      (dgGluingConeSquareRestriction_boundary f₀ f g a b comm μ ν h hh) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from f₀ (n + 1) n rfl
  · simp only [HomologicalComplex.comp_f, mappingCone.map,
      mappingCone.inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap, mappingCone.inl_v_desc_f,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquarePrimitive, Cochain.add_v, Cochain.comp_zero_cochain_v,
      HomologicalComplex.comp_f, Preadditive.comp_add, Category.assoc]
  · simp only [HomologicalComplex.comp_f, mappingCone.map,
      mappingCone.inr_f_desc_f_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap, mappingCone.inr_f_desc_f,
      HomologicalComplex.comp_f, Category.assoc]

lemma dgGluingConeMap_target_transport {A B A' B' : Complex R}
    (x : A ⟶ B) (y y' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (comm : x ≫ b = a ≫ y) (comm' : x ≫ b = a ≫ y') (hy : y = y') :
    mappingCone.map x y a b comm ≫
      (eqToIso (congrArg (fun c : A' ⟶ B' => mappingCone c) hy)).hom =
    mappingCone.map x y' a b comm' := by
  subst y'
  simp

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
