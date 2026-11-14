module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeSquare
/-! cone 係数の負号と、同じ複体間の鎖写像の等式による両端の移送。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (f : P ⟶ Q) (g : S ⟶ T) (μ : P ⟶ S) (ν : Q ⟶ T) (h : Cochain P T (-1))
  (hh : δ (-1) 0 h + Cochain.ofHom (μ ≫ g - f ≫ ν) = 0)

include hh in
lemma dgGluingConeSquareNeg_boundary : δ (-1) 0 (-h) + Cochain.ofHom ((-μ) ≫ g - f ≫ (-ν)) = 0 := by
  rw [δ_neg, eq_neg_of_add_eq_zero_left hh, neg_neg]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, sub_neg_eq_add,
    Cochain.ofHom_sub, Cochain.ofHom_add, Cochain.ofHom_neg]
  abel

lemma dgGluingConeSquareMap_neg (hn : δ (-1) 0 (-h) + Cochain.ofHom ((-μ) ≫ g - f ≫ (-ν)) = 0) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g (-μ) (-ν) (-h) hn = -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g μ ν h hh := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from f (n + 1) n rfl
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap, HomologicalComplex.neg_f_apply,
      Preadditive.comp_neg, mappingCone.inl_v_desc_f,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquarePrimitive, Cochain.add_v, Cochain.zero_cochain_comp_v,
      Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.neg_v,
      HomologicalComplex.neg_f_apply, Preadditive.neg_comp]
    abel
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap, HomologicalComplex.neg_f_apply,
      Preadditive.comp_neg, mappingCone.inr_f_desc_f, HomologicalComplex.comp_f,
      HomologicalComplex.neg_f_apply, Preadditive.neg_comp]

lemma dgGluingConeSquareMap_congr (f' : P ⟶ Q) (g' : S ⟶ T) (μ' : P ⟶ S) (ν' : Q ⟶ T)
    (h' : Cochain P T (-1))
    (hh' : δ (-1) 0 h' + Cochain.ofHom (μ' ≫ g' - f' ≫ ν') = 0)
    (hf : f = f') (hg : g = g') (hμ : μ = μ') (hν : ν = ν') (he : h = h') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g μ ν h hh ≫
      (eqToIso (congrArg (fun a : S ⟶ T => mappingCone a) hg)).hom =
    (eqToIso (congrArg (fun a : P ⟶ Q => mappingCone a) hf)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f' g' μ' ν' h' hh' := by
  subst f'
  subst g'
  subst μ'
  subst ν'
  subst h'
  simp

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
