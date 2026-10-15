module
public import SerrePositivity.HomologicalAlgebra.CochainLinearDual

/-! # Linear dual coordinates of mapping cones and their signed differential -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- Morphisms from a cone term are pairs of morphisms from its two summands. -/
def mappingConeTargetHomEquiv (M : ModuleCat.{u} R) (q : ℤ) :
    (((CochainComplex.mappingCone φ).X q) ⟶ M) ≃ₗ[R]
      ((K.X (q + 1) ⟶ M) × (L.X q ⟶ M)) where
  toFun f := ⟨inlX φ (q + 1) q rfl ≫ f, inrX φ q ≫ f⟩
  invFun f := fstX φ q (q + 1) rfl ≫ f.1 + sndX φ q ≫ f.2
  left_inv f := by
    apply ext_from_X φ (q + 1) q rfl <;> simp
  right_inv f := by simp
  map_add' f g := by simp [Preadditive.comp_add]
  map_smul' a f := by simp [Linear.comp_smul]

/-- The first dual component is restriction to the shifted source summand. -/
@[simp] lemma mappingConeTargetHomEquiv_fst (M : ModuleCat.{u} R) (q : ℤ)
    (f : ((CochainComplex.mappingCone φ).X q) ⟶ M) :
    (mappingConeTargetHomEquiv φ M q f).1 = inlX φ (q + 1) q rfl ≫ f := rfl

/-- The second dual component is restriction to the target summand. -/
@[simp] lemma mappingConeTargetHomEquiv_snd (M : ModuleCat.{u} R) (q : ℤ)
    (f : ((CochainComplex.mappingCone φ).X q) ⟶ M) :
    (mappingConeTargetHomEquiv φ M q f).2 = inrX φ q ≫ f := rfl

/-- Dual cone coordinates are natural under arbitrary coefficient morphisms. -/
lemma mappingConeTargetHomEquiv_coefficient_map {M N : ModuleCat.{u} R}
    (q : ℤ) (f : ((CochainComplex.mappingCone φ).X q) ⟶ M) (g : M ⟶ N) :
    mappingConeTargetHomEquiv φ N q (f ≫ g) =
      ((mappingConeTargetHomEquiv φ M q f).1 ≫ g,
        (mappingConeTargetHomEquiv φ M q f).2 ≫ g) := by
  exact Prod.ext (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- Precomposition by the cone differential has a negative source component and a cross term. -/
lemma mappingConeTargetHomEquiv_d_fst (M : ModuleCat.{u} R) (q : ℤ)
    (f : ((CochainComplex.mappingCone φ).X (q + 1)) ⟶ M) :
    (mappingConeTargetHomEquiv φ M q
        ((CochainComplex.mappingCone φ).d q (q + 1) ≫ f)).1 =
      -(K.d (q + 1) (q + 1 + 1) ≫ (mappingConeTargetHomEquiv φ M (q + 1) f).1) +
        φ.f (q + 1) ≫ (mappingConeTargetHomEquiv φ M (q + 1) f).2 := by
  simp only [mappingConeTargetHomEquiv_fst, mappingConeTargetHomEquiv_snd]
  rw [← Category.assoc]
  change (inlX φ (q + 1) q rfl ≫ homotopyCofiber.d φ q (q + 1)) ≫ f = _
  rw [inlX_d φ q (q + 1) (q + 1 + 1) rfl rfl]
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc]

/-- The second dual component is precomposition by the old target differential. -/
lemma mappingConeTargetHomEquiv_d_snd (M : ModuleCat.{u} R) (q : ℤ)
    (f : ((CochainComplex.mappingCone φ).X (q + 1)) ⟶ M) :
    (mappingConeTargetHomEquiv φ M q
        ((CochainComplex.mappingCone φ).d q (q + 1) ≫ f)).2 =
      L.d q (q + 1) ≫ (mappingConeTargetHomEquiv φ M (q + 1) f).2 := by
  simp only [mappingConeTargetHomEquiv_snd]
  rw [← Category.assoc]
  change (inrX φ q ≫ homotopyCofiber.d φ q (q + 1)) ≫ f = _
  rw [inrX_d, Category.assoc]

/-- The same coordinates on the actual integer-indexed dual cone used in the induction. -/
abbrev mappingConeLinearDualTermEquiv (M : ModuleCat.{u} R) (i : ℤ) :
    ((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M).X i ≃ₗ[R]
      ((K.X (0 - i + 1) ⟶ M) × (L.X (0 - i) ⟶ M)) :=
  mappingConeTargetHomEquiv φ M (0 - i)

/-- Actual dual coefficient maps act componentwise in these coordinates. -/
lemma mappingConeLinearDualTermEquiv_coefficient_map {M N : ModuleCat.{u} R}
    (i : ℤ) (f : M ⟶ N)
    (g : ((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M).X i) :
    mappingConeLinearDualTermEquiv φ N i
        ((((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).map f).f i).hom g) =
      ((mappingConeLinearDualTermEquiv φ M i g).1 ≫ f,
        (mappingConeLinearDualTermEquiv φ M i g).2 ≫ f) :=
  mappingConeTargetHomEquiv_coefficient_map φ (0 - i) g f

/-- For a scalar cone, the cross term is precisely multiplication by the scalar. -/
lemma scalarMappingConeTargetHomEquiv_d_fst (a : R) (M : ModuleCat.{u} R) (q : ℤ)
    (f : ((CochainComplex.mappingCone (a • 𝟙 K)).X (q + 1)) ⟶ M) :
    (mappingConeTargetHomEquiv (a • 𝟙 K) M q
        ((CochainComplex.mappingCone (a • 𝟙 K)).d q (q + 1) ≫ f)).1 =
      -(K.d (q + 1) (q + 1 + 1) ≫
        (mappingConeTargetHomEquiv (a • 𝟙 K) M (q + 1) f).1) +
      a • (mappingConeTargetHomEquiv (a • 𝟙 K) M (q + 1) f).2 := by
  rw [mappingConeTargetHomEquiv_d_fst]
  simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    Linear.smul_comp, Category.id_comp]

end SerrePositivity
