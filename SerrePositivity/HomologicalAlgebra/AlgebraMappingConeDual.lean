module
public import SerrePositivity.HomologicalAlgebra.AlgebraLinearYoneda
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplex
public import SerrePositivity.HomologicalAlgebra.CochainConeCoordinates
public import SerrePositivity.HomologicalAlgebra.CochainConeNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulTower

/-! # Actual coefficient-algebra linear coordinates on dual mapping cones -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {K L K' L' : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The dual of a cone term splits over the actual coefficient algebra, without
requiring a C-linear structure on the category of all R-modules. -/
def algebraMappingConeTargetHomEquiv (φ : K ⟶ L) (M : ModuleCat.{u} C) (q : ℤ) :
    (((CochainComplex.mappingCone φ).X q) ⟶
        (ModuleCat.restrictScalars (algebraMap R C)).obj M) ≃ₗ[C]
      ((K.X (q + 1) ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj M) ×
        (L.X q ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj M)) where
  toFun f := ⟨inlX φ (q + 1) q rfl ≫ f, inrX φ q ≫ f⟩
  invFun f := fstX φ q (q + 1) rfl ≫ f.1 + sndX φ q ≫ f.2
  left_inv f := by
    apply ext_from_X φ (q + 1) q rfl <;> simp
  right_inv f := by simp
  map_add' f g := by simp [Preadditive.comp_add]
  map_smul' c f := by
    apply Prod.ext <;> apply ModuleCat.hom_ext <;> apply LinearMap.ext <;> intro x <;> rfl

/-- Cone dual coordinates retain naturality for arbitrary C-linear coefficient maps. -/
lemma algebraMappingConeTargetHomEquiv_coefficient_map (φ : K ⟶ L)
    {M N : ModuleCat.{u} C} (q : ℤ) (f : (CochainComplex.mappingCone φ).X q ⟶
      (ModuleCat.restrictScalars (algebraMap R C)).obj M) (g : M ⟶ N) :
    algebraMappingConeTargetHomEquiv φ N q
        (f ≫ (ModuleCat.restrictScalars (algebraMap R C)).map g) =
      ((algebraMappingConeTargetHomEquiv φ M q f).1 ≫
          (ModuleCat.restrictScalars (algebraMap R C)).map g,
        (algebraMappingConeTargetHomEquiv φ M q f).2 ≫
          (ModuleCat.restrictScalars (algebraMap R C)).map g) :=
  Prod.ext (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- An actual cone map acts on the first dual component by precomposition with its left map. -/
lemma algebraMappingConeTargetHomEquiv_map_fst (φ : K ⟶ L) (ψ : K' ⟶ L')
    (α : Arrow.mk φ ⟶ Arrow.mk ψ) (M : ModuleCat.{u} C) (q : ℤ)
    (f : (CochainComplex.mappingCone ψ).X q ⟶
      (ModuleCat.restrictScalars (algebraMap R C)).obj M) :
    (algebraMappingConeTargetHomEquiv φ M q
        ((mapArrowHom φ ψ (fun k => ⟨k - 1, by simp⟩) α).f q ≫ f)).1 =
      α.left.f (q + 1) ≫ (algebraMappingConeTargetHomEquiv ψ M q f).1 := by
  change inlX φ (q + 1) q rfl ≫ _ ≫ f = _
  rw [← Category.assoc, DerivedCompletion.moduleConeArrowMap_inl, Category.assoc]
  rfl

/-- The second dual component is precomposition with the right map. -/
lemma algebraMappingConeTargetHomEquiv_map_snd (φ : K ⟶ L) (ψ : K' ⟶ L')
    (α : Arrow.mk φ ⟶ Arrow.mk ψ) (M : ModuleCat.{u} C) (q : ℤ)
    (f : (CochainComplex.mappingCone ψ).X q ⟶
      (ModuleCat.restrictScalars (algebraMap R C)).obj M) :
    (algebraMappingConeTargetHomEquiv φ M q
        ((mapArrowHom φ ψ (fun k => ⟨k - 1, by simp⟩) α).f q ≫ f)).2 =
      α.right.f q ≫ (algebraMappingConeTargetHomEquiv ψ M q f).2 := by
  change inrX φ q ≫ _ ≫ f = _
  rw [← Category.assoc, DerivedCompletion.moduleConeArrowMap_inr, Category.assoc]
  rfl

/-- A scalar factor in the left cone map becomes its image in the coefficient algebra
on the actual first dual summand. This identifies the weight in power transitions. -/
lemma algebraMappingConeTargetHomEquiv_map_fst_of_smul
    (φ : K ⟶ L) (ψ : K' ⟶ L') (α : Arrow.mk φ ⟶ Arrow.mk ψ)
    (g : K ⟶ K') (c : R) (hleft : α.left = c • g)
    (M : ModuleCat.{u} C) (q : ℤ)
    (f : (CochainComplex.mappingCone ψ).X q ⟶
      (ModuleCat.restrictScalars (algebraMap R C)).obj M) :
    (algebraMappingConeTargetHomEquiv φ M q
        ((mapArrowHom φ ψ (fun k => ⟨k - 1, by simp⟩) α).f q ≫ f)).1 =
      algebraMap R C c • (g.f (q + 1) ≫
        (algebraMappingConeTargetHomEquiv ψ M q f).1) := by
  rw [algebraMappingConeTargetHomEquiv_map_fst, hleft]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ((algebraMappingConeTargetHomEquiv ψ M q f).1).hom.map_smul c (g.f (q + 1) x)

/-- The actual power Koszul dual terms split into the shifted and unshifted old terms. -/
def algebraKoszulPowerConeHomEquiv {e : ℕ} (z : Fin (e + 1) → R)
    (M : ModuleCat.{u} C) (n : ℕ) (q : ℤ) :
    ((DerivedCompletion.powerKoszulTower R z n).X q ⟶
        (ModuleCat.restrictScalars (algebraMap R C)).obj M) ≃ₗ[C]
      (((DerivedCompletion.powerKoszulTower R (Fin.init z) n).X (q + 1) ⟶
          (ModuleCat.restrictScalars (algebraMap R C)).obj M) ×
        ((DerivedCompletion.powerKoszulTower R (Fin.init z) n).X q ⟶
          (ModuleCat.restrictScalars (algebraMap R C)).obj M)) :=
  algebraMappingConeTargetHomEquiv
    (smulId (z (Fin.last e) ^ n)
      (DerivedCompletion.powerKoszulTower R (Fin.init z) n)) M q

/-- In the actual dual power transition, the shifted summand carries the new coordinate weight. -/
lemma algebraKoszulPowerConeHomEquiv_transition_fst {e : ℕ} (z : Fin (e + 1) → R)
    (M : ModuleCat.{u} C) (n : ℕ) (q : ℤ)
    (f : (DerivedCompletion.powerKoszulTower R z n).X q ⟶
      (ModuleCat.restrictScalars (algebraMap R C)).obj M) :
    (algebraKoszulPowerConeHomEquiv z M (n + 1) q
        ((DerivedCompletion.powerKoszulTransition R z n).f q ≫ f)).1 =
      algebraMap R C (z (Fin.last e)) •
        ((DerivedCompletion.powerKoszulTransition R (Fin.init z) n).f (q + 1) ≫
          (algebraKoszulPowerConeHomEquiv z M n q f).1) := by
  dsimp only [algebraKoszulPowerConeHomEquiv, DerivedCompletion.powerKoszulTransition,
    DerivedCompletion.koszulComplexMapOfMul]
  apply algebraMappingConeTargetHomEquiv_map_fst_of_smul
  rfl

/-- The unshifted summand carries the previous power transition without the new weight. -/
lemma algebraKoszulPowerConeHomEquiv_transition_snd {e : ℕ} (z : Fin (e + 1) → R)
    (M : ModuleCat.{u} C) (n : ℕ) (q : ℤ)
    (f : (DerivedCompletion.powerKoszulTower R z n).X q ⟶
      (ModuleCat.restrictScalars (algebraMap R C)).obj M) :
    (algebraKoszulPowerConeHomEquiv z M (n + 1) q
        ((DerivedCompletion.powerKoszulTransition R z n).f q ≫ f)).2 =
      (DerivedCompletion.powerKoszulTransition R (Fin.init z) n).f q ≫
        (algebraKoszulPowerConeHomEquiv z M n q f).2 := by
  dsimp only [algebraKoszulPowerConeHomEquiv, DerivedCompletion.powerKoszulTransition,
    DerivedCompletion.koszulComplexMapOfMul]
  exact algebraMappingConeTargetHomEquiv_map_snd _ _ _ M q f

end SerrePositivity
