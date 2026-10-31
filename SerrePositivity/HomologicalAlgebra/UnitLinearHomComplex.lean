module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-! # Evaluating linear cochains from the unit complex at one -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory HomologicalComplex CochainComplex.HomComplex
variable {R : Type u} [CommRing R]

/-- A cochain from R[0] is determined linearly by the image of one. -/
def unitHomCochainEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain (cochainTensorUnit (R := R)) K n ≃ₗ[R] K.X n :=
  (Cochain.fromSingleLinearEquiv (R := R) (zero_add n)).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R (K.X n)))

/-- Evaluation agrees with the specified single-cochain constructor. -/
theorem unitHomCochainEquiv_fromSingleMk
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (f : ModuleCat.of R R ⟶ K.X n) :
    unitHomCochainEquiv K n (Cochain.fromSingleMk f (zero_add n)) = f.hom 1 := by
  simp [unitHomCochainEquiv, Cochain.fromSingleLinearEquiv,
    Cochain.fromSingleEquiv_fromSingleMk]
  rfl

/-- The Hom differential is exactly the original differential under evaluation. -/
theorem unitHomCochainEquiv_d
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ)
    (α : Cochain (cochainTensorUnit (R := R)) K i) :
    unitHomCochainEquiv K j (δ i j α) =
      (K.d i j).hom (unitHomCochainEquiv K i α) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective α i (zero_add i)
  rw [Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j),
    unitHomCochainEquiv_fromSingleMk, unitHomCochainEquiv_fromSingleMk]
  rfl

/-- The actual linear Hom complex from the unit is naturally the original complex. -/
def unitLinearHomComplexIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex.linearHomComplex R (cochainTensorUnit (R := R)) K ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (unitHomCochainEquiv K n).toModuleIso)
    (fun i j _ ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro α
      exact (unitHomCochainEquiv_d K i j α).symm)

/-- Evaluation commutes with genuine postcomposition of cochains. -/
theorem unitHomCochainEquiv_postcomp
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℤ)
    (α : Cochain (cochainTensorUnit (R := R)) K n) :
    unitHomCochainEquiv L n (α.comp (Cochain.ofHom f) (add_zero n)) =
      (f.f n).hom (unitHomCochainEquiv K n α) := by
  obtain ⟨g, rfl⟩ := Cochain.fromSingleMk_surjective α n (zero_add n)
  rw [← Cochain.fromSingleMk_postcomp, unitHomCochainEquiv_fromSingleMk,
    unitHomCochainEquiv_fromSingleMk]
  rfl

/-- Actual postcomposition on linear Hom complexes from the unit. -/
def unitLinearHomMap {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    CochainComplex.linearHomComplex R (cochainTensorUnit (R := R)) K ⟶
      CochainComplex.linearHomComplex R (cochainTensorUnit (R := R)) L where
  f n := ModuleCat.ofHom
    { toFun := fun α ↦ α.comp (Cochain.ofHom f) (add_zero n)
      map_add' := fun α β ↦ Cochain.add_comp α β _ _
      map_smul' := fun r α ↦ Cochain.smul_comp r α _ _ }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact δ_comp_ofHom α f j

/-- The complex isomorphism is natural for the actual postcomposition maps. -/
theorem unitLinearHomComplexIso_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    unitLinearHomMap f ≫ (unitLinearHomComplexIso L).hom =
      (unitLinearHomComplexIso K).hom ≫ f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact unitHomCochainEquiv_postcomp f n α

/-- Evaluation induces a linear comparison on actual cohomology in every integer degree. -/
def unitLinearHomHomologyIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (CochainComplex.linearHomComplex R (cochainTensorUnit (R := R)) K).homology n ≅
      K.homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n).mapIso
    (unitLinearHomComplexIso K)

/-- The cohomology comparison respects the actual homology maps. -/
theorem unitLinearHomHomologyIso_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℤ) :
    homologyMap (unitLinearHomMap f) n ≫ (unitLinearHomHomologyIso L n).hom =
      (unitLinearHomHomologyIso K n).hom ≫ homologyMap f n := by
  change (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n).map
      (unitLinearHomMap f) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n).map
        (unitLinearHomComplexIso L).hom =
    (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n).map
      (unitLinearHomComplexIso K).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n).map f
  rw [← Functor.map_comp, ← Functor.map_comp, unitLinearHomComplexIso_naturality]

end SerrePositivity
