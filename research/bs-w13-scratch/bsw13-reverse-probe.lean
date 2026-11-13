import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
import SerrePositivity.DifferentialGraded.Tensor.Graded
import SerrePositivity.InfinityCategories.Derived.SemifreeBasisEquivalence
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion

noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open InfinityCategories DerivedCompletion DifferentialGraded MonoidalCategory
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

private theorem complexSemifree_kFlat {P : Complex R} (hP : complexSemifree R P) :
    complexKFlat R P :=
  moduleSemifree_objectwiseKFlat R PUnit.{1} (fun _ _ ↦ complexKFlat_unit R) hP PUnit.unit

private def completedModuleTensorUnresolvedIso (p : ℕ) (N : ModuleCat.{u} R) (M : DVertex R) :
    ((derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨completedModuleTensor p R (moduleHeartVertex R N) M⟩) ≅
    (derivedComplexCompletionFunctor R (p : R)).obj
      (DerivedCategory.Q.obj ((moduleTensorCochainFunctor (M.obj 0).val).obj N)) := by
  let P := (M.obj 0).val
  let e := derivedInfinityHomotopyEquivalence R
  have := moduleFreeCochainAugmentation_quasiIso R N
  have := complexKFlat_quasiIso_left R (complexSemifree_kFlat (M.obj 0).property)
    (moduleFreeCochainAugmentation R N)
  exact e.counitIso.app _ ≪≫ (derivedComplexCompletionFunctor R (p : R)).mapIso
    (asIso (DerivedCategory.Q.map (cochainTensorMap (moduleFreeCochainAugmentation R N) (𝟙 P))) ≪≫
      DerivedCategory.Q.mapIso (cochainTensorSingleLeftIso N P))

theorem isAlmostZero_of_completedTensor_isZero (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (J : Ideal R) (M : DVertex R)
    (hM : IsComplete R (p : R) ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩))
    (hz : IsZero ((derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨completedModuleTensor p R (moduleHeartVertex R (ModuleCat.of R (perfectoidKernel p R hR J))) M⟩)) :
    IsJAlmostZero p R hR J M := by
  let K := perfectoidKernel p R hR J
  let q := Ideal.Quotient.mk K
  let P := (M.obj 0).val
  let F := derivedComplexCompletionFunctor R (p : R)
  let S := ModuleCat.shortComplexOfCompEqZero K.subtype K.mkQ
    (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ K) K.injective_subtype K.mkQ_surjective
  obtain ⟨basis⟩ := complexSemifree_nonempty_basis (M.obj 0).property
  have hflat (i : ℤ) : Module.Flat R (P.X i) := by
    let := Module.Free.of_basis (basis.basis i)
    infer_instance
  have hs := moduleTensorCochain_shortExact P hflat S hS
  let triangle := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  have hd : triangle ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hs)
  have hz' : IsZero triangle.obj₁ :=
    hz.of_iso (completedModuleTensorUnresolvedIso p (ModuleCat.of R K) M).symm
  have : IsIso triangle.mor₂ := (triangle.isZero₁_iff_isIso₂ hd).mp hz'
  let eR := F.mapIso (DerivedCategory.Q.mapIso (moduleTensorCochainUnitIso P)) ≪≫
    F.mapIso (derivedVertexLocalizationIso M).symm ≪≫
      (derivedComplexCompletionUnitIso R (p : R) _ hM).symm
  let B := R ⧸ K
  let X := DerivedCategory.Q.obj (baseChange q P)
  let iso := (derivedRestrictScalarsFactors q).app (baseChange q P) ≪≫
    DerivedCategory.Q.mapIso (restrictedBaseChangeComplexIso q P ≪≫
      cochainTensorSingleLeftIso (ModuleCat.of R B) P)
  let eB := (F.mapIso iso).symm ≪≫ (derivedCompletionRestrictionIso q (p : R)).app X
  let e := eR.symm ≪≫ asIso triangle.mor₂ ≪≫ eB
  intro i
  let h := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e ≪≫
    (derivedRestrictScalarsHomologyIso q i).app _
  apply SerrePositivity.Almost.IsAlmostZero.of_equiv h.toLinearEquiv.symm
  apply SerrePositivity.Almost.IsAlmostZero.iff_smul_eq_zero.mpr
  intro r hr x
  let y : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((derivedComplexCompletionFunctor B (q (p : R))).obj X) := x
  change (Ideal.Quotient.mk K r) • y = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

#print axioms isAlmostZero_of_completedTensor_isZero

end SerrePositivity.BhattScholze.Almost
