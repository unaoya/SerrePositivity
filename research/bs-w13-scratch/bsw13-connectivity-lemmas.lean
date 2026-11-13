import SerrePositivity.BhattScholze.Almost.AlmostTensor

noncomputable section
universe u

namespace SerrePositivity.InfinityCategories.Derived
open CategoryTheory
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard

def IsConnectiveAt (R : Type u) [CommRing R] (n : ℤ)
    (X : (derivedInfinityCategory R) _⦋0⦌) : Prop :=
  ∀ i : ℤ, n < i → Subsingleton (derivedInfinityHomology R i X)

end SerrePositivity.InfinityCategories.Derived

namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open InfinityCategories DerivedCompletion DifferentialGraded MonoidalCategory
open Perfectoidization.Derived
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (J : Ideal R)

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

abbrev quotientTensor (M : DVertex R) : DVertex R :=
  completedModuleTensor p R
    (moduleHeartVertex R (ModuleCat.of R (QuotientPerfectoidization R J p hR))) M

theorem isConnectiveAt_iff_isLE (n : ℤ) (M : DVertex R) :
    Derived.IsConnectiveAt R n M ↔
      ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩).IsLE n := by
  rw [DerivedCategory.isLE_iff]
  exact forall_congr' (fun _ ↦ imp_congr_right (fun _ ↦ ModuleCat.isZero_iff_subsingleton.symm))

theorem isLE_moduleHeartVertex (N : ModuleCat.{u} R) :
    ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨moduleHeartVertex R N⟩).IsLE 0 := by
  let e := (moduleHeartDerivedIso R).app N
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

theorem quotientTensor_isAlmostZero (M : DVertex R) :
    IsJAlmostZero p R hR J (quotientTensor p hR J M) := by
  -- This preliminary version uses the one-sided computation of the tensor.
  let K := perfectoidKernel p R hR J
  let B := QuotientPerfectoidization R J p hR
  let q := quotientPerfdMap p R hR J
  let P := (M.obj 0).val
  let F := derivedComplexCompletionFunctor R (p : R)
  let X := DerivedCategory.Q.obj (baseChange q P)
  let iso := (derivedRestrictScalarsFactors q).app (baseChange q P) ≪≫
    DerivedCategory.Q.mapIso (restrictedBaseChangeComplexIso q P ≪≫
      cochainTensorSingleLeftIso (ModuleCat.of R B) P)
  let eB := completedModuleTensorUnresolvedIso p (ModuleCat.of R B) M ≪≫
    (F.mapIso iso).symm ≪≫ (derivedCompletionRestrictionIso q (p : R)).app X
  intro i
  let h := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso eB ≪≫
    (derivedRestrictScalarsHomologyIso q i).app _
  apply SerrePositivity.Almost.IsAlmostZero.of_equiv h.toLinearEquiv.symm
  apply SerrePositivity.Almost.IsAlmostZero.iff_smul_eq_zero.mpr
  intro r hr x
  let y : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((derivedComplexCompletionFunctor B (q (p : R))).obj X) := x
  change q r • y = 0
  rw [show q r = 0 from hr, zero_smul]

private theorem exists_quotientTensorTriangle (M : DVertex R) (hM : isPCompleteVertex p R M) :
    ∃ T : Triangle (ConcreteDerivedCategory R), T ∈ distTriang _ ∧
      Nonempty (T.obj₁ ≅ (derivedInfinityHomotopyEquivalence R).functor.obj
        ⟨kernelTensor p R hR J M⟩) ∧
      Nonempty (T.obj₂ ≅ (derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩) ∧
      Nonempty (T.obj₃ ≅ (derivedInfinityHomotopyEquivalence R).functor.obj
        ⟨quotientTensor p hR J M⟩) := by
  let K := perfectoidKernel p R hR J
  let B := QuotientPerfectoidization R J p hR
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
  let T := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  let e : (R ⧸ K) ≃ₐ[R] B :=
    { RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J) with
      commutes' := fun _ ↦ rfl }
  refine ⟨T, F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hs),
    ⟨(completedModuleTensorUnresolvedIso p (ModuleCat.of R K) M).symm⟩, ?_, ?_⟩
  · exact ⟨F.mapIso (DerivedCategory.Q.mapIso (moduleTensorCochainUnitIso P)) ≪≫
      F.mapIso (derivedVertexLocalizationIso M).symm ≪≫
        (derivedComplexCompletionUnitIso R (p : R) _ hM).symm⟩
  · exact ⟨F.mapIso (DerivedCategory.Q.mapIso
        ((moduleTensorCochainFunctor P).mapIso e.toLinearEquiv.toModuleIso)) ≪≫
      (completedModuleTensorUnresolvedIso p (ModuleCat.of R B) M).symm⟩

theorem almostConnective_of_kernelTensor_connective (M : DVertex R)
    (hM : isPCompleteVertex p R M) (hK : Derived.IsConnectiveAt R 0 (kernelTensor p R hR J M)) :
    IsAlmostConnective p R hR J M := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_quotientTensorTriangle p hR J M hM
  intro i hi
  let H := DerivedCategory.homologyFunctor (ModuleCat R) i
  have h₁ : IsZero (H.obj T.obj₁) :=
    (ModuleCat.isZero_iff_subsingleton.mpr (hK i hi)).of_iso (H.mapIso e₁)
  have hmono : Mono (H.map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).mpr
      (h₁.eq_of_src _ _)
  let f := (H.mapIso e₂).inv ≫ H.map T.mor₂ ≫ (H.mapIso e₃).hom
  have hf : Mono f := by dsimp [f]; infer_instance
  exact SerrePositivity.Almost.IsAlmostZero.of_injective f.hom
    ((ModuleCat.mono_iff_injective f).mp hf) (quotientTensor_isAlmostZero p hR J M i)

theorem connective_of_kernelTensor_and_quotientTensor (M : DVertex R)
    (hM : isPCompleteVertex p R M) (hK : Derived.IsConnectiveAt R 0 (kernelTensor p R hR J M))
    (hB : Derived.IsConnectiveAt R 0 (quotientTensor p hR J M)) :
    Derived.IsConnectiveAt R 0 M := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_quotientTensorTriangle p hR J M hM
  have h₁ := (isConnectiveAt_iff_isLE 0 _).mp hK
  have h₃ := (isConnectiveAt_iff_isLE 0 _).mp hB
  have h₁' : T.obj₁.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso e₁.symm 0
  have h₃' : T.obj₃.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso e₃.symm 0
  have h₂ := DerivedCategory.TStructure.t.isLE₂ T hT 0 h₁' h₃'
  exact (isConnectiveAt_iff_isLE 0 M).mpr
    (DerivedCategory.TStructure.t.isLE_of_iso e₂ 0)

end SerrePositivity.BhattScholze.Almost
