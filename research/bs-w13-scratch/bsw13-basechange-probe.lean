import SerrePositivity.BhattScholze.Almost.AlmostTensorForward
import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAcyclic
import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensorComparison
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.RingTheory.TensorProduct.Quotient

noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open InfinityCategories DerivedCompletion MonoidalCategory
open scoped Simplicial TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (R : Type u) [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']

def completeModuleBaseChange (X : DVertex R) : DVertex R' :=
  let F := (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (.up ℤ)
  let Y := (derivedComplexCompletionFunctor R' (p : R')).obj
    (DerivedCategory.Q.obj (F.obj (X.obj 0).val))
  ((derivedInfinityHomotopyEquivalence R').inverse.obj Y).pt

def completeBaseChangeH0 : ModuleCat.{u} R ⥤ ModuleCat.{u} R' :=
  moduleFreeCochainResolution R ⋙ (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⋙ derivedComplexCompletionFunctor R' (p : R') ⋙
    DerivedCategory.homologyFunctor (ModuleCat R') 0

private def completeBaseChangeH0ModelIso :
    boundedAboveDerivedSingleFunctor (R := R) ⋙ boundedAboveDerivedBaseChange (algebraMap R R') ⋙
      DerivedCategory.Minus.ι ⋙
        derivedComplexCompletionFunctor R' (algebraMap R R' (p : R)) ⋙
        DerivedCategory.homologyFunctor (ModuleCat R') 0 ≅
      completeBaseChangeH0 p R (R' := R') := by
  rw [map_natCast]
  let F := ModuleCat.extendScalars (algebraMap R R')
  let C := derivedComplexCompletionFunctor R' (p : R')
  let H := DerivedCategory.homologyFunctor (ModuleCat R') 0
  refine NatIso.ofComponents (fun M ↦ (C ⋙ H).mapIso
    (boundedAboveDerivedBaseChangeModelIso (algebraMap R R') _
      (moduleHeartProjectiveModel R M))) ?_
  intro M N f
  have h :
      DerivedCategory.Q.map ((moduleFreeCochainResolution R).map f) ≫
          (moduleHeartProjectiveModel R N).iso.hom =
        (moduleHeartProjectiveModel R M).iso.hom ≫ (boundedAboveDerivedSingleFunctor.map f).hom := by
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      (moduleFreeCochainAugmentationNat R).naturality]
  have h' := boundedAboveLeftDerivedModelIso_naturality F
    (moduleHeartProjectiveModel R M) (moduleHeartProjectiveModel R N)
    (boundedAboveDerivedSingleFunctor.map f) ((moduleFreeCochainResolution R).map f) h
  change (C ⋙ H).map _ ≫ (C ⋙ H).map _ = (C ⋙ H).map _ ≫ (C ⋙ H).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (C ⋙ H).map h'

private def baseChangeUnitDerivedIso :
    ((boundedAboveDerivedBaseChange (algebraMap R R')).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R))).obj ≅
    (moduleObjectFunctor R').obj (ModuleCat.of R' R') := by
  let F := ModuleCat.extendScalars (algebraMap R R')
  let e := boundedAboveDerivedBaseChangeModelIso (algebraMap R R')
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)) boundedAboveDerivedTensorUnitModel
  exact e ≪≫ DerivedCategory.Q.mapIso
    (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app (ModuleCat.of R R)) ≪≫
      (CochainComplex.singleFunctor (ModuleCat R') 0).mapIso (Functor.Monoidal.εIso F).symm)

variable [Fact p.Prime]

private def baseChangeUnitCompletedDerivedIso (hR' : IsIntegralPerfectoid R' p) :
    (derivedComplexCompletionFunctor R' (algebraMap R R' (p : R))).obj
      ((boundedAboveDerivedBaseChange (algebraMap R R')).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R))).obj ≅
      (moduleObjectFunctor R').obj (ModuleCat.of R' R') := by
  let a := algebraMap R R' (p : R)
  have h : IsModuleComplete R' a (ModuleCat.of R' R') := by
    dsimp [a]
    simpa only [map_natCast] using hR'.isModuleComplete R' p
  exact (derivedComplexCompletionFunctor R' a).mapIso (baseChangeUnitDerivedIso R (R' := R')) ≪≫
    (derivedComplexCompletionUnitIso R' a _ h).symm

def completeBaseChangeUnitIso (hR' : IsIntegralPerfectoid R' p) :
    (completeBaseChangeH0 p R (R' := R')).obj (ModuleCat.of R R) ≅ ModuleCat.of R' R' :=
  ((completeBaseChangeH0ModelIso p R (R' := R')).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R') 0).mapIso
      (baseChangeUnitCompletedDerivedIso p R hR') ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R') 0).app _

#print axioms completeBaseChangeUnitIso



private def tensorQuotientBaseChange (J : Ideal R) :
    R' ⊗[R] (R ⧸ J) ≃ₐ[R'] R' ⧸ J.map (algebraMap R R') := by
  let e := Algebra.TensorProduct.rid R R' R'
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := R) R' R R' J).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change Ideal.map (algebraMap R R') J = Ideal.map e.toRingHom (Ideal.map
    (Algebra.TensorProduct.includeRight : R →ₐ[R] R' ⊗[R] R).toRingHom J)
  rw [Ideal.map_map]
  congr 1
  ext x
  change algebraMap R R' x = e ((1 : R') ⊗ₜ[R] x)
  simp [e, Algebra.smul_def]

variable (hR : IsIntegralPerfectoid R p) (J : Ideal R) (hR' : IsIntegralPerfectoid R' p)

private def quotientBaseChangeDerivedIso :
    (derivedComplexCompletionFunctor R' (p : R')).obj
      ((boundedAboveDerivedBaseChange (algebraMap R R')).obj
        (boundedAboveDerivedSingleFunctor.obj
          (ModuleCat.of R (QuotientPerfectoidization R J p hR)))).obj ≅
      (moduleObjectFunctor R').obj (ModuleCat.of R'
        (QuotientPerfectoidization R' (J.map (algebraMap R R')) p hR')) := by
  let J' := J.map (algebraMap R R')
  let B := QuotientPerfectoidization R J p hR
  let B' := QuotientPerfectoidization R' J' p hR'
  let f : R ⧸ J →ₐ[R] B :=
    { toRingHom := toQuotientPerfectoidization R J p hR
      commutes' := fun _ ↦ rfl }
  let f' : R' ⧸ J' →ₐ[R'] B' :=
    { toRingHom := toQuotientPerfectoidization R' J' p hR'
      commutes' := fun _ ↦ rfl }
  let e := tensorQuotientBaseChange R (R' := R') J
  let β := f'.comp e.toAlgHom
  have hβ : IsPerfectoidization p β.toRingHom :=
    (isPerfectoidization_toQuotientPerfectoidization R' J' p hR').comp_ringEquiv e.toRingEquiv
  rw [← map_natCast (algebraMap R R') p]
  exact targetCompletedBaseChangeIso R (R ⧸ J) R' B B' p hR hR' f
    (isPerfectoidization_toQuotientPerfectoidization R J p hR) β hβ

#print axioms quotientBaseChangeDerivedIso



private theorem ker_of_surjectiveFromRing {A : Type u} [CommRing A] [Algebra R' A]
    (g : ModuleCat.of R' R' ⟶ ModuleCat.of R' A) (hg : Function.Surjective g) :
    LinearMap.ker g.hom = (RingHom.ker (algebraMap R' A) : Submodule R' R') := by
  ext x
  change g x = 0 ↔ algebraMap R' A x = 0
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hg 1
    have hxy : g (x * y) = 0 := by
      rw [mul_comm x y]
      change g.hom (y • x) = 0
      rw [map_smul, show g.hom x = 0 from hx, smul_zero]
    change g.hom (x • y) = 0 at hxy
    rw [map_smul, show g.hom y = 1 from hy, Algebra.smul_def, mul_one] at hxy
    exact hxy
  · intro hx
    rw [← mul_one x]
    change g.hom (x • (1 : R')) = 0
    rw [map_smul, Algebra.smul_def, hx, zero_mul]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
theorem perfectoidIdeal_baseChange
    (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (hf : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) R') :
    let K := perfectoidKernel p R hR J
    let K' := perfectoidKernel p R' hR' (J.map (algebraMap R R'))
    let i := (completeBaseChangeH0 p R (R' := R')).map (ModuleCat.ofHom K.subtype) ≫
      (completeBaseChangeUnitIso p R hR').hom
    Function.Injective i ∧ K' = LinearMap.range i.hom := by
  let K := perfectoidKernel p R hR J
  let J' := J.map (algebraMap R R')
  let B := QuotientPerfectoidization R J p hR
  let B' := QuotientPerfectoidization R' J' p hR'
  let f := Algebra.linearMap R B
  let S := ModuleCat.shortComplexOfCompEqZero K.subtype f (by
    ext x
    exact x.property)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S (by
    intro x
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩)
    K.injective_subtype (quotientPerfdMap_surjective p R hR J)
  let φ := algebraMap R R'
  let H (n : ℤ) := DerivedCategory.homologyFunctor (ModuleCat R') n
  let T := completedModuleShortExactTriangle φ (p : R) S hS
  have hT : T ∈ distTriang _ := completedModuleShortExactTriangle_distinguished φ (p : R) S hS
  let eU : T.obj₂ ≅ (moduleObjectFunctor R').obj (ModuleCat.of R' R') :=
    baseChangeUnitCompletedDerivedIso p R hR' 
  let eV : T.obj₃ ≅ (moduleObjectFunctor R').obj (ModuleCat.of R' B') := by
    dsimp only [T, completedModuleShortExactTriangle, completedBaseChangeTriangle]
    rw [map_natCast]
    exact quotientBaseChangeDerivedIso p R hR J hR'
  have h₃ : IsZero ((H (-1)).obj T.obj₃) :=
    (derivedSingleHomology_isZero (ModuleCat.of R' B') (-1) (by norm_num)).of_iso
      ((H (-1)).mapIso eV)
  have h₁ : T.obj₁.IsLE 0 := by
    dsimp only [T, completedModuleShortExactTriangle, completedBaseChangeTriangle]
    rw [map_natCast]
    apply derivedComplexCompletionFunctor_isLE
    have hK : (boundedAboveDerivedSingleFunctor.obj S.X₁).obj.IsLE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj S.X₁).IsLE 0
      infer_instance
    exact boundedAboveLeftDerived_isLE (ModuleCat.extendScalars φ)
      (boundedAboveDerivedSingleFunctor.obj S.X₁) 0
  have h₁' : IsZero ((H 1).obj T.obj₁) := (DerivedCategory.isLE_iff _ _).mp h₁ 1 (by norm_num)
  have hmono : Mono ((H 0).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (-1) 0).mpr
      (h₃.eq_of_src _ _)
  have hepi : Epi ((H 0).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1).mpr
      (h₁'.eq_of_tgt _ _)
  let e2 := (H 0).mapIso eU ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R') 0).app (ModuleCat.of R' R')
  let e3 := (H 0).mapIso eV ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R') 0).app (ModuleCat.of R' B')
  let g := e2.inv ≫ (H 0).map T.mor₂ ≫ e3.hom
  let N := completeBaseChangeH0ModelIso p R (R' := R')
  let i := (completeBaseChangeH0 p R (R' := R')).map (ModuleCat.ofHom K.subtype) ≫
    (completeBaseChangeUnitIso p R hR').hom
  have hi : i = N.inv.app (ModuleCat.of R K) ≫ (H 0).map T.mor₁ ≫ e2.hom := by
    have hn := N.inv.naturality S.f
    change (completeBaseChangeH0 p R (R' := R')).map S.f ≫ N.inv.app S.X₂ =
      N.inv.app S.X₁ ≫ (H 0).map T.mor₁ at hn
    change (completeBaseChangeH0 p R (R' := R')).map S.f ≫ N.inv.app S.X₂ ≫ e2.hom = _
    rw [← Category.assoc, hn, Category.assoc]
  have his : Mono i := by rw [hi]; infer_instance
  have hgs : Function.Surjective g := (ModuleCat.epi_iff_surjective g).mp (by
    dsimp only [g]
    infer_instance)
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (DerivedCategory.HomologySequence.exact₂ T hT 0)
  refine ⟨(ModuleCat.mono_iff_injective i).mp his, ?_⟩
  ext x
  change x ∈ RingHom.ker (algebraMap R' B') ↔ x ∈ LinearMap.range i.hom
  rw [← show LinearMap.ker g.hom = (RingHom.ker (algebraMap R' B') : Submodule R' R') from
    ker_of_surjectiveFromRing g hgs]
  change g x = 0 ↔ ∃ y, i y = x
  have h1 : g x = 0 ↔ (H 0).map T.mor₂ (e2.inv x) = 0 := by
    change e3.hom ((H 0).map T.mor₂ (e2.inv x)) = 0 ↔ _
    rw [← map_zero e3.hom.hom, ((ModuleCat.mono_iff_injective e3.hom).mp inferInstance).eq_iff]
  rw [h1, hex]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨N.hom.app (ModuleCat.of R K) y, ?_⟩
    rw [hi]
    change e2.hom ((H 0).map T.mor₁
      (N.inv.app (ModuleCat.of R K) (N.hom.app (ModuleCat.of R K) y))) = x
    simp only [Iso.app_hom, Iso.app_inv]
    rw [Iso.inv_hom_id_apply, hy, Iso.hom_inv_id_apply]
  · rintro ⟨y, hy⟩
    refine ⟨N.inv.app (ModuleCat.of R K) y, ?_⟩
    rw [hi] at hy
    change e2.hom ((H 0).map T.mor₁ _) = x at hy
    rw [← hy, Iso.inv_hom_id_apply]

#print axioms perfectoidIdeal_baseChange

end SerrePositivity.BhattScholze.Almost
