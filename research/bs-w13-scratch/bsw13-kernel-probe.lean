import SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization
import SerrePositivity.BhattScholze.Almost.Lemma103
import SerrePositivity.CommutativeAlgebra.Almost.Quotient
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid
import SerrePositivity.InfinityCategories.Derived.Homology

noncomputable section
universe u
open SerrePositivity
namespace SerrePositivity.BhattScholze.Almost

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
  (J : Ideal R)

def quotientPerfdMap : R →+* QuotientPerfectoidization R J p hR :=
  (toQuotientPerfectoidization R J p hR).comp (Ideal.Quotient.mk J)

def perfectoidKernel : Ideal R := RingHom.ker (quotientPerfdMap p R hR J)

theorem le_perfectoidKernel : J ≤ perfectoidKernel p R hR J := by
  intro x hx
  rw [perfectoidKernel, RingHom.mem_ker, quotientPerfdMap, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

theorem perfectoidKernel_le {T : Type u} [CommRing T] (hT : IsIntegralPerfectoid T p)
    (f : R →+* T) (h : J ≤ RingHom.ker f) :
    perfectoidKernel p R hR J ≤ RingHom.ker f := by
  let f' := Ideal.Quotient.lift J f (fun x hx => h hx)
  obtain ⟨l, hl, _⟩ := (isPerfectoidization_toQuotientPerfectoidization R J p hR).2 T hT f'
  intro x hx
  change quotientPerfdMap p R hR J x = 0 at hx
  change f x = 0
  have he := DFunLike.congr_fun hl (Ideal.Quotient.mk J x)
  change l (quotientPerfdMap p R hR J x) = f x at he
  rw [hx, map_zero] at he
  exact he.symm

theorem perfectoidKernel_mono {I : Ideal R} (h : J ≤ I) :
    perfectoidKernel p R hR J ≤ perfectoidKernel p R hR I :=
  perfectoidKernel_le p R hR J (isPerfectoidization_toQuotientPerfectoidization R I p hR).1
    (quotientPerfdMap p R hR I) (h.trans (le_perfectoidKernel p R hR I))

theorem perfectoidIdeal_radical :
    perfectoidKernel p R hR J = perfectoidKernel p R hR J.radical := by
  refine le_antisymm (perfectoidKernel_mono p R hR J Ideal.le_radical) ?_
  have hB := (isPerfectoidization_toQuotientPerfectoidization R J p hR).1
  have := hB.isReduced _ p
  refine perfectoidKernel_le p R hR J.radical hB (quotientPerfdMap p R hR J) ?_
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  have hh := le_perfectoidKernel p R hR J hn
  change quotientPerfdMap p R hR J (x ^ n) = 0 at hh
  rw [map_pow] at hh
  exact IsNilpotent.eq_zero ⟨n, hh⟩

open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
open SerrePositivity.InfinityCategories SSet
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard

abbrev DVertex (A : Type u) [CommRing A] := (derivedInfinityCategory A) _⦋0⦌

def IsJAlmostZero (M : DVertex R) : Prop :=
  ∀ i : ℤ, SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR J)
    (derivedInfinityHomology R i M)

def IsAlmostConnective (M : DVertex R) : Prop :=
  ∀ i : ℤ, 0 < i → SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR J)
    (derivedInfinityHomology R i M)

theorem isAlmostZero_radical (M : DVertex R) :
    IsJAlmostZero p R hR J M ↔ IsJAlmostZero p R hR J.radical M := by
  rw [IsJAlmostZero, IsJAlmostZero, ← perfectoidIdeal_radical p R hR J]
theorem quotientPerfdMap_surjective : Function.Surjective (quotientPerfdMap p R hR J) := by
  have hs := surjective_perfectoidization_of_quotient p hR
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (toQuotientPerfectoidization R J p hR)
    (isPerfectoidization_toQuotientPerfectoidization R J p hR)
  exact hs.comp Ideal.Quotient.mk_surjective

theorem perfectoidKernel_quotient_isIntegralPerfectoid :
    IsIntegralPerfectoid (R ⧸ perfectoidKernel p R hR J) p :=
  isIntegralPerfectoid_of_ringEquiv p
    (RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J)).symm
    (isPerfectoidization_toQuotientPerfectoidization R J p hR).1

theorem perfectoidKernel_completedTensor_isZero_of_isAlmostZero
    (M : ModuleCat.{u} R) (hM : SerrePositivity.Almost.IsAlmostZero
      (perfectoidKernel p R hR J) M) :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((boundedAboveDerivedTensorModuleFunctor
        (ModuleCat.of R (perfectoidKernel p R hR J))).obj M)) := by
  let K := perfectoidKernel p R hR J
  let := SerrePositivity.Almost.quotientModule K M hM
  let := SerrePositivity.Almost.quotientModule_scalarTower K M hM
  exact completedTensor_isZero_of_algebraModule R (p : R) (R ⧸ K) M
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R K))
    (integralPerfectoid_completedIdealTensorQuotient_isZero p K hR
      (perfectoidKernel_quotient_isIntegralPerfectoid p R hR J))

#print axioms perfectoidIdeal_radical
#print axioms perfectoidKernel_completedTensor_isZero_of_isAlmostZero
end SerrePositivity.BhattScholze.Almost

namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
open SerrePositivity.InfinityCategories SSet
open scoped Simplicial TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

include hR in
private theorem annihilator_isModuleComplete (M : ModuleCat.{u} R)
    (hM : IsModuleComplete R (p : R) M) :
    IsModuleComplete R (p : R) (ModuleCat.of R (Module.annihilator R M)) := by
  have hr := (isModuleComplete_iff_recurrence_bijective R (p : R) (ModuleCat.of R R)).mp
    (hR.isModuleComplete_algebra R R p)
  have hm := (isModuleComplete_iff_recurrence_bijective R (p : R) M).mp hM
  apply (isModuleComplete_iff_recurrence_bijective R (p : R) _).mpr
  constructor
  · intro x y hxy
    have he : (fun n ↦ (x n).val) = (fun n ↦ (y n).val) := hr.injective
      (congrArg (fun z n ↦ (z n).val) hxy)
    funext n
    exact Subtype.ext (congrFun he n)
  · intro y
    obtain ⟨x, hx⟩ := hr.surjective (fun n ↦ (y n).val)
    have hxAnn (n : ℕ) : x n ∈ Module.annihilator R M := by
      apply Module.mem_annihilator.mpr
      intro m
      let g := LinearMap.toSpanSingleton R M m
      have hg : adicRecurrenceMap (p : R) (fun n ↦ g (x n)) = 0 := by
        funext n
        change g (x n) - (p : R) • g (x (n + 1)) = 0
        rw [← map_smul, ← map_sub]
        exact (congrArg g (congrFun hx n)).trans (Module.mem_annihilator.mp (y n).property m)
      exact congrFun (hm.injective (hg.trans (map_zero _).symm)) n
    refine ⟨fun n ↦ ⟨x n, hxAnn n⟩, ?_⟩
    funext n
    exact Subtype.ext (congrFun hx n)

private def quotientPerfdMap_factor (J : Ideal R)
    {A : Type u} [CommRing A] [Algebra R A]
    (h : perfectoidKernel p R hR J ≤ RingHom.ker (algebraMap R A)) :
    QuotientPerfectoidization R J p hR →ₐ[R] A where
  toRingHom := (Ideal.Quotient.lift (perfectoidKernel p R hR J) (algebraMap R A)
    (fun _ hx ↦ h hx)).comp
      (RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J)).symm.toRingHom
  commutes' x := by
    change Ideal.Quotient.lift (perfectoidKernel p R hR J) (algebraMap R A) (fun _ hx ↦ h hx)
      ((RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J)).symm
        (quotientPerfdMap p R hR J x)) = _
    rw [show quotientPerfdMap p R hR J x =
        RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J)
          (Ideal.Quotient.mk (perfectoidKernel p R hR J) x) from rfl,
      RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]

private theorem perfectoidKernel_sup_le_ker {I J : Ideal R} {A : Type u} [CommRing A] [Algebra R A]
    (hA : IsModuleComplete R (p : R) (ModuleCat.of R A))
    (hI : perfectoidKernel p R hR I ≤ RingHom.ker (algebraMap R A))
    (hJ : perfectoidKernel p R hR J ≤ RingHom.ker (algebraMap R A)) :
    perfectoidKernel p R hR (I ⊔ J) ≤ RingHom.ker (algebraMap R A) := by
  let S := QuotientPerfectoidization R I p hR
  let T := QuotientPerfectoidization R J p hR
  let D := S ⊗[R] T
  let C := PrincipalCompletionH0 D (p : D)
  let : CommRing C := principalCompletionCommRing D (p : D)
  let d := principalCompletionUnitRingHom D (p : D)
  let e : D →ₐ[R] A := Algebra.TensorProduct.lift (quotientPerfdMap_factor p R hR I hI)
    (quotientPerfdMap_factor p R hR J hJ) (fun _ _ ↦ Commute.all _ _)
  let : Algebra D A := e.toRingHom.toAlgebra
  let : IsScalarTower R D A := IsScalarTower.of_algebraMap_eq (fun x ↦ (e.commutes x).symm)
  have ha : IsModuleComplete D (p : D) (ModuleCat.of D A) := by
    simpa only [map_natCast] using (isModuleComplete_algebraMap_iff R D (p : R) A).mpr hA
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  have hc : IsIntegralPerfectoid C p :=
    isIntegralPerfectoid_of_ringEquiv p (completedTensorH0PrincipalRingEquiv R p S T)
      (integralPerfectoid_completedTensorH0_isIntegralPerfectoid p R S T hR
        (isPerfectoidization_toQuotientPerfectoidization R I p hR).1
        (isPerfectoidization_toQuotientPerfectoidization R J p hR).1)
  have hkill : I ⊔ J ≤ RingHom.ker (d.comp (algebraMap R D)) := by
    apply sup_le
    · intro x hx
      have hx' : algebraMap R S x = 0 := le_perfectoidKernel p R hR I hx
      change d (algebraMap R D x) = 0
      rw [IsScalarTower.algebraMap_apply R S D, hx', map_zero, map_zero]
    · intro x hx
      have hx' : algebraMap R T x = 0 := le_perfectoidKernel p R hR J hx
      change d (algebraMap R D x) = 0
      rw [← (Algebra.TensorProduct.includeRight : T →ₐ[R] D).commutes x,
        hx', map_zero, map_zero]
  have hK := perfectoidKernel_le p R hR (I ⊔ J) hc _ hkill
  obtain ⟨g, hg, _⟩ := principalCompletion_existsUnique_ringHom D (p : D) A e.toRingHom ha
  intro x hx
  have hcx : d (algebraMap R D x) = 0 := hK hx
  have he := DFunLike.congr_fun hg (algebraMap R D x)
  change g (d (algebraMap R D x)) = e (algebraMap R D x) at he
  rw [hcx, map_zero, e.commutes] at he
  exact he.symm

theorem isAlmostZero_perfectoidKernel_sup (I J : Ideal R) (M : ModuleCat.{u} R)
    (hM : IsModuleComplete R (p : R) M)
    (hI : SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR I) M)
    (hJ : SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR J) M) :
    SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR (I ⊔ J)) M := by
  let A := Module.annihilator R M
  have hA := annihilator_isModuleComplete p R hR M hM
  have hR' := hR.isModuleComplete_algebra R R p
  have hc := isModuleComplete_coker R (p : R) (M := ModuleCat.of R A) A.subtype hA hR'
  rw [Submodule.range_subtype] at hc
  have hk : RingHom.ker (algebraMap R (R ⧸ A)) = A := Ideal.mk_ker
  change perfectoidKernel p R hR (I ⊔ J) ≤ A
  change perfectoidKernel p R hR I ≤ A at hI
  change perfectoidKernel p R hR J ≤ A at hJ
  rw [← hk] at hI hJ ⊢
  exact perfectoidKernel_sup_le_ker p R hR hc hI hJ

#print axioms isAlmostZero_perfectoidKernel_sup

end SerrePositivity.BhattScholze.Almost

namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory SerrePositivity.DerivedCompletion SerrePositivity.InfinityCategories
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

def isPCompleteVertex (M : DVertex R) : Prop :=
  IsComplete R (p : R) ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩)

theorem isAlmostZero_iff_forall_gen (J : Ideal R) {r : ℕ} (f : Fin r → R)
    (hf : J = Ideal.span (Set.range f)) (M : DVertex R) (hM : isPCompleteVertex p R M) :
    IsJAlmostZero p R hR J M ↔ ∀ i, IsJAlmostZero p R hR (Ideal.span {f i}) M := by
  classical
  constructor
  · intro h i n
    exact (perfectoidKernel_mono p R hR _ (by
      rw [hf]
      exact Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨i, rfl⟩))).trans (h n)
  · intro h n
    let N := derivedInfinityHomology R n M
    have hn : IsModuleComplete R (p : R) N :=
      isComplete_homology_isModuleComplete R (p : R) _ hM n
    have hs (s : Finset R) (hf' : (s : Set R) ⊆ Set.range f) :
        SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR (Ideal.span (s : Set R))) N := by
      induction s using Finset.induction_on with
      | empty =>
        have hker : RingHom.ker (RingHom.id R) = ⊥ :=
          (RingHom.ker_eq_bot_iff_eq_zero (RingHom.id R)).mpr (fun _ hx ↦ hx)
        have hz : perfectoidKernel p R hR (⊥ : Ideal R) ≤ ⊥ := by
          rw [← hker]
          exact perfectoidKernel_le p R hR _ hR (RingHom.id R) bot_le
        simpa only [Finset.coe_empty, Ideal.span_empty, SerrePositivity.Almost.IsAlmostZero] using
          (hz.trans (bot_le : (⊥ : Ideal R) ≤ Module.annihilator R N))
      | insert a s has ih =>
        obtain ⟨i, hi⟩ := hf' (Finset.mem_insert_self a s)
        have ha := h i n
        rw [hi] at ha
        rw [Finset.coe_insert, Set.insert_eq, Ideal.span_union]
        exact isAlmostZero_perfectoidKernel_sup p R hR _ _ N hn ha
          (ih (fun _ hx => hf' (Finset.mem_insert_of_mem hx)))
    have he : ((Finset.univ.image f : Finset R) : Set R) = Set.range f := by
      simp
    rw [hf, ← he]
    exact hs _ (he ▸ Set.Subset.rfl)

#print axioms isAlmostZero_iff_forall_gen

end SerrePositivity.BhattScholze.Almost
