module

public import SerrePositivity.PerfectComplex.IdempotentImagePerfect
public import SerrePositivity.HomologicalAlgebra.CochainBiproduct
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentDecomposition
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Perfectness and closed support of binary sums -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

def cochainBiprodXIsoProd (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (P ⊞ Q).X n ≅ ModuleCat.of R (P.X n × Q.X n) :=
  Functor.mapBiprod (HomologicalComplex.eval _ _ n) P Q ≪≫
    ModuleCat.biprodIsoProd (P.X n) (Q.X n)

lemma strictlyPerfectComplex_biprod {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    strictlyPerfectComplex R (P ⊞ Q) := by
  obtain ⟨a, b, ha, hb⟩ := hp.1
  obtain ⟨c, d, hc, hd⟩ := hq.1
  have hz : ∀ n, IsZero (P.X n) → IsZero (Q.X n) → IsZero ((P ⊞ Q).X n) := by
    intro n hn hn'
    have := ModuleCat.subsingleton_of_isZero hn
    have := ModuleCat.subsingleton_of_isZero hn'
    exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (P.X n × Q.X n))).of_iso
      (cochainBiprodXIsoProd P Q n)
  refine ⟨⟨min a c, max b d, ?_, ?_⟩, fun n => ?_⟩
  · exact ((P ⊞ Q).isStrictlyGE_iff _).mpr fun n hn => hz n
      (P.isZero_of_isStrictlyGE a n (lt_of_lt_of_le hn (min_le_left _ _)))
      (Q.isZero_of_isStrictlyGE c n (lt_of_lt_of_le hn (min_le_right _ _)))
  · exact ((P ⊞ Q).isStrictlyLE_iff _).mpr fun n hn => hz n
      (P.isZero_of_isStrictlyLE b n (lt_of_le_of_lt (le_max_left _ _) hn))
      (Q.isZero_of_isStrictlyLE d n (lt_of_le_of_lt (le_max_right _ _) hn))
  · have := (hp.2 n).1
    have := (hq.2 n).1
    have := (hp.2 n).2
    have := (hq.2 n).2
    let e := (cochainBiprodXIsoProd P Q n).toLinearEquiv
    exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
      Module.Projective.of_equiv' e.symm⟩

lemma HasHomologySupportOn.biprod {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : HasHomologySupportOn Z P) (hq : HasHomologySupportOn Z Q) :
    HasHomologySupportOn Z (P ⊞ Q) := by
  intro n
  let e : (P ⊞ Q).homology n ≅ ModuleCat.of R (P.homology n × Q.homology n) :=
    Functor.mapBiprod (HomologicalComplex.homologyFunctor _ _ n) P Q ≪≫
    ModuleCat.biprodIsoProd (P.homology n) (Q.homology n)
  rw [e.toLinearEquiv.support_eq]
  exact (module_support_subset_union_of_exact (LinearMap.inl R (P.homology n) (Q.homology n))
    (LinearMap.snd R (P.homology n) (Q.homology n))
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_snd, LinearMap.range_inl]))).trans
      (Set.union_subset (hp n) (hq n))

end SerrePositivity
