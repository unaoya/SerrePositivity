module

public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.StrictlyPerfect
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # 二項の直和の閉じた台

二つの複体のホモロジーの台が閉集合 `Z` に入れば、直和のホモロジーの台も `Z` に入る。直和の有限射影性（`strictlyPerfectComplex_biprod`）は HomologicalAlgebra/Complex/StrictlyPerfect にある。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

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
