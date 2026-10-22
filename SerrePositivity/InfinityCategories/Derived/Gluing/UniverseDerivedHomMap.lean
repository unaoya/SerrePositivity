module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalDerivedHomMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseCoefficientMappingSpan

/-! 射影的始域からの元の導来 Hom 作用の同値性を、同じ共通宇宙の実写像へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingUniverseModuleDerivedHomMap_equivalence (N P : RightModule R C)
    (hN : moduleHomotopicallyProjective R C (ForgetEnrichment.of (Complex R) N)) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
        (ULift.up (Simplex.vertex N)) (ULift.up (Simplex.vertex P))) := by
  let L := dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))
  change IsSimplicialHomotopyEquivalence (pinchedHomMap
    ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map L)
    (ULift.up (Simplex.vertex N)) (ULift.up (Simplex.vertex P)))
  apply (dgGluingHomotopyEquivalence_precomp_iso_iff
    (uliftPinchedHomIso.{max (u + 1) v, max (u + 1) v w}
      (C := dgNerve R (RightModule R C)) (Simplex.vertex N) (Simplex.vertex P)) _).mp
  rw [← uliftPinchedHomIso_naturality]
  apply (dgGluingHomotopyEquivalence_postcomp_iso_iff _
    (uliftPinchedHomIso.{max (u + 1) v, max (u + 1) v w}
      (L.app (Opposite.op ⦋0⦌) (Simplex.vertex N))
      (L.app (Opposite.op ⦋0⦌) (Simplex.vertex P)))).mpr
  exact (dgGluingModuleDerivedHomMap_equivalence R C N P hN).ulift

end SerrePositivity.InfinityCategories
