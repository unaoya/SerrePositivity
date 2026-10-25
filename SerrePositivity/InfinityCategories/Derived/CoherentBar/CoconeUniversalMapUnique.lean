module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeUniversalMap
/-!
概要：任意余錐の全 native 成分を回収する正規化実加群射は一意である。
方針：閉 Hom 同値と全次数の非退化成分同値の単射性を使う。
規約：この厳密な成分一意性と native 写像空間の同値を区別する。
使われ方：工程Bの Hom 比較の零次元での両逆則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeUniversalMap_unique (c : JoinCocone F)
    (g : ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModule R D F hMC) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarCoconeModule R D F c))
    (hg : ∀ s : dgCoherentBarNormalizedIndex I,
      compose R (x := dgCoherentBarSource R D F s.val)
        (y := dgCoherentBarNormalizedModule R D F hMC) (z := dgCoherentBarCoconeModule R D F c)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val
        (dgCoherentBarNativeColumn R D F hMC s.val)
        (show -(s.val.1 : ℤ) + 0 = 0 - (s.val.1 : ℤ) by omega) =
        dgCoherentBarCoconeNativeCoefficients R D F c s) :
    g = dgCoherentBarCoconeUniversalMap R D F hMC c := by
  apply (closedHomEquiv R (RightModule R D)
    (ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModule R D F hMC))
    (ForgetEnrichment.of (Complex R) (dgCoherentBarCoconeModule R D F c))).injective
  apply Subtype.ext
  change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgCoherentBarCoconeUniversalMap R D F hMC c))).val
  rw [dgCoherentBarCoconeUniversalMap_cycle]
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgCoherentBarCoconeModule R D F c) 0).injective
  funext s
  rw [← dgCoherentBarNativeColumn_compose_eq_coordinates,
    ← dgCoherentBarNativeColumn_compose_eq_coordinates, hg,
    dgCoherentBarCoconeHomCandidate_nondegenerate]

abbrev dgCoherentBarCoconeUniversalMapUnconditional (c : JoinCocone F) :=
  dgCoherentBarCoconeUniversalMap R D F (dgCoherentBarTheta_maurerCartan R D F) c

end SerrePositivity.InfinityCategories
