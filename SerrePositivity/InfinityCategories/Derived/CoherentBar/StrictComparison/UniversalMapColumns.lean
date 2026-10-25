module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeUniversalMap
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ShiftPostcomposition
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Unconditional

/-!
概要：指定 native 余錐の増大射の全列は、元の同じ余錐の係数。
方針：増大射の閉零 cycle と B の列回収式を前後合成の式で結ぶ。
規約：零次元列だけでなく全次数・全単体列を保持する。
使われ方：C1 のホモロジー増大と指定 native 増大の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgBarCoconeUniversalMap_columns (c : JoinCocone G) (s : dgCoherentBarIndex I) :
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G s))
      (dgCoherentBarCoconeUniversalMap R D G (dgCoherentBarMaurerCartan_unconditional R D G) c)).f
      (-(s.1 : ℤ))
      (dgCoherentBarNativeColumn R D G (dgCoherentBarMaurerCartan_unconditional R D G) s) =
        dgCoherentBarCoconeColumn R D G c s := by
  rw [dgStrictPostcompose_eq_compose]
  change compose R (x := dgCoherentBarSource R D G s)
    (y := dgCoherentBarNormalizedModuleUnconditional R D G)
    (z := dgCoherentBarCoconeModule R D G c)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgCoherentBarCoconeUniversalMap R D G (dgCoherentBarMaurerCartan_unconditional R D G) c))).val
    (dgCoherentBarNativeColumn R D G (dgCoherentBarMaurerCartan_unconditional R D G) s)
    (add_zero (-(s.1 : ℤ))) = _
  rw [dgCoherentBarCoconeUniversalMap_cycle, dgCoherentBarCoconeHomCandidate_columns]

end SerrePositivity.InfinityCategories
