module
public import SerrePositivity.DifferentialGraded.Module.RingDGComparison
public import SerrePositivity.DifferentialGraded.Complexes.KProjectiveHom
public import SerrePositivity.DifferentialGraded.Derived.HomotopicallyProjective

/-! # 一対象A上の主Homによる射影性と通常のK-projective性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A]

/-- 一対象AではHom endの射影性と評価複体のK-projective性が一致する。 -/
lemma ringModule_homotopicallyProjective_iff (M : RightModule A PUnit.{1}) :
    moduleHomotopicallyProjective A PUnit.{1} (ForgetEnrichment.of (Complex A) M) ↔
      (M.obj (op PUnit.unit)).IsKProjective := by
  constructor
  · intro hM
    apply isKProjective_of_homComplex_acyclic A
    intro N hN
    have h := hM (ForgetEnrichment.of (Complex A) (ringModule A N)) (fun _ => hN)
    exact cochainAcyclic_of_iso h (ringModuleHomIso A M (ringModule A N))
  · intro hM N hN
    let := hM
    exact cochainAcyclic_of_iso
      (homComplex_acyclic_of_isKProjective A (M.obj (op PUnit.unit))
        ((ForgetEnrichment.to (Complex A) N).obj (op PUnit.unit)) (hN PUnit.unit))
      (ringModuleHomIso A M (ForgetEnrichment.to (Complex A) N)).symm

end SerrePositivity.DifferentialGraded
