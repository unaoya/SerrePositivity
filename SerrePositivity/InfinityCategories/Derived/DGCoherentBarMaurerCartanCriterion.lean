module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarDifferential
public import SerrePositivity.DifferentialGraded.Module.HomRestrictionComposition
/-!
概要：元の coherent bar の MC 方程式を、各元の summand からの式へ帰着する。
方針：同じ直和からの全 Hom の直積表示と、閉包含による制限の微分・合成保存を使う。
規約：列の式を明示し、HA 方程式からのその実証を省略しない。
使われ方：bar 微分の二乗零の単体ごとの証明。
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

lemma dgCoherentBarTheta_maurerCartan_of_columns
    (h : ∀ s : dgCoherentBarIndex I,
      (moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
          (dgCoherentBarColumn R D F s) +
      compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarColumn R D F s)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
        (dgCoherentBarTheta R D F) +
      compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarTheta R D F)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  apply (dgCoherentBarHomEquiv R D F (dgCoherentBarGraded R D F) 2).injective
  funext s
  rw [dgCoherentBarHomEquiv_apply, dgCoherentBarHomEquiv_apply]
  simp only [map_add, map_zero]
  have hd := ConcreteCategory.congr_hom
    ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).comm 1 2) (dgCoherentBarTheta R D F)
  change (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
      ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
        (dgCoherentBarGraded R D F)).f 1 (dgCoherentBarTheta R D F)) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 2
      ((moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
        (dgCoherentBarTheta R D F)) at hd
  rw [← hd, moduleHomRestriction_compose R D
    (S := dgCoherentBarFamily R D F s) (M := dgCoherentBarGraded R D F)
    (N := dgCoherentBarGraded R D F) (P := dgCoherentBarGraded R D F)]
  simp only [dgCoherentBarTheta_restrict]
  exact h s

end SerrePositivity.InfinityCategories
