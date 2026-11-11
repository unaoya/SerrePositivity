module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarDifferential
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarTheta_maurerCartan_of_columns
    (h : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I,
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F s) +
      compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F s)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) +
      compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) 2).injective
  funext s
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply]
  simp only [map_add, map_zero]
  have hd := ConcreteCategory.congr_hom
    ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).comm 1 2) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
      ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 2
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)) at hd
  rw [← hd, _root_.SerrePositivity.DifferentialGraded.moduleHomRestriction_compose R D
    (S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s) (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
    (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) (P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_restrict]
  exact h s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
