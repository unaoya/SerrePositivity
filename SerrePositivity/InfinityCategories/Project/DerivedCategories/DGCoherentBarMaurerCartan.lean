module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBianchiEquation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarMaurerCartanCriterion

/-!
概要：元の全 coherent dg 加群図式から構成した bar の θ は、無条件で MC 方程式を満たす。
方針：全末端部分集合の実 HA 右辺比較を Bianchi に渡し、元の各列の式を回収して貼り合わせる。
規約：元の θ・全単体ラベル・全次数加群作用を保持し、filtered 性や MC を仮定しない。
使われ方：D-bar の実 dg bar 摂動と native 余錐の構成への無条件入力。
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

private lemma barCurvature_eq_zero : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarCurvature R D F = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarCurvature_eq_zero_of_bianchi_rhs R D F
  intro n σ J a k hJ ha hb hk
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_rhs R D F σ J a k hJ ha hb hk

lemma dgCoherentBarColumn_maurerCartan (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F s) +
      compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F s)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  have hz := congrArg
    ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 2) (barCurvature_eq_zero R D F)
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarCurvature at hz
  simp only [map_add, map_zero] at hz
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
    (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) (P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)] at hz
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_restrict] using hz

lemma dgCoherentBarTheta_maurerCartan :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) +
      compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_maurerCartan_of_columns R D F (dgCoherentBarColumn_maurerCartan R D F)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
