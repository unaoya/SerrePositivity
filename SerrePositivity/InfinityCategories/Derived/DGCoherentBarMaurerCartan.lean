module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiEquation
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarMaurerCartanCriterion

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

private lemma barCurvature_eq_zero : dgCoherentBarCurvature R D F = 0 := by
  apply dgCoherentBarCurvature_eq_zero_of_bianchi_rhs R D F
  intro n σ J a k hJ ha hb hk
  exact dgCoherentBarBianchiData_rhs R D F σ J a k hJ ha hb hk

lemma dgCoherentBarColumn_maurerCartan (s : dgCoherentBarIndex I) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
        (dgCoherentBarColumn R D F s) +
      compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarColumn R D F s)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  have hz := congrArg
    ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 2) (barCurvature_eq_zero R D F)
  unfold dgCoherentBarCurvature at hz
  simp only [map_add, map_zero] at hz
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
    (N := dgCoherentBarGraded R D F) (P := dgCoherentBarGraded R D F)] at hz
  simpa only [dgCoherentBarTheta_restrict] using hz

lemma dgCoherentBarTheta_maurerCartan :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
        (dgCoherentBarTheta R D F) +
      compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarTheta R D F)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 :=
  dgCoherentBarTheta_maurerCartan_of_columns R D F (dgCoherentBarColumn_maurerCartan R D F)

end SerrePositivity.InfinityCategories
