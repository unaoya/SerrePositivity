module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcompositionComponents

/-! 閉射による豊穣前合成を、対象圏の小ささを仮定せず全次数で計算する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

lemma dgGluingHomWhiskerRight_f {x y z : D}
    (s : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y)
    (k : ℤ) (a : GradedHom R y z k) :
    (eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) z)).f k a =
      DifferentialGraded.compose R a (closedHomEquiv R D _ _ s).val (zero_add k) := by
  change ((leftUnitor' (homObject R D y z)).inv k ≫
    (ForgetEnrichment.homTo (Complex R) s ▷ homObject R D y z).f k ≫
      (eComp (Complex R) x y z).f k) a = _
  simp only [leftUnitor'_inv, Category.assoc, ι_whiskerRight_assoc]
  change forward R (closedHomEquiv R D _ _ s).val a (zero_add k) = _
  simp only [DifferentialGraded.compose, zero_mul, Int.negOnePow_zero, one_smul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
