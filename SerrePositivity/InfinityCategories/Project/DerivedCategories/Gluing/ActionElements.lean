module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Objects

/-! 閉元における全 Hom の作用を、各整数次数で元の双加群作用に同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
  DifferentialGraded Opposite
variable {R : Type u} [CommRing R]

/-- 閉次数零の元での内部 Hom の実評価。 -/
lemma dgGluingClosedEvaluation_apply {P Q H : Complex R} (μ : zeroCycles P)
    (a : H ⟶ homComplex R P Q) (n : ℤ) (f : H.X n) :
    ((λ_ H).inv ≫ (unitFromCycle P μ ⊗ₘ a) ≫ evaluation P Q).f n f =
      (a.f n f).v 0 n (zero_add n) μ.val := by
  change (evaluation P Q).f n (((unitFromCycle P μ ⊗ₘ a).f n)
    ((leftUnitor' H).inv n f)) = _
  rw [leftUnitor'_inv]
  change (evaluation P Q).f n (((unitFromCycle P μ ⊗ₘ a).f n)
    (ιTensorObj (𝟙_ (Complex R)) H 0 n n (zero_add n) ((1 : R) ⊗ₜ[R] f))) = _
  rw [tensorMap_apply, evaluation_apply]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  change (a.f n f).v 0 n (zero_add n) (cycleFromUnit P (unitFromCycle P μ)).val = _
  rw [cycleFromUnit_unitFromCycle]

variable (R) (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- νf の全次数成分は、元の右加群の斉次作用そのもの。 -/
lemma dgGluingLeftAction_apply (n : ℤ) (f : GradedHom R X.left Y.left n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y).f n f =
      moduleAction R (M.rightAt Y.right) (x := op Y.left) (y := op X.left)
        f Y.gluing.val (zero_add n) :=
  dgGluingClosedEvaluation_apply _ _ _ _

/-- gμ の全次数成分は、元の左加群の斉次作用そのもの。 -/
lemma dgGluingRightAction_apply (n : ℤ) (g : GradedHom R X.right Y.right n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y).f n g =
      leftAction R (M.leftAt X.left) g X.gluing.val (zero_add n) :=
  dgGluingClosedEvaluation_apply _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
