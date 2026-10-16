module
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation

/-! # 閉零bimodule射の値の複体による外延性 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma value_hom_ext {M N : BimoduleCategory A B C} {f g : M ⟶ N}
    (h : ∀ b c, (valueEvaluation A B C b c).map f = (valueEvaluation A B C b c).map g) :
    f = g := by
  apply hom_ext A B C
  intro c
  apply moduleMorphism_ext A B
  intro b
  exact h b c

end SerrePositivity.DifferentialGraded.BimoduleCategory
