module

public import Mathlib.CategoryTheory.Abelian.EpiWithInjectiveKernel
public import Mathlib.CategoryTheory.Abelian.Opposite

/-!
# 射影 cokernel を持つ単射の持ち上げ性

概要：射影 cokernel の単射は任意の全射に対して持ち上げる。
方針：反対圏で injective kernel の既存判定を使う。
規約：次数ごとの線形持ち上げの判定である。
使われ方：複体の全持ち上げ障害への入力。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma mono_projectiveCokernel_lifting {W Z X Y : C} (i : W ⟶ Z) [Mono i] [Projective (cokernel i)]
    (p : X ⟶ Y) [Epi p] : HasLiftingProperty i p := by
  have : Injective (kernel i.op) :=
    Injective.of_iso (kernelOpOp i).symm inferInstance
  exact HasLiftingProperty.iff_op.mpr
    (Abelian.epiWithInjectiveKernel.hasLiftingProperty ⟨inferInstance, inferInstance⟩ p.op)

end SerrePositivity.ComplexLimits
