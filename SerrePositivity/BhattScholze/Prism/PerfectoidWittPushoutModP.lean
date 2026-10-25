module

public import SerrePositivity.BhattScholze.Prism.PerfectoidWittPushout
public import SerrePositivity.BhattScholze.Prism.WittQuotientModP

/-! # B4-5：Witt係数余積のmod pと標準射

係数テンソルにCharP pを持つ枝の具体的な同型と、左右の標準射の式。
通常テンソルのmod pとの同型はさらに別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (R A B : Type u)
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CharP R p] [CharP A p] [CharP B p]
variable [PerfectRing R p] [PerfectRing A p] [PerfectRing B p]
variable [CharP (A ⊗[R] B) p]

/-- Witt係数余積のmod pは、係数テンソルを基底生成元の第0係数の像で割った環。 -/
def wittCoefficientPushoutModPEquiv (d : WittVector p R) :
    ModP (WittCoefficientPushout p R A B d) p ≃+*
      (A ⊗[R] B) ⧸ Ideal.span
        {((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom)
          (algebraMap R A (d.coeff 0))} := by
  let : PerfectRing (A ⊗[R] B) p := perfectCoefficientTensor_perfectRing p R A B
  exact wittQuotientModPEquiv p (A ⊗[R] B) _

/-- 同型はWitt代表元の第0係数を標準商へ写す。 -/
@[simp] theorem wittCoefficientPushoutModPEquiv_mk (d : WittVector p R)
    (x : WittVector p (A ⊗[R] B)) :
    wittCoefficientPushoutModPEquiv p R A B d
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) =
      Ideal.Quotient.mk _ (x.coeff 0) := rfl

/-- 左因子の標準射のmod pでの式。 -/
@[simp] theorem wittCoefficientPushoutModPEquiv_left_mk (d : WittVector p R)
    (x : WittVector p A) :
    wittCoefficientPushoutModPEquiv p R A B d
      (Ideal.Quotient.mk _
        (wittCoefficientPushoutLeft p R A B d (Ideal.Quotient.mk _ x))) =
      Ideal.Quotient.mk _ (x.coeff 0 ⊗ₜ[R] (1 : B)) := by
  rw [wittCoefficientPushoutLeft_mk, wittCoefficientPushoutModPEquiv_mk]
  rfl

/-- 右因子の標準射のmod pでの式。 -/
@[simp] theorem wittCoefficientPushoutModPEquiv_right_mk (d : WittVector p R)
    (x : WittVector p B) :
    wittCoefficientPushoutModPEquiv p R A B d
      (Ideal.Quotient.mk _
        (wittCoefficientPushoutRight p R A B d (Ideal.Quotient.mk _ x))) =
      Ideal.Quotient.mk _ ((1 : A) ⊗ₜ[R] x.coeff 0) := by
  rw [wittCoefficientPushoutRight_mk, wittCoefficientPushoutModPEquiv_mk]
  rfl

end SerrePositivity.BhattScholze
