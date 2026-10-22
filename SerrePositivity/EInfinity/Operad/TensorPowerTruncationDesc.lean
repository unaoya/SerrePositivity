module

public import SerrePositivity.EInfinity.Operad.ConnectiveCover
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorTruncationDesc

/-!
# 非正複体の全テンソル冪の smart 零次商への降下

概要：全 arity の元の演算射を、各入力の τ≥0 へ一意に降ろす。
方針：二入力の切断降下と内部 Hom の下界を入力数に沿って反復する。
規約：平坦性・有限生成性を仮定せず、零入力も含む。
使われ方：元の非正 E 代数の零次商。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad.Algebra
open CategoryTheory MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.LocalizingInvariants
variable {A : Type u} [CommRing A]

def descendPower (X : Complex A) [X.IsStrictlyLE 0] :
    ∀ (n : ℕ) {T : Complex A} [T.IsStrictlyGE 0],
      (TensorPowers.power X n ⟶ T) →
        (TensorPowers.power (X.truncGE 0) n ⟶ T)
  | 0, _, _, f => f
  | n + 1, T, _, f => by
    let := power_nonpositive X n
    let := TruncationDesc.truncation_nonpositive X 0
    let := internalHom_lowerBound (X.truncGE 0) T 0
    exact uncurry (descendPower X n (curry (TruncationDesc.descendFirst 0 f)))

lemma projection_descendPower (X : Complex A) [X.IsStrictlyLE 0] (n : ℕ)
    {T : Complex A} [T.IsStrictlyGE 0] (f : TensorPowers.power X n ⟶ T) :
    TensorPowers.map (X.πTruncGE 0) n ≫ descendPower X n f = f := by
  induction n generalizing T with
  | zero => exact Category.id_comp f
  | succ n ih =>
    let := power_nonpositive X n
    let := TruncationDesc.truncation_nonpositive X 0
    let := internalHom_lowerBound (X.truncGE 0) T 0
    change (X.πTruncGE 0 ⊗ₘ TensorPowers.map (X.πTruncGE 0) n) ≫
      uncurry (descendPower X n (curry (TruncationDesc.descendFirst 0 f))) = f
    rw [tensorHom_def, Category.assoc, ← uncurry_natural_left, ih, uncurry_curry]
    exact TruncationDesc.projection_descendFirst 0 f

def descendCoefficientPower (X Q : Complex A) [X.IsStrictlyLE 0] [Q.IsStrictlyLE 0]
    (n : ℕ) {T : Complex A} [T.IsStrictlyGE 0]
    (f : Q ⊗ TensorPowers.power X n ⟶ T) :
    Q ⊗ TensorPowers.power (X.truncGE 0) n ⟶ T := by
  let := internalHom_lowerBound Q T 0
  exact uncurry (descendPower X n (curry f))

lemma projection_descendCoefficientPower (X Q : Complex A)
    [X.IsStrictlyLE 0] [Q.IsStrictlyLE 0] (n : ℕ) {T : Complex A} [T.IsStrictlyGE 0]
    (f : Q ⊗ TensorPowers.power X n ⟶ T) :
    (Q ◁ TensorPowers.map (X.πTruncGE 0) n) ≫ descendCoefficientPower X Q n f = f := by
  let := internalHom_lowerBound Q T 0
  change (Q ◁ TensorPowers.map (X.πTruncGE 0) n) ≫
    uncurry (descendPower X n (curry f)) = f
  rw [← uncurry_natural_left, projection_descendPower, uncurry_curry]

end SerrePositivity.EInfinity.Operad.Algebra
