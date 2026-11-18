module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConnectiveCover
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorTruncationDesc

/-!
模型。文献の定義との比較は後で
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
namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {A : Type u} [CommRing A]

def descendPower (X : Complex A) [X.IsStrictlyLE 0] :
    ∀ (n : ℕ) {T : Complex A} [T.IsStrictlyGE 0],
      (_root_.SerrePositivity.TensorPowers.power X n ⟶ T) →
        (_root_.SerrePositivity.TensorPowers.power (X.truncGE 0) n ⟶ T)
  | 0, _, _, f => f
  | n + 1, T, _, f => by
    let := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.power_nonpositive X n
    let := TruncationDesc.truncation_nonpositive X 0
    let := internalHom_lowerBound (X.truncGE 0) T 0
    exact uncurry (descendPower X n (curry (TruncationDesc.descendFirst 0 f)))

lemma projection_descendPower (X : Complex A) [X.IsStrictlyLE 0] (n : ℕ)
    {T : Complex A} [T.IsStrictlyGE 0] (f : _root_.SerrePositivity.TensorPowers.power X n ⟶ T) :
    _root_.SerrePositivity.TensorPowers.map (X.πTruncGE 0) n ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.descendPower X n f = f := by
  induction n generalizing T with
  | zero => exact Category.id_comp f
  | succ n ih =>
    let := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.power_nonpositive X n
    let := TruncationDesc.truncation_nonpositive X 0
    let := internalHom_lowerBound (X.truncGE 0) T 0
    change (X.πTruncGE 0 ⊗ₘ _root_.SerrePositivity.TensorPowers.map (X.πTruncGE 0) n) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.descendPower X n (curry (TruncationDesc.descendFirst 0 f))) = f
    rw [tensorHom_def, Category.assoc, ← uncurry_natural_left, ih, uncurry_curry]
    exact TruncationDesc.projection_descendFirst 0 f

def descendCoefficientPower (X Q : Complex A) [X.IsStrictlyLE 0] [Q.IsStrictlyLE 0]
    (n : ℕ) {T : Complex A} [T.IsStrictlyGE 0]
    (f : Q ⊗ _root_.SerrePositivity.TensorPowers.power X n ⟶ T) :
    Q ⊗ _root_.SerrePositivity.TensorPowers.power (X.truncGE 0) n ⟶ T := by
  let := internalHom_lowerBound Q T 0
  exact uncurry (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.descendPower X n (curry f))

lemma projection_descendCoefficientPower (X Q : Complex A)
    [X.IsStrictlyLE 0] [Q.IsStrictlyLE 0] (n : ℕ) {T : Complex A} [T.IsStrictlyGE 0]
    (f : Q ⊗ _root_.SerrePositivity.TensorPowers.power X n ⟶ T) :
    (Q ◁ _root_.SerrePositivity.TensorPowers.map (X.πTruncGE 0) n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.descendCoefficientPower X Q n f = f := by
  let := internalHom_lowerBound Q T 0
  change (Q ◁ _root_.SerrePositivity.TensorPowers.map (X.πTruncGE 0) n) ≫
    uncurry (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.descendPower X n (curry f)) = f
  rw [← uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.projection_descendPower, uncurry_curry]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
