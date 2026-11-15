module

public import SerrePositivity.EInfinity.SimplexCuts.CochainInsertionCutSum
public import SerrePositivity.EInfinity.IntervalCuts.IteratedCochainAction

/-!
# 一般の単体鎖の同じ二段余作用と係数交換

Berger–Fresse §2.2.6・§3.1、M14 L12a の元の合成射の証明分割、報告 §307。
元の四つの射をそのまま合成し、既存の任意の複体のKoszul評価を適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 概要：内外の区間余作用の実際の二段適用（BF §3.1）。
方針：余代数の部分合成則に現れる右辺と同じ四射を合成する。
規約：内側係数を前へ交換してから外側作用を施す。
使われ方：χ の余代数公理の右辺を有限切断和で評価する。 -/
def iteratedCochainAction (S : SSet.{0}) (m n : ℕ) (i : Fin (m + 1)) :
    (Surjection.complex A (m + 1) ⊗ Surjection.complex A n) ⊗ chains A S ⟶
      power (chains A S) (m + n) :=
  ((β_ (Surjection.complex A (m + 1)) (Surjection.complex A n)).hom ▷ chains A S) ≫
    (α_ (Surjection.complex A n) (Surjection.complex A (m + 1)) (chains A S)).hom ≫
    (Surjection.complex A n ◁ cochainAction A S (m + 1)) ≫
    tensorCoInsertionAction (chains A S) (Surjection.complex A n) m n i (cochainAction A S n)

/-- 概要：二段適用の係数交換は内外の整数次数の積で決まる（BF §3.1）。
方針：純粋斉次元で交換・結合子・左テンソル作用を順に評価する。
規約：元の外側・内側係数の順序と全次数を保持する。
使われ方：実際の全右辺を外側余作用と内側余代入の和へ移す。 -/
lemma iteratedCochainAction_apply (S : SSet.{0}) (m n : ℕ) (i : Fin (m + 1)) (r s t z : ℤ)
    (hz : r + s + t = z) (x : (Surjection.complex A (m + 1)).X r) (y : (Surjection.complex A n).X s)
    (w : (chains A S).X t) :
    (iteratedCochainAction A S m n i).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A n) (chains A S)
        (r + s) t z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A n) r s (r + s) rfl
          (x ⊗ₜ[A] y) ⊗ₜ[A] w)) =
      (r * s).negOnePow •
        (tensorCoInsertionAction (chains A S) (Surjection.complex A n) m n i
          (cochainAction A S n)).f z
          (ιTensorObj (Surjection.complex A n) (power (chains A S) (m + 1)) s (r + t) z (by omega)
            (y ⊗ₜ[A] (cochainAction A S (m + 1)).f (r + t)
              (ιTensorObj (Surjection.complex A (m + 1)) (chains A S) r t (r + t) rfl
                (x ⊗ₜ[A] w)))) := by
  exact IntervalCuts.coactionComposition_apply A
    (Surjection.complex A (m + 1)) (Surjection.complex A n) (chains A S)
    (power (chains A S) (m + 1)) (power (chains A S) (m + n))
    (cochainAction A S (m + 1))
    (tensorCoInsertionAction (chains A S) (Surjection.complex A n) m n i (cochainAction A S n))
    r s t z hz x y w


end SerrePositivity.EInfinity.SimplexCuts
