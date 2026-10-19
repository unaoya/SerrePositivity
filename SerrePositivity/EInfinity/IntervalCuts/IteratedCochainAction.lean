module

public import SerrePositivity.EInfinity.IntervalCuts.CochainInsertionSums
public import SerrePositivity.EInfinity.IntervalCuts.NestedFaceCutEquiv

/-!
# 区間余作用の二段適用と係数交換

概要：Berger–Fresse §3.1 の部分合成則の右辺を実際の複体射として評価する。
方針：内外係数の交換、結合子、外側作用、指定出力への内側作用を順に計算する。
規約：余代数公理は仮定せず、arity 零も許す。
使われ方：合成語の切断作用と比較する右辺そのもの。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

attribute [local implicit_reducible] TensorPowers.power

/-- 概要：二段余作用の係数交換と外側作用の斉次評価（BF §3.1）。
方針：任意の複体で Koszul 交換、結合子、左テンソル射を評価する。
規約：交換される二係数と第三因子の全整数次数を保持する。
使われ方：具体的な全射語複体を展開せず二段作用の評価を得る。 -/
lemma coactionComposition_apply (P Q K W X : Complex A) (θ : P ⊗ K ⟶ W)
    (ψ : Q ⊗ W ⟶ X) (r s t z : ℤ) (hz : r + s + t = z)
    (x : P.X r) (y : Q.X s) (w : K.X t) :
    (((β_ P Q).hom ▷ K) ≫ (α_ Q P K).hom ≫ (Q ◁ θ) ≫ ψ).f z
      (ιTensorObj (P ⊗ Q) K (r + s) t z hz
        (ιTensorObj P Q r s (r + s) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] w)) =
      (r * s).negOnePow • ψ.f z
        (ιTensorObj Q W s (r + t) z (by omega)
          (y ⊗ₜ[A] θ.f (r + t) (ιTensorObj P K r t (r + t) rfl (x ⊗ₜ[A] w)))) := by
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply]
  rw [braiding_eq_existing]
  rw [signedSwap_apply]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]
  rw [SerrePositivity.DifferentialGraded.associator_apply_of_sum,
    SerrePositivity.DifferentialGraded.whiskerLeft_apply]

/-- 概要：内外の区間余作用の実際の二段適用（BF §3.1）。
方針：余代数の部分合成則に現れる右辺と同じ四射を合成する。
規約：内側係数を前へ交換してから外側作用を施す。
使われ方：χ の余代数公理の右辺を有限切断和で評価する。 -/
def iteratedCochainAction (m n : ℕ) (i : Fin (m + 1)) :
    (complex A (m + 1) ⊗ complex A n) ⊗ interval A ⟶ power (interval A) (m + n) :=
  ((β_ (complex A (m + 1)) (complex A n)).hom ▷ interval A) ≫
    (α_ (complex A n) (complex A (m + 1)) (interval A)).hom ≫
    (complex A n ◁ cochainAction A (m + 1)) ≫
    tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)

/-- 概要：二段適用の係数交換は内外の整数次数の積で決まる（BF §3.1）。
方針：純粋斉次元で交換・結合子・左テンソル作用を順に評価する。
規約：元の外側・内側係数の順序と全次数を保持する。
使われ方：実際の全右辺を外側余作用と内側余代入の和へ移す。 -/
lemma iteratedCochainAction_apply (m n : ℕ) (i : Fin (m + 1)) (r s t z : ℤ)
    (hz : r + s + t = z) (x : (complex A (m + 1)).X r) (y : (complex A n).X s)
    (w : (interval A).X t) :
    (iteratedCochainAction A m n i).f z
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A) (r + s) t z hz
        (ιTensorObj (complex A (m + 1)) (complex A n) r s (r + s) rfl
          (x ⊗ₜ[A] y) ⊗ₜ[A] w)) =
      (r * s).negOnePow •
        (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f z
          (ιTensorObj (complex A n) (power (interval A) (m + 1)) s (r + t) z (by omega)
            (y ⊗ₜ[A] (cochainAction A (m + 1)).f (r + t)
              (ιTensorObj (complex A (m + 1)) (interval A) r t (r + t) rfl
                (x ⊗ₜ[A] w)))) := by
  exact coactionComposition_apply A (complex A (m + 1)) (complex A n) (interval A)
    (power (interval A) (m + 1)) (power (interval A) (m + n))
    (cochainAction A (m + 1))
    (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n))
    r s t z hz x y w

end SerrePositivity.EInfinity.IntervalCuts
