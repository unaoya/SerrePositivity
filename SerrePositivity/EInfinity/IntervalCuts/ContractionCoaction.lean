module

public import SerrePositivity.EInfinity.IntervalCuts.UnitCoactionValues
public import SerrePositivity.EInfinity.IntervalCuts.BarrattEcclesVertex

/-!
# 正規化区間の収縮は E 余作用を保つ

概要：Berger–Fresse §3.1 の実際の収縮の余代数射性を全整数複体射として証明する。
方針：単位冪の零次集中で他の全次数を消し、零次は TR と BE augmentation を比較する。
規約：全 arity、任意の可換環、モデル構造と χ augmentation は仮定しない。
使われ方：具体的な E-coalgebra 区間の contraction_coaction フィールド。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：収縮の余作用保存は零次の任意係数と両頂点で成立（BF §3.1）。
方針：E の頂点値と収縮の反復テンソル値を単位余作用の生成元値へ照合する。
規約：任意の BE 零次係数、全 arity。
使われ方：全整数複体射の保存図式の唯一の非零次数。 -/
lemma contraction_coaction_zero_vertex (n : ℕ)
    (x : (BarrattEccles.complex A n).X 0) (b : Fin 2) :
    (((barrattEcclesCoalgebra A).coaction n) ≫ TensorPowers.map (contraction A) n).f 0
      (ιTensorObj (BarrattEccles.complex A n) (interval A) 0 0 0 rfl
        (x ⊗ₜ[A] faceVector A (vertex b))) =
      (((BarrattEccles.complex A n) ◁ contraction A) ≫
        Operad.unitCoaction (BarrattEccles.augmentation A) n).f 0
        (ιTensorObj (BarrattEccles.complex A n) (interval A) 0 0 0 rfl
          (x ⊗ₜ[A] faceVector A (vertex b))) := by
  change (TensorPowers.map (contraction A) n).f 0
    (((barrattEcclesCoalgebra A).coaction n).f 0
      (ιTensorObj (BarrattEccles.complex A n) (interval A) 0 0 0 rfl
        (x ⊗ₜ[A] faceVector A (vertex b)))) =
    (Operad.unitCoaction (BarrattEccles.augmentation A) n).f 0
      (((BarrattEccles.complex A n) ◁ contraction A).f 0
        (ιTensorObj (BarrattEccles.complex A n) (interval A) 0 0 0 rfl
          (x ⊗ₜ[A] faceVector A (vertex b))))
  rw [barrattEcclesCoaction_zero_vertex, map_smul, contraction_power_vertex,
    SerrePositivity.DifferentialGraded.whiskerLeft_apply, contraction_vertex_eq,
    unitCoaction_zero_one]
  rw [unitPower_expand_zero A n ((BarrattEccles.complexAugmentation A n).f 0 x),
    zeroTensor_unit]

/-- 概要：実際の正規化区間の収縮は全 E 余作用を保つ（BF §3.1）。
方針：全斉次テンソルで比較し、零次以外の標的と正次数の係数を零性で消す。
規約：nullary・全整数次数を含む実際の複体射の等式。
使われ方：CoalgebraInterval の contraction_coaction フィールド。 -/
lemma contraction_coaction (n : ℕ) :
    (barrattEcclesCoalgebra A).coaction n ≫ TensorPowers.map (contraction A) n =
      ((BarrattEccles.operad A).arity n ◁ contraction A) ≫
        Operad.unitCoaction (BarrattEccles.augmentation A) n := by
  apply tensorHom_ext
  intro r s t h
  by_cases ht : t = 0
  · subst t
    by_cases hs : s = 0
    · subst s
      have hr : r = 0 := by omega
      subst r
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply vertexInput_linear_ext A
      intro b
      exact contraction_coaction_zero_vertex A n x b
    · by_cases hs1 : s = -1
      · subst s
        have hr : r = 1 := by omega
        subst r
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        have hx := BarrattEccles.complex_eq_zero_of_positive A n 1 (by decide) x
        simp only [hx, map_zero]
      · apply ModuleCat.hom_ext
        apply TensorProduct.ext
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        have hy := interval_eq_zero_of_other A s hs hs1 y
        simp only [hy, map_zero]
  · exact (unitPower_isZero_of_ne_zero A n t ht).eq_of_tgt _ _

end SerrePositivity.EInfinity.IntervalCuts
