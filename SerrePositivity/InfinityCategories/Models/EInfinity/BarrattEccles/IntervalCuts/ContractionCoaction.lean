module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.UnitCoactionValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.BarrattEcclesVertex

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：収縮の余作用保存は零次の任意係数と両頂点で成立（BF §3.1）。
方針：E の頂点値と収縮の反復テンソル値を単位余作用の生成元値へ照合する。
規約：任意の BE 零次係数、全 arity。
使われ方：全整数複体射の保存図式の唯一の非零次数。 -/
lemma contraction_coaction_zero_vertex (n : ℕ)
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X 0) (b : Fin 2) :
    (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n) ≫ _root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A) n).f 0
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) 0 0 0 rfl
        (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))) =
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n).f 0
        (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) 0 0 0 rfl
          (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))) := by
  change (_root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A) n).f 0
    (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n).f 0
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) 0 0 0 rfl
        (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)))) =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n).f 0
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A).f 0
        (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) 0 0 0 rfl
          (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoaction_zero_vertex, map_smul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction_power_vertex,
    SerrePositivity.DifferentialGraded.whiskerLeft_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction_vertex_eq,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unitCoaction_zero_one]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unitPower_expand_zero A n ((_root_.SerrePositivity.EInfinity.BarrattEccles.complexAugmentation A n).f 0 x),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor_unit]

/-- 概要：実際の正規化区間の収縮は全 E 余作用を保つ（BF §3.1）。
方針：全斉次テンソルで比較し、零次以外の標的と正次数の係数を零性で消す。
規約：nullary・全整数次数を含む実際の複体射の等式。
使われ方：CoalgebraInterval の contraction_coaction フィールド。 -/
lemma contraction_coaction (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n ≫ _root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A) n =
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n := by
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
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInput_linear_ext A
      intro b
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction_coaction_zero_vertex A n x b
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
        have hx := _root_.SerrePositivity.EInfinity.BarrattEccles.complex_eq_zero_of_positive A n 1 (by decide) x
        simp only [hx, map_zero]
      · apply ModuleCat.hom_ext
        apply TensorProduct.ext
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        have hy := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_eq_zero_of_other A s hs hs1 y
        simp only [hy, map_zero]
  · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unitPower_isZero_of_ne_zero A n t ht).eq_of_tgt _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
