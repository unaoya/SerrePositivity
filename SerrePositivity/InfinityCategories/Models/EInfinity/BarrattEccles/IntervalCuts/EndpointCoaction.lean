module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PositiveVertexValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.UnitCoactionValues

/-!
模型。文献の定義との比較は後で
# 正規化区間の両端点は E 余作用を保つ

概要：Berger–Fresse §3.1 の実際の両端点の余代数射性を全整数複体射として証明する。
方針：単位入力の零次集中、正鎖次数の頂点零性、零次の BE augmentation 比較を使う。
規約：全 arity・両端点、モデル構造と χ augmentation は仮定しない。
使われ方：具体的な E-coalgebra 区間の endpoint_coaction フィールド。
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

/-- 概要：単位の零次からの線形写像は一の像で決まる（BF §3.1）。
方針：任意の入力を比較後のスカラー倍の一として表す。
規約：標的は任意の A 加群。
使われ方：端点の保存則を単位の一だけで検証する。 -/
lemma unit_zero_linear_ext {M : Type u} [AddCommGroup M] [Module A M]
    {f g : (𝟙_ (Complex A)).X 0 →ₗ[A] M}
    (h : f ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
      g ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) : f = g := by
  apply LinearMap.ext
  intro x
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unit_zero_eq_smul A x, map_smul, map_smul, h]

/-- 概要：両端点の余作用保存は零次の任意係数と単位の一で成立（BF §3.1）。
方針：E の一定頂点値を単位余作用の展開と端点の反復テンソル値に照合する。
規約：両端点、全 arity。
使われ方：端点の全整数保存図式の零次条件。 -/
lemma endpoint_coaction_zero_one (b : Bool) (n : ℕ)
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X 0) :
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n).f 0
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) 0 0 0 rfl
        (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n ≫
        _root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) n).f 0
        (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) 0 0 0 rfl
          (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) := by
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n).f 0
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b).f 0
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) 0 0 0 rfl
        (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))) =
    (_root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) n).f 0
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n).f 0
        (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) 0 0 0 rfl
          (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))))
  rw [SerrePositivity.DifferentialGraded.whiskerLeft_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_zero_apply, one_smul,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoaction_zero_vertex, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unitCoaction_zero_one,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unitPower_expand_zero A n ((_root_.SerrePositivity.EInfinity.BarrattEccles.complexAugmentation A n).f 0 x), map_smul,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor_unit, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_power_unit]

/-- 概要：両端点の正鎖次数の余作用保存は両辺の零性による（BF §3.1）。
方針：E の頂点値零と単位冪の非零整数次数の零性を使う。
規約：全 arity、任意の正鎖次数と BE 係数。
使われ方：端点の全整数保存図式の負次数条件。 -/
lemma endpoint_coaction_positive_one (b : Bool) (n d : ℕ) (hd : 0 < d)
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X (-(d : ℤ))) :
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n).f (-(d : ℤ))
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) (-(d : ℤ)) 0 (-(d : ℤ))
        (by omega) (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n ≫
        _root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) n).f (-(d : ℤ))
        (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) (-(d : ℤ)) 0 (-(d : ℤ))
          (by omega) (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) := by
  have hz : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n).f (-(d : ℤ)) = 0 :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unitPower_isZero_of_ne_zero A n (-(d : ℤ)) (by omega)).eq_of_tgt _ _
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n).f (-(d : ℤ))
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b).f (-(d : ℤ))
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) (-(d : ℤ)) 0 (-(d : ℤ))
        (by omega) (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))) =
    (_root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) n).f (-(d : ℤ))
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n).f (-(d : ℤ))
        (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) (-(d : ℤ)) 0 (-(d : ℤ))
          (by omega) (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))))
  rw [SerrePositivity.DifferentialGraded.whiskerLeft_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_zero_apply, one_smul,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoaction_positive_vertex A n d hd, hz]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]

/-- 概要：端点の正鎖次数保存則を任意の同じ全整数次数で読む（BF §3.1）。
方針：全次数の等式を先に消去して既存の生成元比較へ戻す。
規約：係数次数と全次数を独立に指定する。
使われ方：テンソル外延性の r+0 という次数表示を扱う。 -/
lemma endpoint_coaction_positive_one_at (b : Bool) (n d : ℕ) (hd : 0 < d)
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X (-(d : ℤ))) (t : ℤ) (ht : -(d : ℤ) = t) :
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n).f t
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) (-(d : ℤ)) 0 t
        (by omega) (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n ≫
        _root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) n).f t
        (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) (-(d : ℤ)) 0 t
          (by omega) (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) := by
  subst t
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_coaction_positive_one A b n d hd x

/-- 概要：実際の正規化区間の両端点は全 E 余作用を保つ（BF §3.1）。
方針：全斉次テンソルで比較し、単位入力の一と係数の非正次数へ帰着する。
規約：nullary・全整数次数を含む実際の複体射の等式。
使われ方：CoalgebraInterval の endpoint_coaction フィールド。 -/
lemma endpoint_coaction (b : Bool) (n : ℕ) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n ≫
          _root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) n := by
  apply tensorHom_ext
  intro r s t h
  by_cases hs : s = 0
  · subst s
    simp only [add_zero] at h
    subst t
    by_cases hr : 0 < r
    · apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      have hx := _root_.SerrePositivity.EInfinity.BarrattEccles.complex_eq_zero_of_positive A n r hr x
      simp only [hx, map_zero]
    · obtain ⟨d, rfl⟩ : ∃ d : ℕ, r = -(d : ℤ) := ⟨(-r).toNat, by omega⟩
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unit_zero_linear_ext A
      by_cases hd : d = 0
      · subst d
        exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_coaction_zero_one A b n x
      · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_coaction_positive_one_at A b n d (by omega) x _ (by omega)
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    have hy : y = 0 := by
      let _ := ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) s hs)
      exact Subsingleton.elim _ _
    simp only [hy, map_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
