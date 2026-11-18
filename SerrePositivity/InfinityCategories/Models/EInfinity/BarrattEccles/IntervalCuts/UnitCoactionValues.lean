module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ZeroVertexValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoalgebraInterval
public import SerrePositivity.EInfinity.BarrattEccles.OperadAugmentation

/-!
模型。文献の定義との比較は後で
# 単位余作用の実際の零次生成元値

概要：Berger–Fresse §3.1 の単位余作用を BE augmentation と純粋テンソルで評価する。
方針：単位の零次を A と比較し、単位子の逆公式と単位冪の展開を使う。
規約：全 arity、任意の可換環、χ の augmentation は仮定しない。
使われ方：具体的な区間の端点・収縮の余代数射性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：単位の零次元は比較後のスカラー倍の一（BF §3.1）。
方針：singleObjXSelf の単射性と線形性で比較する。
規約：実際の単位複体の零次で述べる。
使われ方：augmentation の値を一定頂点テンソルのスカラーへ直す。 -/
lemma unit_zero_eq_smul (x : (𝟙_ (Complex A)).X 0) :
    x = (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom x •
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  apply (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).toLinearEquiv.injective
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom x =
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom x •
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))
  rw [map_smul, ModuleCat.hom_inv_apply, smul_eq_mul, mul_one]

/-- 概要：単位冪の零次の展開は比較後のスカラー倍の純粋テンソル（BF §3.1）。
方針：単位零次の一による表示を線形な単位冪展開へ送る。
規約：零重テンソルも含む。
使われ方：単位余作用の像を切断余作用の係数公式に合わせる。 -/
lemma unitPower_expand_zero (n : ℕ) (x : (𝟙_ (Complex A)).X 0) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv.f 0 x =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom x •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (𝟙_ (Complex A))
          ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) n := by
  have H := congrArg (fun y => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv.f 0 y)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unit_zero_eq_smul A x)
  simpa only [map_smul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor_unit] using! H

/-- 概要：単位上の左単位子は右因子が一の零次テンソルを縮約する（BF §3.1）。
方針：単位上の左右単位子の一致と右単位子の逆の生成元公式を使う。
規約：左因子は任意の単位零次元。
使われ方：単位余作用の augmentation 後の単位子を評価する。 -/
lemma unit_leftUnitor_right_one (x : (𝟙_ (Complex A)).X 0) :
    (λ_ (𝟙_ (Complex A))).hom.f 0
      (ιTensorObj (𝟙_ (Complex A)) (𝟙_ (Complex A)) 0 0 0 rfl
        (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) = x := by
  rw [unitors_equal, ← _root_.SerrePositivity.EInfinity.BarrattEccles.cochain_rightUnitor_inv_apply A]
  exact congrArg (fun f => f.f 0 x) (Iso.inv_hom_id (ρ_ (𝟙_ (Complex A))))

/-- 概要：BE の単位余作用の零次は augmentation 値の単位冪展開（BF §3.1）。
方針：係数の右テンソル作用を評価し、単位子の純粋テンソル公式を使う。
規約：BE の係数は任意の零次元、区間因子は単位の一。
使われ方：端点・収縮の保存図式の単位余作用側。 -/
lemma unitCoaction_zero_one (n : ℕ) (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X 0) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) n).f 0
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) 0 0 0 rfl
        (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv.f 0
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.complexAugmentation A n).f 0 x) := by
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv.f 0
    ((λ_ (𝟙_ (Complex A))).hom.f 0
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.complexAugmentation A n) ▷ (𝟙_ (Complex A))).f 0
        (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (𝟙_ (Complex A)) 0 0 0 rfl
          (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))))) = _
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply]
  exact congrArg (fun y => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv.f 0 y)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unit_leftUnitor_right_one A ((_root_.SerrePositivity.EInfinity.BarrattEccles.complexAugmentation A n).f 0 x))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
