module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ContractionValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorDegreeTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.UnitPowers
public import SerrePositivity.EInfinity.BarrattEccles.Unitors

/-!
模型。文献の定義との比較は後で
# 零次生成元の反復テンソルと単位冪

概要：Berger–Fresse §3.1 の端点・収縮の出力を実際の反復テンソルで比較する。
方針：零次純粋テンソルを再帰的に作り、射の自然性と単位冪の標準同型を評価する。
規約：零重テンソルを含み、任意の非有界複体の零次元を使う。
使われ方：単位余作用と一定頂点出力の比較。
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

attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：零次元の同じ元の右括弧反復テンソル（BF §3.1）。
方針：零重は単位の一、後続は零次のテンソル包含で連結する。
規約：元の閉性を要求しない。
使われ方：端点の一定頂点テンソルと単位出力の共通表示。 -/
def zeroTensor (K : Complex A) (x : K.X 0) : ∀ n : ℕ, (power K n).X 0
  | 0 => (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)
  | n + 1 => ιTensorObj K (power K n) 0 0 0 rfl (x ⊗ₜ[A] zeroTensor K x n)

/-- 概要：零次の反復純粋テンソルは複体射に自然（BF §3.1）。
方針：各 tensorHom を左右の作用として評価して長さで帰納する。
規約：零重テンソルを含む。
使われ方：端点と収縮の反復テンソルの生成元値。 -/
lemma map_zeroTensor {K L : Complex A} (f : K ⟶ L) (x : K.X 0) (n : ℕ) :
    (_root_.SerrePositivity.TensorPowers.map f n).f 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A K x n) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A L (f.f 0 x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (f ⊗ₘ _root_.SerrePositivity.TensorPowers.map f n).f 0
      (ιTensorObj K (power K n) 0 0 0 rfl (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A K x n)) = _
    rw [tensorHom_def]
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    rw [SerrePositivity.DifferentialGraded.whiskerRight_apply,
      SerrePositivity.DifferentialGraded.whiskerLeft_apply, ih]
    rfl

/-- 概要：単位の一の反復テンソルは標準の単位冪の展開（BF §3.1）。
方針：単位冪同型の再帰と左単位子の逆の生成元公式を使う。
規約：零次の単位元は singleObjXSelf の逆で指定する。
使われ方：augmentation に付随する単位余作用を純粋テンソルとして読む。 -/
lemma zeroTensor_unit (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (𝟙_ (Complex A))
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) n =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv.f 0
          ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change _ = ((𝟙_ (Complex A)) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv).f 0
      ((λ_ (𝟙_ (Complex A))).inv.f 0
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))
    rw [_root_.SerrePositivity.EInfinity.BarrattEccles.cochain_leftUnitor_inv_apply,
      SerrePositivity.DifferentialGraded.whiskerLeft_apply, ← ih]
    rfl

/-- 概要：区間の一定頂点テンソルは零次反復テンソル（BF §2.2.6・§3.1）。
方針：面テンソルの指定整数次数の再帰式を全て零次へ特殊化する。
規約：元の零・一の両頂点と零重テンソル。
使われ方：切断の頂点値を端点の反復テンソルに照合する。 -/
lemma zeroTensor_vertex (b : Fin 2) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) 0 (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree]; rfl) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_succ A n (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) 0 0 0 rfl
      (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree]; rfl) rfl]
    change ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) 0 0 0 rfl
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) n) = _
    rw [ih]
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
