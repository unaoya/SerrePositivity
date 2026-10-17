module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestrictionElements

/-! # 第一中間圏の制限と結合子の二経路の計算

## 概要
第一中間圏の制限と結合子の二経路の計算。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LP" => Bimodule.leftRestriction A B C D F P₀
local notation "RQ" => Bimodule.rightRestriction A C D E F Q₀
local notation "LPc" => BimoduleCategory.of A B D LP

/-- 右制限比較と中間比較を続けると、元の右括弧の三重生成元になる。 -/
lemma middleRestriction_rightElement (b : B) (d : D) (e : E) (t : T)
    {k r s l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hl : k + r = l) (hn : l + s = n) :
    (middleRestrictionComparisonValue A B C D T F P₀ (compose A C E T Q₀ R₀) b t).f n
        ((composeValueMap A B D T (𝟙 LPc)
          (composeRightRestrictionIso A C D E T F Q R).hom b t).f n
          (associatorRightElement A B D E T LP RQ R₀ b d e t τ q p hl hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl hn := by
  have h₁ := composeValueMap_rightRestriction_rightElement A B C D E T F P Q R
    b d e t τ q p hl hn
  have h₂ := middleRestrictionComparisonValue_element A B C D T F P₀
    (compose A C E T Q₀ R₀) b t d
    (BalancedTensor.element A E ((R₀).rightAt t) ((Q₀).leftAt (F.obj d)) e τ q hl) p hn
  exact (congrArg (fun x => (middleRestrictionComparisonValue A B C D T F P₀
    (compose A C E T Q₀ R₀) b t).f n x) h₁).trans h₂

/-- 結合子、内側右比較、中間比較を続ける経路の生成元計算。 -/
lemma associatorMiddleRestriction_left_path_element (b : B) (d : D) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (middleRestrictionComparisonValue A B C D T F P₀ (compose A C E T Q₀ R₀) b t).f n
        ((composeValueMap A B D T (𝟙 LPc)
          (composeRightRestrictionIso A C D E T F Q R).hom b t).f n
          ((associatorValueIso A B D E T LP RQ R₀ b t).hom.f n
            (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl (by omega) := by
  have h₁ := associatorValueIso_hom_element A B D E T LP RQ R₀ b d e t τ q p hi hl hn
  have h₂ := middleRestriction_rightElement A B C D E T F P Q R b d e t τ q p hl
    (show l + s = n by omega)
  exact (congrArg (fun x => (middleRestrictionComparisonValue A B C D T F P₀
    (compose A C E T Q₀ R₀) b t).f n
    ((composeValueMap A B D T (𝟙 LPc)
      (composeRightRestrictionIso A C D E T F Q R).hom b t).f n x)) h₁).trans h₂

/-- 内側の中間比較の後で結合子を適用する経路も、同じ三重生成元になる。 -/
lemma associatorMiddleRestriction_right_path_element (b : B) (d : D) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom.f n
        ((composeValueMap A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀)
          (𝟙 R) b t).f n
          (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl (by omega) := by
  have h₁ := composeValueMap_middleRestriction_leftElement A B C D E T F P Q R
    b d e t τ q p hi hn
  have h₂ := associatorValueIso_hom_element A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hi hl hn
  exact (congrArg (fun x => (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom.f n x) h₁).trans h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
