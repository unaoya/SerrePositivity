module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestriction
public import SerrePositivity.DifferentialGraded.Tensor.ComposeLeftRestriction

/-! # 第二中間圏の制限と三重斉次生成元の計算

## 概要
第二中間圏の制限と三重斉次生成元の計算。

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
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LQ" => Bimodule.leftRestriction A C E D F Q₀
local notation "RR" => Bimodule.rightRestriction A E D T F R₀
local notation "RRc" => BimoduleCategory.of A D T RR

lemma composeValueMap_leftRestriction_leftElement (b : B) (c : C) (d : D) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    (composeValueMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
        (𝟙 RRc) b t).f n
        (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn) =
      BalancedTensor.element A D ((RR).rightAt t)
        ((Bimodule.leftRestriction A B E D F (compose A B C E P₀ Q₀)).leftAt b) d τ
        (BalancedTensor.element A C ((Q₀).rightAt (F.obj d)) ((P₀).leftAt b) c q p hi) hn := by
  have h := composeValueMap_element A B D T
    (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) b d t τ
    (BalancedTensor.element A C ((LQ).rightAt d) ((P₀).leftAt b) c q p hi) hn
  simp only [composeLeftRestrictionIso_hom_value, CategoryTheory.Functor.map_id,
    HomologicalComplex.id_f, ModuleCat.id_apply] at h
  exact h

/-- 左制限比較と中間比較の二段階合成は、元の左括弧の生成元になる。 -/
lemma middleRestriction_leftElement (b : B) (c : C) (d : D) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    (middleRestrictionComparisonValue A B E D T F (compose A B C E P₀ Q₀) R₀ b t).f n
        ((composeValueMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
          (𝟙 RRc) b t).f n
          (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn)) =
      associatorLeftElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hi hn := by
  have h₁ := composeValueMap_leftRestriction_leftElement A B C D E T F P Q R
    b c d t τ q p hi hn
  have h₂ := middleRestrictionComparisonValue_element A B E D T F
    (compose A B C E P₀ Q₀) R₀ b t d τ
    (BalancedTensor.element A C ((Q₀).rightAt (F.obj d)) ((P₀).leftAt b) c q p hi) hn
  exact (congrArg (fun x => (middleRestrictionComparisonValue A B E D T F
    (compose A B C E P₀ Q₀) R₀ b t).f n x) h₁).trans h₂

lemma composeValueMap_middleRestriction_rightElement (b : B) (c : C) (d : D) (t : T)
    {k r s l n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hl : k + r = l) (hn : l + s = n) :
    (composeValueMap A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
        b t).f n (associatorRightElement A B C D T P₀ LQ RR b c d t τ q p hl hn) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl hn := by
  have h := composeValueMap_element A B C T (𝟙 P)
    (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b c t
    (BalancedTensor.element A D ((RR).rightAt t) ((LQ).leftAt c) d τ q hl) p hn
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply,
    middleRestrictionComparisonMap_value_eval] at h
  erw [middleRestrictionComparisonValue_element A C E D T F Q₀ R₀ c t d τ q hl] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
