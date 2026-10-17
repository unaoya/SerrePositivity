module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestrictionComponents

/-! # 第一中間圏の制限と結合子の値での可換square

## 概要
第一中間圏の制限と結合子の値での可換square。

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
open CategoryTheory CochainComplex HomComplex
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

lemma associatorValueHom_middleRestriction (b : B) (t : T) :
    associatorValueHom A B D E T LP RQ R₀ b t ≫
      composeValueHom A B D T (𝟙 LPc)
        (composeRightRestrictionIso A C D E T F Q R).hom b t ≫
      middleRestrictionValueHom A B C D T F P₀ (compose A C E T Q₀ R₀) b t =
    composeValueHom A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) b t ≫
      associatorValueHom A B C E T P₀ Q₀ R₀ b t := by
  apply Cochain.ofHom_injective
  apply associatorLeft_cochain_element_ext A B D E T LP RQ R₀ b t
  intro d e k r s i m n hi hm hn τ q p
  simp only [add_zero] at hn
  cases hn
  simp only [Cochain.ofHom_v]
  change middleRestrictionValueComponent A B C D T F P₀ (compose A C E T Q₀ R₀) b t m
      (composeMapComponent A B D T (𝟙 LPc)
        (composeRightRestrictionIso A C D E T F Q R).hom b t m
        (associatorValueComponent A B D E T LP RQ R₀ b t m
          (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hm))) =
    associatorValueComponent A B C E T P₀ Q₀ R₀ b t m
      (composeMapComponent A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀)
        (𝟙 R) b t m (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hm))
  exact (associatorMiddleRestriction_left_component_element A B C D E T F P Q R
    b d e t (l := k + r) τ q p hi rfl hm).trans
    (associatorMiddleRestriction_right_component_element A B C D E T F P Q R
      b d e t (l := k + r) τ q p hi rfl hm).symm

lemma associatorValue_middleRestriction (b : B) (t : T) :
    (associatorValueIso A B D E T LP RQ R₀ b t).hom ≫
      composeValueMap A B D T (𝟙 LPc)
        (composeRightRestrictionIso A C D E T F Q R).hom b t ≫
      middleRestrictionComparisonValue A B C D T F P₀ (compose A C E T Q₀ R₀) b t =
    composeValueMap A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) b t ≫
      (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom := by
  simpa only [associatorValueHom_eq, composeValueHom_eq, middleRestrictionValueHom_eq]
    using associatorValueHom_middleRestriction A B C D E T F P Q R b t

end SerrePositivity.DifferentialGraded.BimoduleTensor
