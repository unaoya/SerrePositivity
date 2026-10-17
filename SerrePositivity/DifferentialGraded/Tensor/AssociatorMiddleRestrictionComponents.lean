module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestrictionPaths
public import SerrePositivity.DifferentialGraded.Tensor.MiddleRestrictionValueHom
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleValueHom
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHom

/-! # 第一中間圏の制限と結合子の固定成分関数計算

## 概要
第一中間圏の制限と結合子の固定成分関数計算。

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

lemma associatorMiddleRestriction_left_component_element (b : B) (d : D) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    middleRestrictionValueComponent A B C D T F P₀ (compose A C E T Q₀ R₀) b t n
        (composeMapComponent A B D T (𝟙 LPc)
          (composeRightRestrictionIso A C D E T F Q R).hom b t n
          (associatorValueComponent A B D E T LP RQ R₀ b t n
            (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl (by omega) := by
  have h := associatorMiddleRestriction_left_path_element A B C D E T F P Q R
    b d e t τ q p hi hl hn
  rw [middleRestrictionValueComponent_eq, composeMapComponent_eq, associatorValueComponent_eq]
  exact h

lemma associatorMiddleRestriction_right_component_element (b : B) (d : D) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E T P₀ Q₀ R₀ b t n
        (composeMapComponent A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀)
          (𝟙 R) b t n (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl (by omega) := by
  have h := associatorMiddleRestriction_right_path_element A B C D E T F P Q R
    b d e t τ q p hi hl hn
  rw [associatorValueComponent_eq, composeMapComponent_eq]
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
