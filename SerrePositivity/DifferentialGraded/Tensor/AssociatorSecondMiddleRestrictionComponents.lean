module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestrictionPaths
public import SerrePositivity.DifferentialGraded.Tensor.MiddleRestrictionValueHom
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleValueHom
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHom

/-! # 第二中間圏の制限と結合子の固定成分計算

## 概要
第二中間圏の制限と結合子の固定成分計算。

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

lemma associatorSecondMiddleRestriction_left_component_element
    (b : B) (c : C) (d : D) (t : T) {k r s i l n : ℤ}
    (τ : ((R₀).value (F.obj d) t).X k) (q : ((Q₀).value c (F.obj d)).X r)
    (p : ((P₀).value b c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E T P₀ Q₀ R₀ b t n
        (middleRestrictionValueComponent A B E D T F (compose A B C E P₀ Q₀) R₀ b t n
          (composeMapComponent A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
            (𝟙 RRc) b t n
            (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl (by omega) := by
  have h := associatorSecondMiddleRestriction_left_path_element A B C D E T F P Q R
    b c d t τ q p hi hl hn
  rw [associatorValueComponent_eq, middleRestrictionValueComponent_eq, composeMapComponent_eq]
  exact h

lemma associatorSecondMiddleRestriction_right_component_element
    (b : B) (c : C) (d : D) (t : T) {k r s i l n : ℤ}
    (τ : ((R₀).value (F.obj d) t).X k) (q : ((Q₀).value c (F.obj d)).X r)
    (p : ((P₀).value b c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    composeMapComponent A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
        b t n (associatorValueComponent A B C D T P₀ LQ RR b t n
          (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl (by omega) := by
  have h := associatorSecondMiddleRestriction_right_path_element A B C D E T F P Q R
    b c d t τ q p hi hl hn
  rw [composeMapComponent_eq, associatorValueComponent_eq]
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
