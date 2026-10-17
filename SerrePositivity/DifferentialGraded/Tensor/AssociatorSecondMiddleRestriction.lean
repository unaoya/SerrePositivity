module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestrictionValues

/-! # 第二中間圏の制限は通常のbimodule結合子と可換

## 概要
第二中間圏の制限は通常のbimodule結合子と可換。

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
open CategoryTheory HomologicalComplex CochainComplex HomComplex
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

/-- 後二因子の間の圏を制限する比較と、三因子の通常結合子の可換square。 -/
lemma associatorIso_secondMiddleRestriction :
    composeMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) ≫
      middleRestrictionComparisonMap A B E D T F (compose A B C E P₀ Q₀) R₀ ≫
      (associatorIso A B C E T P₀ Q₀ R₀).hom =
    (associatorIso A B C D T P₀ LQ RR).hom ≫
      composeMap A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀) := by
  apply BimoduleCategory.value_hom_ext A B T
  intro b t
  have h₁ := composeMap_value_eval A B D T
    (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) b t
  have h₂ := middleRestrictionComparisonMap_value_eval A B E D T F
    (compose A B C E P₀ Q₀) R₀ b t
  have h₃ := associatorIso_hom_value_eval A B C E T P₀ Q₀ R₀ b t
  have h₄ := associatorIso_hom_value_eval A B C D T P₀ LQ RR b t
  have h₅ := composeMap_value_eval A B C T (𝟙 P)
    (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b t
  simp only [CategoryTheory.Functor.map_comp]
  rw [h₁, h₂, h₃, h₄, h₅]
  exact associatorValue_secondMiddleRestriction A B C D E T F P Q R b t

end SerrePositivity.DifferentialGraded.BimoduleTensor
