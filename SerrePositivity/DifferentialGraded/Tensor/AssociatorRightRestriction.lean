module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestrictionValues

/-! # 外側右作用の制限は通常のbimodule結合子を保つ

## 概要
外側右作用の制限は通常のbimodule結合子を保つ。

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
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "RP" => Bimodule.rightRestriction A B D C F P₀
local notation "PQ" => BimoduleCategory.of A B E (compose A B C E P₀ Q₀)
local notation "QR" => BimoduleCategory.of A C T (compose A C E T Q₀ R₀)

/-- 外側右制限の二段階比較と通常結合子の可換square。終端のsmallness・flatnessは不要。 -/
lemma associatorIso_rightRestriction :
    (associatorIso A D C E T RP Q₀ R₀).hom ≫
      (composeRightRestrictionIso A B D C T F P QR).hom =
    composeMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) ≫
      (composeRightRestrictionIso A B D E T F PQ R).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D T F).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom := by
  apply BimoduleCategory.value_hom_ext A D T
  intro d t
  have hrestrict : (BimoduleCategory.valueEvaluation A D T d t).map
      ((BimoduleCategory.middleRightRestrictionFunctor A B D T F).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom) =
      (BimoduleCategory.valueEvaluation A B T (F.obj d) t).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom :=
    BimoduleCategory.middleRightRestrictionMap_value_eval A B D T F _ d t
  have h₁ := associatorIso_hom_value_eval A D C E T RP Q₀ R₀ d t
  have h₂ := composeRightRestrictionIso_hom_value A B D C T F P QR d t
  have h₃ := composeMap_value_eval A D E T
    (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d t
  have h₄ := composeRightRestrictionIso_hom_value A B D E T F PQ R d t
  have h₅ := associatorIso_hom_value_eval A B C E T P₀ Q₀ R₀ (F.obj d) t
  simp only [CategoryTheory.Functor.map_comp]
  rw [h₁, h₂, h₃, h₄, hrestrict, h₅]
  exact associatorValue_rightRestriction A B D C E T F P Q R d t

end SerrePositivity.DifferentialGraded.BimoduleTensor
