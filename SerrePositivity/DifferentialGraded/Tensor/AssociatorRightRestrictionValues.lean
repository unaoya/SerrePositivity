module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestrictionComponents

/-! # 外側右制限と結合子の、各値の複体における可換square

## 概要
外側右制限と結合子の、各値の複体における可換square。

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
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "RP" => Bimodule.rightRestriction A B D C F P₀

/-- 固定した成分関数によるchain mapとして、右制限と結合子は可換。 -/
lemma associatorValueHom_rightRestriction (d : D) (t : T) :
    associatorValueHom A D C E T RP Q₀ R₀ d t ≫
      composeRightRestrictionValueHom A B D C T F P₀ (compose A C E T Q₀ R₀) d t =
    composeValueHom A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d t ≫
      composeRightRestrictionValueHom A B D E T F (compose A B C E P₀ Q₀) R₀ d t ≫
      associatorValueHom A B C E T P₀ Q₀ R₀ (F.obj d) t := by
  apply Cochain.ofHom_injective
  apply associatorLeft_cochain_element_ext A D C E T RP Q₀ R₀ d t
  intro c e k r s i m n hi hm hn τ q p
  simp only [add_zero] at hn
  cases hn
  simp only [Cochain.ofHom_v]
  change composeRightRestrictionValueComponent A B D C T F P₀ (compose A C E T Q₀ R₀) d t m
      (associatorValueComponent A D C E T RP Q₀ R₀ d t m
        (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hm)) =
    associatorValueComponent A B C E T P₀ Q₀ R₀ (F.obj d) t m
      (composeRightRestrictionValueComponent A B D E T F (compose A B C E P₀ Q₀) R₀ d t m
        (composeMapComponent A D E T (composeRightRestrictionIso A B D C E F P Q).hom
          (𝟙 R) d t m (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hm)))
  exact (associatorRightRestriction_left_component_element A B D C E T F P Q R
    d c e t (l := k + r) τ q p hi rfl hm).trans
    (associatorRightRestriction_right_component_element A B D C E T F P Q R
      d c e t (l := k + r) τ q p hi rfl hm).symm

/-- 外側右制限の二段階比較と結合子は、各値の複体で可換。 -/
lemma associatorValue_rightRestriction (d : D) (t : T) :
    (associatorValueIso A D C E T RP Q₀ R₀ d t).hom ≫
      (composeRightRestrictionValueIso A B D C T F P₀ (compose A C E T Q₀ R₀) d t).hom =
    composeValueMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d t ≫
      (composeRightRestrictionValueIso A B D E T F (compose A B C E P₀ Q₀) R₀ d t).hom ≫
      (associatorValueIso A B C E T P₀ Q₀ R₀ (F.obj d) t).hom := by
  simpa only [associatorValueHom_eq, composeValueHom_eq, composeRightRestrictionValueHom_eq]
    using associatorValueHom_rightRestriction A B D C E T F P Q R d t

end SerrePositivity.DifferentialGraded.BimoduleTensor
