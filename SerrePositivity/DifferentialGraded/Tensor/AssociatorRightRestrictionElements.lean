module
public import SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestriction
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorIsoElements
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorDegreeExt
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleValueElements
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor

/-! # 外側右制限比較の三重斉次生成元上の計算

## 概要
外側右制限比較の三重斉次生成元上の計算。

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

/-- 右括弧の生成元に外側右制限比較を作用させても、三つの成分と次数を保つ。 -/
lemma composeRightRestriction_rightElement (d : D) (c : C) (e : E) (t : T)
    {k r s l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hl : k + r = l) (hn : l + s = n) :
    (composeRightRestrictionValueIso A B D C T F P₀ (compose A C E T Q₀ R₀) d t).hom.f n
        (associatorRightElement A D C E T RP Q₀ R₀ d c e t τ q p hl hn) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl hn := by
  exact composeRightRestrictionValueIso_element A B D C T F P₀ (compose A C E T Q₀ R₀)
    d c t hn (BalancedTensor.element A E ((R₀).rightAt t) ((Q₀).leftAt c) e τ q hl) p

/-- 内側合成の右制限比較を前因子へ作用させた、左括弧の生成元の計算。 -/
lemma composeValueMap_rightRestriction_leftElement (d : D) (c : C) (e : E) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hn : k + i = n) :
    (composeValueMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d t).f n
        (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn) =
    BalancedTensor.element A E ((R₀).rightAt t)
      ((Bimodule.rightRestriction A B D E F (compose A B C E P₀ Q₀)).leftAt d) e τ
      (BalancedTensor.element A C ((Q₀).rightAt e) ((P₀).leftAt (F.obj d)) c q p hi) hn := by
  have h := composeValueMap_element A D E T
    (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d e t τ
    (BalancedTensor.element A C ((Q₀).rightAt e) ((RP).leftAt d) c q p hi) hn
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply,
    composeRightRestrictionIso_hom_value] at h
  erw [composeRightRestrictionValueIso_element A B D C E F P₀ Q₀ d c e hi q p] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
