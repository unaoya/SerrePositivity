module
public import SerrePositivity.DifferentialGraded.Tensor.ComposeLeftRestriction
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation

/-! # 外側左作用の制限は通常のbimodule結合子を保つ

## 概要
外側左作用の制限は通常のbimodule結合子を保つ。

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
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] (D : Type s) [DGCategory A D]
  (G : DGFunctor A D T) (P : BimoduleCategory A B C)
  (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LR" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A E T D G) R
local notation "PQ" => BimoduleCategory.of A B E (compose A B C E P₀ Q₀)
local notation "QR" => BimoduleCategory.of A C T (compose A C E T Q₀ R₀)

/-- 内側合成の左制限比較を後因子へ作用させても、各値での射は恒等である。 -/
lemma composeMap_leftRestrictionIso_value (b : B) (d : D) :
    (BimoduleCategory.valueEvaluation A B D b d).map
      (composeMap A B C D (𝟙 P) (composeLeftRestrictionIso A C E T D G Q R).hom) =
      𝟙 _ := by
  rw [composeMap_value_eval]
  apply BalancedTensor.hom_ext A C
    ((compose A C E D Q₀ (BimoduleCategory.underlying A E D LR)).rightAt d) ((P₀).leftAt b)
  intro c
  erw [Category.comp_id]
  have h := ι_composeValueMap A B C D (𝟙 P)
    (composeLeftRestrictionIso A C E T D G Q R).hom b c d
  simp only [composeLeftRestrictionIso_hom_value, CategoryTheory.Functor.map_id,
    tensorHom_id, id_whiskerRight, Category.id_comp] at h
  exact h

/-- 結合子の各値は、後因子の外側左作用を制限してから評価しても変わらない。 -/
lemma associatorValue_leftRestriction (b : B) (d : D) :
    (associatorValueIso A B C E D P₀ Q₀ (BimoduleCategory.underlying A E D LR) b d).hom =
      (associatorValueIso A B C E T P₀ Q₀ R₀ b (G.obj d)).hom := by
  unfold associatorValueIso
  rfl

/-- 外側左制限の二段階比較と通常結合子の可換square。終端のsmallness・flatnessは不要。 -/
lemma associatorIso_leftRestriction :
    (associatorIso A B C E D P₀ Q₀ (BimoduleCategory.underlying A E D LR)).hom ≫
      composeMap A B C D (𝟙 P) (composeLeftRestrictionIso A C E T D G Q R).hom ≫
      (composeLeftRestrictionIso A B C T D G P QR).hom =
    (composeLeftRestrictionIso A B E T D G PQ R).hom ≫
      (BimoduleCategory.middleLeftRestrictionFunctor A B T D G).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom := by
  apply BimoduleCategory.value_hom_ext A B D
  intro b d
  have h₁ := associatorIso_hom_value_eval A B C E D P₀ Q₀
    (BimoduleCategory.underlying A E D LR) b d
  have h₂ := composeMap_leftRestrictionIso_value A B C E T D G P Q R b d
  have h₃ := composeLeftRestrictionIso_hom_value A B C T D G P QR b d
  have h₄ := composeLeftRestrictionIso_hom_value A B E T D G PQ R b d
  have h₅ : (BimoduleCategory.valueEvaluation A B D b d).map
      ((BimoduleCategory.middleLeftRestrictionFunctor A B T D G).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom) =
      (BimoduleCategory.valueEvaluation A B T b (G.obj d)).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom := rfl
  have h₆ := associatorIso_hom_value_eval A B C E T P₀ Q₀ R₀ b (G.obj d)
  simp only [CategoryTheory.Functor.map_comp]
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  erw [Category.comp_id, Category.id_comp]
  exact associatorValue_leftRestriction A B C E T D G P Q R b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
