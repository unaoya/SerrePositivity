module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestrictionElements
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleMap

/-! # 第一中間圏の制限と結合子の斉次生成元計算 -/
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
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LP" => Bimodule.leftRestriction A B C D F P₀
local notation "RQ" => Bimodule.rightRestriction A C D E F Q₀
local notation "LPc" => BimoduleCategory.of A B D LP

/-- 内側の中間比較を作用させると、元の左括弧の三重生成元になる。 -/
lemma composeValueMap_middleRestriction_leftElement (b : B) (d : D) (e : E) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hn : k + i = n) :
    (composeValueMap A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀)
        (𝟙 R) b t).f n
        (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn) =
      associatorLeftElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hi hn := by
  have h := composeValueMap_element A B E T
    (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) b e t τ
    (BalancedTensor.element A D ((RQ).rightAt e) ((LP).leftAt b) d q p hi) hn
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply,
    middleRestrictionComparisonMap_value_eval] at h
  erw [middleRestrictionComparisonValue_element A B C D E F P₀ Q₀ b e d q p hi] at h
  exact h

/-- 右括弧の内側の右制限比較は、三成分を保って後の中間比較の生成元を与える。 -/
lemma composeValueMap_rightRestriction_rightElement (b : B) (d : D) (e : E) (t : T)
    {k r s l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hl : k + r = l) (hn : l + s = n) :
    (composeValueMap A B D T (𝟙 LPc)
        (composeRightRestrictionIso A C D E T F Q R).hom b t).f n
        (associatorRightElement A B D E T LP RQ R₀ b d e t τ q p hl hn) =
      BalancedTensor.element A D
        ((Bimodule.rightRestriction A C D T F (compose A C E T Q₀ R₀)).rightAt t)
        ((LP).leftAt b) d
        (BalancedTensor.element A E ((R₀).rightAt t) ((Q₀).leftAt (F.obj d)) e τ q hl) p hn := by
  have h := composeValueMap_element A B D T (𝟙 LPc)
    (composeRightRestrictionIso A C D E T F Q R).hom b d t
    (BalancedTensor.element A E ((R₀).rightAt t) ((RQ).leftAt d) e τ q hl) p hn
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply,
    composeRightRestrictionIso_hom_value] at h
  erw [composeRightRestrictionValueIso_element A C D E T F Q₀ R₀ d e t hl τ q] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
