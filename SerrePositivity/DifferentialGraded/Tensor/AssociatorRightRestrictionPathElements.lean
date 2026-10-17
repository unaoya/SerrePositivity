module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestrictionElements

/-! # 右制限・結合子の二経路を三重斉次生成元で計算する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
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

private lemma eval_two {X Y Z : Type*} (f : X → Y) (g : Y → Z) (x : X) (y : Y) (z : Z)
    (hf : f x = y) (hg : g y = z) : g (f x) = z := (congrArg g hf).trans hg

/-- 結合子の後で右制限比較を行う経路の、三重斉次生成元での計算。 -/
lemma associatorRightRestriction_left_path_element (d : D) (c : C) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (composeRightRestrictionValueIso A B D C T F P₀ (compose A C E T Q₀ R₀) d t).hom.f n
        ((associatorValueIso A D C E T RP Q₀ R₀ d t).hom.f n
          (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl (by omega) := by
  have h₁ := associatorValueIso_hom_element A D C E T RP Q₀ R₀ d c e t τ q p hi hl hn
  have h₂ := composeRightRestriction_rightElement A B D C E T F P Q R
    d c e t τ q p hl (show l + s = n by omega)
  exact eval_two _ _ _ _ _ h₁ h₂

/-- 二つの右制限比較を続けると、元の左括弧の三重生成元を与える。 -/
lemma composeRightRestriction_leftElement (d : D) (c : C) (e : E) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hn : k + i = n) :
    (composeRightRestrictionValueIso A B D E T F (compose A B C E P₀ Q₀) R₀ d t).hom.f n
        ((composeValueMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom
          (𝟙 R) d t).f n
            (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn)) =
      associatorLeftElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hi hn := by
  have h₁ := composeValueMap_rightRestriction_leftElement A B D C E T F P Q R
    d c e t τ q p hi hn
  have h₂ := composeRightRestrictionValueIso_element A B D E T F (compose A B C E P₀ Q₀) R₀
    d e t (r := k) (s := i) (n := n) hn τ
      (BalancedTensor.element A C ((Q₀).rightAt e) ((P₀).leftAt (F.obj d)) c q p hi)
  exact (congrArg (fun z => (composeRightRestrictionValueIso A B D E T F
    (compose A B C E P₀ Q₀) R₀ d t).hom.f n z) h₁).trans h₂

/-- 二段階の右制限比較の後で結合子を行う経路も、同じ三重生成元を与える。 -/
lemma associatorRightRestriction_right_path_element (d : D) (c : C) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (associatorValueIso A B C E T P₀ Q₀ R₀ (F.obj d) t).hom.f n
        ((composeRightRestrictionValueIso A B D E T F (compose A B C E P₀ Q₀) R₀ d t).hom.f n
          ((composeValueMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom
            (𝟙 R) d t).f n
              (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl (by omega) := by
  have h₁ := composeRightRestriction_leftElement A B D C E T F P Q R
    d c e t τ q p hi hn
  have h₂ := associatorValueIso_hom_element A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hi hl hn
  exact (congrArg (fun z =>
    (associatorValueIso A B C E T P₀ Q₀ R₀ (F.obj d) t).hom.f n z) h₁).trans h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
