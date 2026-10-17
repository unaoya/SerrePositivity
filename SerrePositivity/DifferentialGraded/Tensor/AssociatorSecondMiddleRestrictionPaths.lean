module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestrictionElements

/-! # 第二中間圏の制限と結合子の二経路 -/
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

lemma associatorSecondMiddleRestriction_left_path_element (b : B) (c : C) (d : D) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom.f n
        ((middleRestrictionComparisonValue A B E D T F (compose A B C E P₀ Q₀) R₀ b t).f n
          ((composeValueMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
            (𝟙 RRc) b t).f n
            (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl (by omega) := by
  have h₁ := middleRestriction_leftElement A B C D E T F P Q R b c d t τ q p hi hn
  have h₂ := associatorValueIso_hom_element A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hi hl hn
  exact (congrArg (fun x => (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom.f n x) h₁).trans h₂

lemma associatorSecondMiddleRestriction_right_path_element (b : B) (c : C) (d : D) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (composeValueMap A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
        b t).f n ((associatorValueIso A B C D T P₀ LQ RR b t).hom.f n
          (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl (by omega) := by
  have h₁ := associatorValueIso_hom_element A B C D T P₀ LQ RR b c d t τ q p hi hl hn
  have h₂ := composeValueMap_middleRestriction_rightElement A B C D E T F P Q R
    b c d t τ q p hl (show l + s = n by omega)
  exact (congrArg (fun x => (composeValueMap A B C T (𝟙 P)
    (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b t).f n x) h₁).trans h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
