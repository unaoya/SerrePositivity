module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestrictionComponents

/-! # 第二中間圏の制限と結合子の値での可換square -/
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

lemma associatorValueHom_secondMiddleRestriction (b : B) (t : T) :
    composeValueHom A B D T (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) b t ≫
      middleRestrictionValueHom A B E D T F (compose A B C E P₀ Q₀) R₀ b t ≫
      associatorValueHom A B C E T P₀ Q₀ R₀ b t =
    associatorValueHom A B C D T P₀ LQ RR b t ≫
      composeValueHom A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b t := by
  apply Cochain.ofHom_injective
  apply associatorLeft_cochain_element_ext A B C D T P₀ LQ RR b t
  intro c d k r s i m n hi hm hn τ q p
  simp only [add_zero] at hn
  cases hn
  simp only [Cochain.ofHom_v]
  change associatorValueComponent A B C E T P₀ Q₀ R₀ b t m
      (middleRestrictionValueComponent A B E D T F (compose A B C E P₀ Q₀) R₀ b t m
        (composeMapComponent A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
          (𝟙 RRc) b t m (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hm))) =
    composeMapComponent A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
      b t m (associatorValueComponent A B C D T P₀ LQ RR b t m
        (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hm))
  exact (associatorSecondMiddleRestriction_left_component_element A B C D E T F P Q R
    b c d t (l := k + r) τ q p hi rfl hm).trans
    (associatorSecondMiddleRestriction_right_component_element A B C D E T F P Q R
      b c d t (l := k + r) τ q p hi rfl hm).symm

lemma associatorValue_secondMiddleRestriction (b : B) (t : T) :
    composeValueMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) b t ≫
      middleRestrictionComparisonValue A B E D T F (compose A B C E P₀ Q₀) R₀ b t ≫
      (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom =
    (associatorValueIso A B C D T P₀ LQ RR b t).hom ≫
      composeValueMap A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b t := by
  simpa only [associatorValueHom_eq, composeValueHom_eq, middleRestrictionValueHom_eq]
    using associatorValueHom_secondMiddleRestriction A B C D E T F P Q R b t

end SerrePositivity.DifferentialGraded.BimoduleTensor
