module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestrictionValues

/-! # 第一中間圏の制限は通常のbimodule結合子と可換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
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
local notation "QR" => BimoduleCategory.of A C T (compose A C E T Q₀ R₀)

/-- 最初の中間圏を制限する比較は、三因子の通常結合子と可換。 -/
lemma associatorIso_middleRestriction :
    (associatorIso A B D E T LP RQ R₀).hom ≫
      composeMap A B D T (𝟙 LPc) (composeRightRestrictionIso A C D E T F Q R).hom ≫
      middleRestrictionComparisonMap A B C D T F P₀ (compose A C E T Q₀ R₀) =
    composeMap A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) ≫
      (associatorIso A B C E T P₀ Q₀ R₀).hom := by
  apply BimoduleCategory.value_hom_ext A B T
  intro b t
  have h₁ := associatorIso_hom_value_eval A B D E T LP RQ R₀ b t
  have h₂ := composeMap_value_eval A B D T (𝟙 LPc)
    (composeRightRestrictionIso A C D E T F Q R).hom b t
  have h₃ := middleRestrictionComparisonMap_value_eval A B C D T F P₀
    (compose A C E T Q₀ R₀) b t
  have h₄ := composeMap_value_eval A B E T
    (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) b t
  have h₅ := associatorIso_hom_value_eval A B C E T P₀ Q₀ R₀ b t
  simp only [CategoryTheory.Functor.map_comp]
  rw [h₁, h₂, h₃, h₄, h₅]
  exact associatorValue_middleRestriction A B C D E T F P Q R b t

end SerrePositivity.DifferentialGraded.BimoduleTensor
