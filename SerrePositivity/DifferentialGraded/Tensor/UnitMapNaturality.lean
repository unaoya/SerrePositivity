module
public import SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
public import SerrePositivity.DifferentialGraded.Tensor.YonedaNaturality
public import SerrePositivity.DifferentialGraded.Bimodule.ValueExt

/-! # 単位比較の閉零bimodule変数に関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite

namespace BalancedTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

/-- 対角の左制限による単位評価の右加群変数に関する自然性。 -/
lemma leftUnitValueHom_map_naturality {M M' : ModuleCategory A B} (f : M ⟶ M') (b : B) :
    map A B f (𝟙 (ForgetEnrichment.of (Complex A) ((Bimodule.diagonal A B).leftAt b))) ≫
      leftUnitValueHom A B (ForgetEnrichment.to (Complex A) M') b =
    leftUnitValueHom A B (ForgetEnrichment.to (Complex A) M) b ≫
      (moduleEvaluation A B b).map f := by
  apply hom_ext
  intro x
  simp only [ι_map_assoc, CategoryTheory.Functor.map_id]
  change ((moduleEvaluation A B x).map f ⊗ₘ 𝟙 _) ≫
      ι A B (ForgetEnrichment.to (Complex A) M') ((Bimodule.diagonal A B).leftAt b) x ≫
        leftUnitValueHom A B (ForgetEnrichment.to (Complex A) M') b =
    ι A B (ForgetEnrichment.to (Complex A) M) ((Bimodule.diagonal A B).leftAt b) x ≫
      leftUnitValueHom A B (ForgetEnrichment.to (Complex A) M) b ≫
        (moduleEvaluation A B b).map f
  rw [leftUnitValueHom, leftUnitValueHom, ι_leftUnitValueIso_hom,
    ι_leftUnitValueIso_hom_assoc]
  exact (rightAction_morphism A B f b x).symm

end BalancedTensor

namespace BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
variable {P P' : BimoduleCategory A B C}
local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "P₁" => BimoduleCategory.underlying A B C P'

lemma leftUnitValue_map_naturality (f : P ⟶ P') (b : B) (c : C) :
    composeValueMap A B B C (𝟙 (BimoduleCategory.of A B B (Bimodule.diagonal A B)))
      f b c ≫ (leftUnitValueIso A B C P₁ b c).hom =
    (leftUnitValueIso A B C P₀ b c).hom ≫
      (BimoduleCategory.valueEvaluation A B C b c).map f := by
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  exact BalancedTensor.leftUnitValueHom_map_naturality A B
    ((BimoduleCategory.evaluation A B C c).map f) b

/-- 左単位同型の閉零bimodule射に関する自然性。Cのsmall性は不要。 -/
lemma leftBimoduleUnitIso_naturality (f : P ⟶ P') :
    composeMap A B B C (𝟙 (BimoduleCategory.of A B B (Bimodule.diagonal A B))) f ≫
      (leftBimoduleUnitIso A B C P₁).hom =
    (leftBimoduleUnitIso A B C P₀).hom ≫ f := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    leftBimoduleUnitIso_hom_value]
  exact leftUnitValue_map_naturality A B C f b c

variable [Small.{u} C]

lemma rightUnitValue_map_naturality (f : P ⟶ P') (b : B) (c : C) :
    composeValueMap A B C C f
      (𝟙 (BimoduleCategory.of A C C (Bimodule.diagonal A C))) b c ≫
      (rightUnitValueIso A B C P₁ b c).hom =
    (rightUnitValueIso A B C P₀ b c).hom ≫
      (BimoduleCategory.valueEvaluation A B C b c).map f := by
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  have h := BalancedTensor.yonedaEvaluation_naturality A C c
    ((BimoduleCategory.leftEvaluation A B C b).map f)
  exact h.trans (congrArg (fun k =>
    (rightUnitValueIso A B C P₀ b c).hom ≫ k)
    (BimoduleCategory.leftEvaluation_map_eval A B C f b c))

/-- 右単位同型の閉零bimodule射に関する自然性。 -/
lemma rightBimoduleUnitIso_naturality (f : P ⟶ P') :
    composeMap A B C C f (𝟙 (BimoduleCategory.of A C C (Bimodule.diagonal A C))) ≫
      (rightBimoduleUnitIso A B C P₁).hom =
    (rightBimoduleUnitIso A B C P₀).hom ≫ f := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    rightBimoduleUnitIso_hom_value]
  exact rightUnitValue_map_naturality A B C f b c

end BimoduleTensor
end SerrePositivity.DifferentialGraded
