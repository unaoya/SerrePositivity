module
public import SerrePositivity.DifferentialGraded.Bimodule.ParameterEvaluation

/-! # パラメータ付き変換の可換式を値から主Hom endへ戻す -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma param_square_of_values {K : Complex A} {M M' N N' : Bimodule A B C}
    (τ : BimoduleParamTrans A B C K M M') (υ : BimoduleParamTrans A B C K N N')
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (a' : ∀ c, ForgetEnrichment.of (Complex A) (M'.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N'.rightAt c))
    (h : ∀ b c, paramValue A B C τ b c ≫
      homPostcompose (M.value b c) (moduleMorphismComponent A B _ _ (a' c) b) =
      paramValue A B C υ b c ≫
        homPrecompose (moduleMorphismComponent A B _ _ (a c) b) (N'.value b c)) (c : C) :
    τ.app c ≫ moduleHomPostcompose A B (M.rightAt c) (M'.rightAt c) (N'.rightAt c) (a' c) =
    υ.app c ≫ moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N'.rightAt c) (a c) := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  exact h b c

end SerrePositivity.DifferentialGraded.Bimodule
