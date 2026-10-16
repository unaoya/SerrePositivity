module
public import SerrePositivity.DifferentialGraded.Bimodule.RestrictedRepresentable
public import SerrePositivity.DifferentialGraded.Module.RestrictionTensor

/-! # 積dg圏上の自由加群の右制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 制限後の生成複体にはHom_C(c₀,c)が現れる。Hom_Bのflat性は用いない。 -/
def restrictedFreeIso (b₀ : B) (c₀ c : C) (K : Complex A) :
    (tensorRightRestriction A B C c).obj
        ((freeAt (A := A) (D := (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
          (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))).obj K) ≅
      (freeAt b₀).obj (K ⊗ (c₀ ⟶[Complex A] c)) :=
  moduleRestrictionTensorIso A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (tensorRightRestrictionInclusion A B C c) K
      (ForgetEnrichment.of (Complex A)
        (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C)))) ≪≫
    (moduleTensorLeftFunctor A B K).mapIso (restrictedRepresentableIso A B C b₀ c₀ c) ≪≫
    tensorModuleAssociatorIso A B K (c₀ ⟶[Complex A] c) (representable A b₀)

end SerrePositivity.DifferentialGraded
