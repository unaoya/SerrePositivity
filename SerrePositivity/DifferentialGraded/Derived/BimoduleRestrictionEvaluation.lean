module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestriction

/-! # 両側制限とbimodule値評価の自然比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- 積dg圏表示へ移ってからの評価は元のbimodule値と自然同型。 -/
def bimoduleRightModuleEvaluationIso (b : B) (c : C) :
    (rightModuleBimoduleEquivalence A B C).inverse ⋙
        moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c)) ≅
      BimoduleCategory.valueEvaluation A B C b c :=
  Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A B C).inverse
      (rightModuleBimoduleEvaluationIso A B C b c).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightModuleBimoduleEquivalence A B C).counitIso
      (BimoduleCategory.valueEvaluation A B C b c) ≪≫
    Functor.leftUnitor _

variable (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

def bimoduleRestrictionEvaluationIso (b : B) (c : C) :
    bimoduleRestriction A B C D E F G ⋙ BimoduleCategory.valueEvaluation A B C b c ≅
      BimoduleCategory.valueEvaluation A D E (F.obj b) (G.obj c) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (Functor.isoWhiskerLeft
        (moduleRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
          (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (bimoduleRestrictionIndex A B C D E F G))
        (rightModuleBimoduleEvaluationIso A B C b c)) ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (moduleRestrictionEvaluationIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (bimoduleRestrictionIndex A B C D E F G)
        (op (op b, c))) ≪≫
    bimoduleRightModuleEvaluationIso A D E (F.obj b) (G.obj c)

end SerrePositivity.DifferentialGraded
