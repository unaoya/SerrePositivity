module
public import SerrePositivity.DifferentialGraded.Bimodule.RightRestriction

/-! # 積dg圏表示の右制限比較の射に関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

def rightModuleBimoduleRightRestrictionNatIso (c : C) :
    (rightModuleBimoduleEquivalence A B C).functor ⋙ BimoduleCategory.evaluation A B C c ≅
      tensorRightRestriction A B C c :=
  NatIso.ofComponents (fun M => rightModuleBimoduleRightRestrictionIso A B C M c) (by
    intro M N f
    apply moduleMorphism_ext
    intro b
    simp only [CategoryTheory.Functor.map_comp, rightModuleBimoduleRightRestrictionIso,
      moduleIsoMk_hom_eval, tensorRightRestriction, moduleRestriction_map_eval]
    have h := (rightModuleBimoduleEvaluationIso A B C b c).hom.naturality f
    exact h)

lemma rightModuleBimoduleRightRestrictionNatIso_app (c : C)
    (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) :
    (rightModuleBimoduleRightRestrictionNatIso A B C c).app M =
      rightModuleBimoduleRightRestrictionIso A B C M c := rfl

end SerrePositivity.DifferentialGraded
