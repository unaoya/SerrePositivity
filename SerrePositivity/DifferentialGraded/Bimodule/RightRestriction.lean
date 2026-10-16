module
public import SerrePositivity.DifferentialGraded.Bimodule.RightModuleComparison
public import SerrePositivity.DifferentialGraded.Module.RestrictionColimits
public import SerrePositivity.DifferentialGraded.Module.Isomorphism

/-! # 積dg圏のopposite上の右加群の右B制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 第一因子の包含を二重oppositeへ送り、右加群の制限の向きを固定する。 -/
def tensorRightRestrictionInclusion (c : C) :
    DGFunctor A Bᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖᵒᵖ :=
  (dgTensorIncludeFirst A Bᵒᵖ C c).comp (dgDoubleOpposite A (DGTensorCategory A Bᵒᵖ C))

def tensorRightRestriction (c : C) :
    ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ⥤ ModuleCategory A B :=
  moduleRestriction A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (tensorRightRestrictionInclusion A B C c)

def tensorRightRestrictionEvaluationIso (b : B) (c : C) :
    tensorRightRestriction A B C c ⋙ moduleEvaluation A B b ≅
      moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c)) :=
  moduleRestrictionEvaluationIso A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    (tensorRightRestrictionInclusion A B C c) b

/-- 選択された左右同値の逆を使う主bimoduleの右制限も、直接の制限と同型。 -/
def rightModuleBimoduleRightRestrictionIso
    (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (c : C) :
    (BimoduleCategory.evaluation A B C c).obj
        ((rightModuleBimoduleEquivalence A B C).functor.obj M) ≅
      (tensorRightRestriction A B C c).obj M := by
  let L := leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)
  let ε := L.counitIso.app M
  let K := ForgetEnrichment.to (Complex A) (L.inverse.obj M)
  refine moduleIsoMk A B
    (M := (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M)).rightAt c)
    (N := restrictModule A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (tensorRightRestrictionInclusion A B C c) (ForgetEnrichment.to (Complex A) M))
    (fun x => (moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (x, c))).mapIso ε) ?_
  intro x y
  have h := moduleRestriction_naturality A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    (tensorRightRestrictionInclusion A B C c) ε.hom x y
  change (((dgTensorFirstHom A Bᵒᵖ C c x y) ≫ 𝟙 _) ≫
      (𝟙 _ ≫ K.map (x, c) (y, c))) ≫ _ =
    (((dgTensorFirstHom A Bᵒᵖ C c x y) ≫ 𝟙 _) ≫
      (ForgetEnrichment.to (Complex A) M).map (op (op (x, c))) (op (op (y, c)))) ≫ _ at h
  simp only [Category.comp_id, Category.id_comp] at h
  exact h

end SerrePositivity.DifferentialGraded
