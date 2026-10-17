module
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation

/-! # 右作用制限後の左加群評価を元の評価へ比較する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] (F : DGFunctor A D B)

/-- 右作用を制限したbimoduleの左加群は、元の左加群の対象を再選択したものである。 -/
lemma rightRestriction_leftAt_eq (P : Bimodule A B C) (d : D) :
    (rightRestriction A B D C F P).leftAt d = P.leftAt (F.obj d) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (rightRestriction A B D C F P).leftAt d) (G := P.leftAt (F.obj d)) (fun _ => rfl)
  intro c c'
  simp only [eqToHom_refl, Category.comp_id]
  exact rightRestriction_leftAt_map A B D C F P d c c'

variable [Small.{u} C]

/-- 閉零左加群圏上の、制限後評価と元の評価の同型。 -/
def rightRestrictionLeftEvaluationIso (P : BimoduleCategory A B C) (d : D) :
    (BimoduleCategory.leftEvaluation A D C d).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P) ≅
      (BimoduleCategory.leftEvaluation A B C (F.obj d)).obj P :=
  eqToIso (rightRestriction_leftAt_eq A B D C F _ d)

@[simp]
lemma rightRestrictionLeftEvaluationIso_hom_eval (P : BimoduleCategory A B C) (d : D) (c : C) :
    (leftModuleEvaluation A C c).map (rightRestrictionLeftEvaluationIso A B D C F P d).hom =
      𝟙 _ := by
  simp only [rightRestrictionLeftEvaluationIso, eqToIso.hom, eqToHom_map]
  rfl

@[simp]
lemma rightRestrictionLeftEvaluationIso_inv_eval (P : BimoduleCategory A B C) (d : D) (c : C) :
    (leftModuleEvaluation A C c).map (rightRestrictionLeftEvaluationIso A B D C F P d).inv =
      𝟙 _ := by
  simp only [rightRestrictionLeftEvaluationIso, eqToIso.inv, eqToHom_map]
  rfl

end SerrePositivity.DifferentialGraded.Bimodule
