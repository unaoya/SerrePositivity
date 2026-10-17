module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionEvaluation

/-! # graph延長への単位挿入成分と評価による復元 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- N(d)の元とF(d)の閉単位を、対応するtensor生成元へ送る。 -/
def functorExtensionInsertionComponent (N : RightModule A D) (d : D) :
    N.obj (op d) ⟶ ((dgModuleExtension A D E F).obj N).obj (op (F.obj d)) :=
  freeUnitInsert A (F.obj d) (N.obj (op d)) ≫
    BalancedTensor.ι A D N ((functorGraph A D E F).leftAt (F.obj d)) d

lemma functorExtensionInsertion_apply (N : RightModule A D) (d : D) (r : ℤ)
    (m : (N.obj (op d)).X r) :
    (functorExtensionInsertionComponent A D E F N d).f r m =
      BalancedTensor.element A D N ((functorGraph A D E F).leftAt (F.obj d)) d
        m (unitElement A (F.obj d)).val (add_zero r) := by
  change (BalancedTensor.ι A D N ((functorGraph A D E F).leftAt (F.obj d)) d).f r
    ((freeUnitInsert A (F.obj d) (N.obj (op d))).f r m) = _
  rw [freeUnitInsert_apply]
  rfl

/-- 制限加群の値を挿入して評価すると元に戻る。 -/
lemma functorExtensionInsertion_evaluation (M : RightModule A E) (d : D) :
    functorExtensionInsertionComponent A D E F (restrictModule A D E F.op M) d ≫
      functorExtensionEvaluationComponent A D E F M (F.obj d) = 𝟙 (M.obj (op (F.obj d))) := by
  apply chain_ext_apply
  intro r m
  rw [chain_comp_apply, functorExtensionInsertion_apply, functorExtensionEvaluation_element]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact moduleAction_unit A M (op (F.obj d)) r m

end SerrePositivity.DifferentialGraded
