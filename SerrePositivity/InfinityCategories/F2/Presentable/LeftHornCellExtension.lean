module

public import SerrePositivity.InfinityCategories.F2.Presentable.LeftHornCellStep

/-!
概要：一段の左ホーン付加は、底上の各指定ホーンを実際に充填する。
方針：元の底上の射で添字付けたセルを含め、pushout の可換条件を制限する。
規約：充填と境界の等式は底上の圏で成立し、底の射を厳密に保つ。
使われ方：可算反復の余極限の left fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 指定した底上の左ホーンの、次段での境界を固定する充填。 -/
lemma exists_leftHornCellStep_extension {B : SSet.{u}} {X : Over B}
    (h : LeftHornCellIndex B) (t : leftHornCellSource h ⟶ X) :
    ∃ F : leftHornCellTarget h ⟶ (leftHornCellStep B).obj X,
      leftHornCellArrow h ≫ F = t ≫ (leftHornCellStepUnit B).app X := by
  let S := fun k : LeftHornCellIndex B ↦
    overCellCopiesFunctor (leftHornCellSource k) (leftHornCellSource k)
  let T := fun k : LeftHornCellIndex B ↦
    overCellCopiesFunctor (leftHornCellSource k) (leftHornCellTarget k)
  let a := Sigma.ι (fun _ : leftHornCellSource h ⟶ X ↦ leftHornCellSource h) t
  let b := Sigma.ι (fun _ : leftHornCellSource h ⟶ X ↦ leftHornCellTarget h) t
  let jS := (Sigma.ι S h).app X
  let jT := (Sigma.ι T h).app X
  let m := (overCellCopiesMap (leftHornCellSource h) (leftHornCellArrow h)).app X
  have he : jS ≫ (leftHornCopiesEvaluation B).app X =
      (overCellCopiesEvaluation (leftHornCellSource h)).app X :=
    NatTrans.congr_app (Sigma.ι_comp_desc
      (fun k : LeftHornCellIndex B ↦ overCellCopiesEvaluation (leftHornCellSource k)) h) X
  have hm : jS ≫ (leftHornCopiesBoundary B).app X = m ≫ jT :=
    NatTrans.congr_app (Sigma.ι_map
      (fun k : LeftHornCellIndex B ↦
        overCellCopiesMap (leftHornCellSource k) (leftHornCellArrow k)) h) X
  have hc := NatTrans.congr_app (leftHornCellStep_condition B) X
  refine ⟨b ≫ jT ≫ (leftHornCellStepCells B).app X, ?_⟩
  calc
    leftHornCellArrow h ≫ b ≫ jT ≫ (leftHornCellStepCells B).app X =
        a ≫ m ≫ jT ≫ (leftHornCellStepCells B).app X := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ jT ≫ (leftHornCellStepCells B).app X) (overCellCopiesMap_ι _ t).symm
    _ = a ≫ jS ≫ (leftHornCopiesBoundary B).app X ≫ (leftHornCellStepCells B).app X := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ a ≫ z ≫ (leftHornCellStepCells B).app X) hm.symm
    _ = a ≫ jS ≫ (leftHornCopiesEvaluation B).app X ≫ (leftHornCellStepUnit B).app X := by
      simpa only [NatTrans.comp_app, Category.assoc] using congrArg (fun z ↦ a ≫ jS ≫ z) hc.symm
    _ = t ≫ (leftHornCellStepUnit B).app X := by
      rw [← Category.assoc jS, he, ← Category.assoc a, overCellCopiesEvaluation_ι]

end SerrePositivity.InfinityCategories.F2.Presentable
