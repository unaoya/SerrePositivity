module
public import SerrePositivity.KST.SConstruction.CutRelativeEquivalence
public import SerrePositivity.KST.SConstruction.CutIntervalEquivalences
public import SerrePositivity.KST.SConstruction.RelativeMultiRealizationAdditivity

/-! # 相対切断の評価と元の連続区間の Segal 射
概要：相対二評価の後の短い区間への制限を元の連続区間への制限と厳密に照合する。
方針：包含で相対評価を忘れ、min・max の端点写像が対応する区間上で恒等となることを使う。
規約：元の Segal 射そのものを対象にする。使われ方：実現後の加法性から Segal 同値へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories

/-- 元の左側の連続区間への完全な制限。 -/
def cutLeftSegalEvaluation (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    sStableModel n X ⟶ sStableModel k.val X :=
  ⟨sMap X.carrier (cutLeftIntervalInclusion n k),
    preservesCofiberData_sMap X.carrier (cutLeftIntervalInclusion n k)⟩

/-- 元の右側の連続区間への完全な制限。 -/
def cutRightSegalEvaluation (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    sStableModel n X ⟶ sStableModel (n - k.val) X :=
  ⟨sMap X.carrier (cutRightIntervalInclusion n k),
    preservesCofiberData_sMap X.carrier (cutRightIntervalInclusion n k)⟩

/-- 相対切断の subobject を左区間へ制限すると元の左 Segal 評価を厳密に回収する。 -/
lemma cutRelativeComparison_leftSegal (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutRelativeComparison n k X ≫
        relativeCofiberSubobject (cutLeftSupport n k X) (cutRightSupport n k X) ≫
        cutLeftIntervalRestriction n k X = cutLeftSegalEvaluation n k X := by
  have h : cutRelativeComparison n k X ≫
      relativeCofiberSubobject (cutLeftSupport n k X) (cutRightSupport n k X) ≫
      closedStableInclusion (cutLeftSupport n k X) =
    cutStableComparison n k X ≫ cofiberStableSubobject (sStableModel n X) := by
    calc
      _ = cutRelativeComparison n k X ≫
          (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
            cofiberStableSubobject (sStableModel n X)) :=
        congrArg (fun f => cutRelativeComparison n k X ≫ f)
          (relativeCofiberSubobject_inclusion _ _)
      _ = _ := (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ cofiberStableSubobject (sStableModel n X))
          (cutRelativeComparison_inclusion n k X))
  have he := congrArg (fun f => f ≫ cutLeftSegalEvaluation n k X) h
  apply Subtype.ext
  change ((cutRelativeComparison n k X ≫
    relativeCofiberSubobject (cutLeftSupport n k X) (cutRightSupport n k X) ≫
    closedStableInclusion (cutLeftSupport n k X)) ≫ cutLeftSegalEvaluation n k X).val = _
  rw [he]
  have hc := cutStableComparison_evaluation n k X 0 0
  have hv := congrArg Subtype.val (congrArg (fun f => f ≫ cutLeftSegalEvaluation n k X) hc)
  refine hv.trans ?_
  have hi : (cutCornerOrder k 0 0).comp (cutLeftIntervalInclusion n k) =
      cutLeftIntervalInclusion n k := by
    apply DFunLike.ext
    intro i
    apply Fin.ext
    change (cutEndpoint k ((cutLeftIntervalInclusion n k) i) 0 0).val = i.val
    rw [cutEndpoint_zero_zero]
    exact min_eq_left (Nat.le_of_lt_succ i.isLt)
  exact (sMap_comp X.carrier _ _).symm.trans (congrArg (sMap X.carrier) hi)

/-- 相対切断の quotient を右区間へ制限すると元の右 Segal 評価を厳密に回収する。 -/
lemma cutRelativeComparison_rightSegal (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutRelativeComparison n k X ≫
        relativeCofiberQuotient (cutLeftSupport n k X) (cutRightSupport n k X) ≫
        cutRightIntervalRestriction n k X = cutRightSegalEvaluation n k X := by
  have h : cutRelativeComparison n k X ≫
      relativeCofiberQuotient (cutLeftSupport n k X) (cutRightSupport n k X) ≫
      closedStableInclusion (cutRightSupport n k X) =
    cutStableComparison n k X ≫ cofiberStableQuotient (sStableModel n X) := by
    calc
      _ = cutRelativeComparison n k X ≫
          (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
            cofiberStableQuotient (sStableModel n X)) :=
        congrArg (fun f => cutRelativeComparison n k X ≫ f)
          (relativeCofiberQuotient_inclusion _ _)
      _ = _ := (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ cofiberStableQuotient (sStableModel n X))
          (cutRelativeComparison_inclusion n k X))
  have he := congrArg (fun f => f ≫ cutRightSegalEvaluation n k X) h
  apply Subtype.ext
  change ((cutRelativeComparison n k X ≫
    relativeCofiberQuotient (cutLeftSupport n k X) (cutRightSupport n k X) ≫
    closedStableInclusion (cutRightSupport n k X)) ≫ cutRightSegalEvaluation n k X).val = _
  rw [he]
  have hc := cutStableComparison_evaluation n k X 1 1
  have hv := congrArg Subtype.val (congrArg (fun f => f ≫ cutRightSegalEvaluation n k X) hc)
  refine hv.trans ?_
  have hi : (cutCornerOrder k 1 1).comp (cutRightIntervalInclusion n k) =
      cutRightIntervalInclusion n k := by
    apply DFunLike.ext
    intro i
    apply Fin.ext
    change (cutEndpoint k ((cutRightIntervalInclusion n k) i) 1 1).val = i.val + k.val
    rw [cutEndpoint_one_one]
    exact max_eq_left (Nat.le_add_left _ _)
  exact (sMap_comp X.carrier _ _).symm.trans (congrArg (sMap X.carrier) hi)

/-- 任意の実現関手の下で、相対二評価と両区間の制限の合成は元の Segal 射対。 -/
lemma cutRelativeSegalPair (F : StableModel.{u} ⥤ SSet.{u}) (n : ℕ)
    (k : Fin (n + 1)) (X : StableModel.{u}) :
    F.map (cutRelativeComparison n k X) ≫
        CartesianMonoidalCategory.lift
          (F.map (relativeCofiberSubobject (cutLeftSupport n k X) (cutRightSupport n k X)))
          (F.map (relativeCofiberQuotient (cutLeftSupport n k X) (cutRightSupport n k X))) ≫
        (F.map (cutLeftIntervalRestriction n k X) ⊗ₘ F.map (cutRightIntervalRestriction n k X)) =
      CartesianMonoidalCategory.lift (F.map (cutLeftSegalEvaluation n k X))
        (F.map (cutRightSegalEvaluation n k X)) := by
  rw [CartesianMonoidalCategory.lift_map, CartesianMonoidalCategory.comp_lift]
  simp only [← F.map_comp, cutRelativeComparison_leftSegal, cutRelativeComparison_rightSegal]

end SerrePositivity.KST.SConstruction
