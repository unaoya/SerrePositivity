module

public import SerrePositivity.InfinityCategories.F1.Transport.PointSliceFamilyHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFibrationHomComparison

/-!
概要：元の right fibration の Hom 比較を、指定終点への slice の全族と円柱にする。
方針：既存の比較 span の選択済み切断をそのまま評価する。
規約：比較射と切断を選び直さず、全 Hom のパラメータを保持する。
使われ方：native な錐の全 Hom 作用の合成三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {E B : SSet.{u}} (r : E ⟶ B) [RightFibration r] (c : E _⦋0⦌) (x : B _⦋0⦌)
local notation "H" => pinchedHom x (r.app (Opposite.op ⦋0⦌) c)

/-- 元の選択済み切断から得る、指定終点の slice 内の全 Hom の族。 -/
def rightPointHomTransportSliceFamily : H ⟶ sliceOver (SSet.yonedaEquiv.symm c) :=
  rightFibrationMappingSection r c x ≫
    vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) x

/-- 同じ slice の族の始点は、元の Hom 比較そのもの。 -/
lemma rightPointHomTransportSliceFamily_evaluation :
    rightPointHomTransportSliceFamily r c x ≫ sliceOverProjection (SSet.yonedaEquiv.symm c) =
      rightFibrationHomComparison r c x ≫ vertexFiberι r x := by
  rw [rightFibrationHomComparison, Category.assoc, rightFibrationMappingEvaluation,
    vertexFiberMap_ι]
  rfl

/-- 同じ Hom 比較から指定終点への、元の選択済み切断が与える全円柱。 -/
def rightPointHomTransportCylinder :
    SSet.Homotopy (rightFibrationHomComparison r c x ≫ vertexFiberι r x) (SSet.const c) := by
  let h := pointSliceFamilyHomotopy (rightPointHomTransportSliceFamily r c x)
  exact ⟨h.h, h.h₀.trans (rightPointHomTransportSliceFamily_evaluation r c x), h.h₁, h.rel⟩

/-- 元の切断を底の slice fiber へ戻すと、元の基底表示同型の逆そのもの。 -/
lemma rightPointHomTransportSliceFamily_baseProjection :
    rightFibrationMappingSection r c x ≫ rightFibrationMappingProjection r c x =
      (rightFibrationMappingBaseIso r c x).inv := by
  have h := congrArg (fun k ↦ k ≫ (rightFibrationMappingBaseIso r c x).inv)
    (rightFibrationMappingSection_projection r c x)
  dsimp only [rightFibrationMappingHomProjection] at h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp] using h

/-- 元の全 Hom の slice の族は、底でも指定した同じ基底表示の族。 -/
lemma rightPointHomTransportSliceFamily_base :
    rightPointHomTransportSliceFamily r c x ≫ sliceOverPostcomp (SSet.yonedaEquiv.symm c) r =
      (rightFibrationMappingBaseIso r c x).inv ≫
        vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm c ≫ r)) x := by
  rw [rightPointHomTransportSliceFamily, Category.assoc,
    ← vertexFiberMap_ι (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r)
      (sliceOverProjection (SSet.yonedaEquiv.symm c ≫ r))
      (sliceOverPostcomp (SSet.yonedaEquiv.symm c) r) (sliceOverPostcomp_projection _ r) x,
    ← Category.assoc, ← rightFibrationMappingProjection,
    rightPointHomTransportSliceFamily_baseProjection]

end SerrePositivity.InfinityCategories
