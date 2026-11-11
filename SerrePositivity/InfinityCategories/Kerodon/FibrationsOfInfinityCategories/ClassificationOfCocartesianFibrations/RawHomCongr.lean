module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RawHomWhisker
public import Mathlib.CategoryTheory.Enriched.HomCongr

/-!
概要：元の raw な相対 Hom の同型共役を、全パラメーターの前後合成で評価する。
方針：豊穣前後合成を、元の全空間の射の合成へ戻す。
規約：全局所 Hom を保持する。
使われ方：raw な共役の core と既存の core Hom 共役の厳密な照合。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の raw な相対 Hom の共役は、全パラメーターで指定同型の前後合成。 -/
lemma cocartesianRawHomCongr_apply {B : SSet.{u}}
    {p p' q q' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject B} (ep : p ≅ p') (eq : q ≅ q')
    {n m : SimplexCategoryᵒᵖ} (s : (SimplicialCategory.sHom p q).obj n)
    (α : n ⟶ m) (x : p'.val.left.obj m) :
    ((((Iso.eHomCongr SSet.{u} ep eq).hom).app n s).val.val.app m α) x =
      eq.hom.val.left.app m (s.val.val.app m α (ep.inv.val.left.app m x)) := by
  change (((eHomWhiskerLeft SSet.{u} p' eq.hom).app n
    ((eHomWhiskerRight SSet.{u} ep.inv q).app n s)).val.val.app m α) x = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRawHomWhiskerLeft_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRawHomWhiskerRight_apply]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
