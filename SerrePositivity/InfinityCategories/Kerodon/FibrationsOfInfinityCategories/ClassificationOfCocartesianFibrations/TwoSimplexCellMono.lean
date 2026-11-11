module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexCellCospan

/-!
概要：二辺の同じ共有頂点の包含は、元の nerve 上でも単射。
方針：標準単体との同型で元の面の単射性を移す。
規約：同じ底上の射の underlying map を使う。
使われ方：局所 cospan の相対 path 持ち上げ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元のセル写像が単射なら、同じ通常圏の nerve 上のセル写像も単射。 -/
lemma cocartesianSimplexCellIndex_nerveMap_mono {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    [Mono (stdSimplex.map α : (Δ[m] : SSet.{u}) ⟶ Δ[n])] :
    Mono (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex.{u} α)) := by
  have h : nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex.{u} α) =
      (stdSimplex.isoNerve.{u} m).inv ≫ stdSimplex.map α ≫
        (stdSimplex.isoNerve.{u} n).hom := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex_projection, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [h]
  infer_instance

instance cocartesianTwoSimplexSharedToFirst_left_mono
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSharedToFirst k).left := by
  change Mono (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex.{u}
    (SimplexCategory.δ (0 : Fin 2))))
  have : Mono (stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) := inferInstanceAs (Mono (stdSimplex.δ (0 : Fin 2)))
  exact cocartesianSimplexCellIndex_nerveMap_mono _

instance cocartesianTwoSimplexSharedToSecond_left_mono
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSharedToSecond k).left := by
  change Mono (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex.{u}
    (SimplexCategory.δ (1 : Fin 2))))
  have : Mono (stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) := inferInstanceAs (Mono (stdSimplex.δ (1 : Fin 2)))
  exact cocartesianSimplexCellIndex_nerveMap_mono _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
