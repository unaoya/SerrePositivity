module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldCellCospan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexCellMono

/-!
概要：最初の辺と任意次元の尾部への同じ共有頂点の包含は単射。
方針：最初の脚は標準面の単射性、尾部の脚は一点圏の射列の一意性を使う。
規約：元の底上の二射の underlying map を使う。
使われ方：高次単体の局所 cospan の相対 path 持ち上げ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

instance cocartesianScaffoldSharedToFirst_left_mono (n : ℕ)
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedToFirst n k).left := by
  change Mono (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex.{u} (SimplexCategory.δ (0 : Fin 2))))
  have : Mono (stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) := inferInstanceAs (Mono (stdSimplex.δ (0 : Fin 2)))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex_nerveMap_mono _

instance cocartesianScaffoldSharedToTail_left_mono (n : ℕ)
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedToTail n k).left := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro σ τ _
  refine CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)
    (fun _ _ _ ↦ Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
