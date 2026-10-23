module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldCellCospan
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexCellMono

/-!
概要：最初の辺と任意次元の尾部への同じ共有頂点の包含は単射。
方針：最初の脚は標準面の単射性、尾部の脚は一点圏の射列の一意性を使う。
規約：元の底上の二射の underlying map を使う。
使われ方：高次単体の局所 cospan の相対 path 持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

instance cocartesianScaffoldSharedToFirst_left_mono (n : ℕ)
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C) :
    Mono (cocartesianScaffoldSharedToFirst n k).left := by
  change Mono (nerveMap (cocartesianSimplexCellIndex.{u} (SimplexCategory.δ (0 : Fin 2))))
  have : Mono (stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) := inferInstanceAs (Mono (stdSimplex.δ (0 : Fin 2)))
  exact cocartesianSimplexCellIndex_nerveMap_mono _

instance cocartesianScaffoldSharedToTail_left_mono (n : ℕ)
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C) :
    Mono (cocartesianScaffoldSharedToTail n k).left := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro σ τ _
  refine CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)
    (fun _ _ _ ↦ Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories
