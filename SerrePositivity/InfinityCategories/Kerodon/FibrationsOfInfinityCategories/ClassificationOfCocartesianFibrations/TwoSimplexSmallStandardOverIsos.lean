module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexCellCospan
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOverPushout

/-!
概要：同じ二辺を標準単体で表示し、元の nerve セルと底上の同型で結ぶ。
方針：標準単体の底の同型が同じ面と合成に整合する式を使う。
規約：二辺と共有頂点を動かさず、同じ底への射を保持する。
使われ方：元の source Segal 制限を標準ホーンの自明 Kan 制限へ移す。

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

/-- 標準単体の同じ底の同型は、元のセル添字と任意の後続関手に整合する。 -/
lemma stdSimplexIsoNerve_cell_comp {C : Type u} [Category.{u} C]
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (k : ULift.{u} (Fin (n + 1)) ⥤ C) :
    (stdSimplex.isoNerve.{u} m).hom ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex α ⋙ k) =
    stdSimplex.map α ≫ (stdSimplex.isoNerve.{u} n).hom ≫
      nerveMap k := by
  have h : nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex α ⋙ k) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex α) ≫ nerveMap k := rfl
  rw [h, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex_projection, Category.assoc]

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)

/-- 同じ二単体の元の内ホーンを、元の小さい宇宙の底上で表示する。 -/
def cocartesianTwoSimplexSmallStandardHorn :
    (Λ[2, 1] : SSet.{u}) ⟶ nerve C :=
  (horn 2 1).ι ≫ (stdSimplex.isoNerve.{u} 2).hom ≫
    nerveMap k

/-- 最初の標準区間と元の最初の nerve セルの底上の同型。 -/
def cocartesianTwoSimplexSmallStandardFirstOverIso :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.first (cocartesianTwoSimplexSmallStandardHorn k) ≅
      Over.mk (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexFirstCell k)) :=
  Over.isoMk (stdSimplex.isoNerve.{u} 1) (by
    change _ = horn₂₁.ι₀₁ ≫ ((horn 2 1).ι ≫ _)
    rw [← Category.assoc, horn.ι_ι]
    exact stdSimplexIsoNerve_cell_comp (SimplexCategory.δ (2 : Fin 3)) k)

/-- 次の標準区間と元の次の nerve セルの底上の同型。 -/
def cocartesianTwoSimplexSmallStandardSecondOverIso :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.second (cocartesianTwoSimplexSmallStandardHorn k) ≅
      Over.mk (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSecondCell k)) :=
  Over.isoMk (stdSimplex.isoNerve.{u} 1) (by
    change _ = horn₂₁.ι₁₂ ≫ ((horn 2 1).ι ≫ _)
    rw [← Category.assoc, horn.ι_ι]
    exact stdSimplexIsoNerve_cell_comp (SimplexCategory.δ (0 : Fin 3)) k)

/-- 同じ共有頂点の標準表示と元の唯一の共有セルの底上の同型。 -/
def cocartesianTwoSimplexSmallStandardSharedOverIso :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.vertex (cocartesianTwoSimplexSmallStandardHorn k) ≅
      Over.mk (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSharedCell k)) :=
  Over.isoMk (stdSimplex.isoNerve.{u} 0) (by
    exact (stdSimplexIsoNerve_cell_comp (SimplexCategory.δ (0 : Fin 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexFirstCell k)).trans
      (congrArg (fun m ↦ stdSimplex.δ (0 : Fin 2) ≫ m)
        (cocartesianTwoSimplexSmallStandardFirstOverIso k).hom.w))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
