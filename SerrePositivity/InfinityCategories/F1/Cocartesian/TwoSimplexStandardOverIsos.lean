module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexCellCospan
public import SerrePositivity.InfinityCategories.F1.InnerTwoHornOverPushout

/-!
概要：同じ二辺を標準単体で表示し、元の nerve セルと底上の同型で結ぶ。
方針：標準単体の底の同型が同じ面と合成に整合する式を使う。
規約：二辺と共有頂点を動かさず、同じ底への射を保持する。
使われ方：元の target Segal 制限を標準ホーンの自明 Kan 制限へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 標準単体の同じ底の同型は、元のセル添字と任意の後続関手に整合する。 -/
lemma localKanDiagramBaseIso_cell_comp {C : Type u} [Category.{u} C]
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (k : ULift.{u} (Fin (n + 1)) ⥤ C) :
    (localKanDiagramBaseIso.{u} m).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianSimplexCellIndex α ⋙ k)) =
    stdSimplex.map α ≫ (localKanDiagramBaseIso.{u} n).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) := by
  have h : nerveMap (cocartesianSimplexCellIndex α ⋙ k) =
      nerveMap (cocartesianSimplexCellIndex α) ≫ nerveMap k := rfl
  rw [h, Functor.map_comp, ← Category.assoc,
    cocartesianSimplexCellIndex_large_projection, Category.assoc]

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)

/-- 同じ二単体の元の内ホーンを、大きい宇宙の元の底上で表示する。 -/
def cocartesianTwoSimplexStandardHorn :
    (Λ[2, 1] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) :=
  (horn 2 1).ι ≫ (localKanDiagramBaseIso.{u} 2).hom ≫
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)

/-- 最初の標準区間と元の最初の nerve セルの底上の同型。 -/
def cocartesianTwoSimplexStandardFirstOverIso :
    InnerTwoHornOver.first (cocartesianTwoSimplexStandardHorn k) ≅
      Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (cocartesianTwoSimplexFirstCell k))) :=
  Over.isoMk (localKanDiagramBaseIso.{u} 1) (by
    change _ = horn₂₁.ι₀₁ ≫ ((horn 2 1).ι ≫ _)
    rw [← Category.assoc, horn.ι_ι]
    exact localKanDiagramBaseIso_cell_comp (SimplexCategory.δ (2 : Fin 3)) k)

/-- 次の標準区間と元の次の nerve セルの底上の同型。 -/
def cocartesianTwoSimplexStandardSecondOverIso :
    InnerTwoHornOver.second (cocartesianTwoSimplexStandardHorn k) ≅
      Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (cocartesianTwoSimplexSecondCell k))) :=
  Over.isoMk (localKanDiagramBaseIso.{u} 1) (by
    change _ = horn₂₁.ι₁₂ ≫ ((horn 2 1).ι ≫ _)
    rw [← Category.assoc, horn.ι_ι]
    exact localKanDiagramBaseIso_cell_comp (SimplexCategory.δ (0 : Fin 3)) k)

/-- 同じ共有頂点の標準表示と元の唯一の共有セルの底上の同型。 -/
def cocartesianTwoSimplexStandardSharedOverIso :
    InnerTwoHornOver.vertex (cocartesianTwoSimplexStandardHorn k) ≅
      Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (cocartesianTwoSimplexSharedCell k))) :=
  Over.isoMk (localKanDiagramBaseIso.{u} 0) (by
    exact (localKanDiagramBaseIso_cell_comp (SimplexCategory.δ (0 : Fin 2))
      (cocartesianTwoSimplexFirstCell k)).trans
      (congrArg (fun m ↦ stdSimplex.δ (0 : Fin 2) ≫ m)
        (cocartesianTwoSimplexStandardFirstOverIso k).hom.w))

end SerrePositivity.InfinityCategories
