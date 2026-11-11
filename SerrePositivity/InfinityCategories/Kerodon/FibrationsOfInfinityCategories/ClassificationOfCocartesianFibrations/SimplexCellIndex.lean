module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCoefficientFormula
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalKanDiagramStrictification

/-!
概要：同じ標準単体の面を、元の分類に使う持ち上げた有限順序の関手へ移す。
方針：既存の射列の添字と nerve の同型を合成する。
規約：元の面と頂点を厳密に保持する。
使われ方：二次元 Segal 比較の辺と共有頂点を、元の零・一次元の分類へ接続する。

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

/-- 元の標準単体の射を、同じ持ち上げた有限順序の通常関手へ移す。 -/
def cocartesianSimplexCellIndex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    ULift.{u} (Fin (m + 1)) ⥤ ULift.{u} (Fin (n + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexChain α)

/-- 同じセル添字は、元の単調写像の合成を保持する。 -/
lemma cocartesianSimplexCellIndex_comp {l m n : ℕ}
    (α : ⦋l⦌ ⟶ ⦋m⦌) (β : ⦋m⦌ ⟶ ⦋n⦌) :
    cocartesianSimplexCellIndex.{u} α ⋙ cocartesianSimplexCellIndex β =
      cocartesianSimplexCellIndex (α ≫ β) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- 元の面の nerve は、標準単体の元の同じ面に厳密に一致する。 -/
lemma cocartesianSimplexCellIndex_projection {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (stdSimplex.isoNerve.{u} m).hom ≫ nerveMap (cocartesianSimplexCellIndex α) =
      stdSimplex.map α ≫ (stdSimplex.isoNerve.{u} n).hom :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor_projection _).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexChain_projection α).symm

/-- 元の分類先の宇宙へ移しても、同じ底の同型は元の面と厳密に可換。 -/
lemma cocartesianSimplexCellIndex_large_projection {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} m).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianSimplexCellIndex α)) =
      stdSimplex.map α ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} n).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- 元の二辺の共有頂点を表す二つのセル添字の合成は厳密に一致。 -/
lemma cocartesianSimplexCellIndex_twoSimplex_sharedVertex :
    cocartesianSimplexCellIndex.{u} (SimplexCategory.δ (0 : Fin 2)) ⋙
        cocartesianSimplexCellIndex (SimplexCategory.δ (2 : Fin 3)) =
      cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)) ⋙
        cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 3)) := by
  rw [cocartesianSimplexCellIndex_comp, cocartesianSimplexCellIndex_comp]
  congr 1
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  fin_cases i
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
