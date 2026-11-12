module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal

/-! # 削除標準表示の元の頂点関数による判定
概要：保持・削除の標準表示は元の座標選択の関数から一意に回収できる。
方針：保持添字の単射性を入力次元で帰納し、一座標頂点で添字を検出する。
規約：形式語の等号を仮定しない。使われ方：元の削除語の Serre 評価の等号。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 保持する元の添字は、保持・削除の標準表示を一意に決める。 -/
lemma cubeDeletionNormalEmbedding_injective (n m : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding (n := n) (m := m)) := by
  induction n generalizing m with
  | zero => intro d e h; cases d; cases e; rfl
  | succ n ih =>
    intro d e h
    cases d with
    | drop d =>
      cases e with
      | drop e =>
        congr 1
        apply ih
        funext i
        simpa only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding, Fin.succ_inj] using congrFun h i
      | keep e =>
        have hc := congrFun h 0
        simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding] at hc
    | keep d =>
      cases e with
      | drop e =>
        have hc := congrFun h 0
        simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding] at hc
        exact False.elim ((Fin.succ_ne_zero _) hc.symm)
      | keep e =>
        congr 1
        apply ih
        funext i
        simpa only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding, Fin.cons_succ, Fin.succ_inj] using
          congrFun h i.succ

/-- 座標選択の元の頂点関数は、選択した元の添字を一意に決める。 -/
lemma cubeCoordinateSelect_injective (n m : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (n := n) (m := m)) := by
  intro e f h
  funext j
  have hj := congrFun (congrFun h (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n (e j))) j
  have hf : f j = e j := by
    simpa [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] using hj.symm
  exact hf.symm

/-- 標準表示の元の頂点での評価。 -/
def cubeDeletionNormalVertex {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding d)

/-- 元の頂点関数は、保持・削除の標準表示の等号を検出する。 -/
lemma cubeDeletionNormalVertex_injective (n m : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (n := n) (m := m)) := by
  intro d e h
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding_injective n m (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_injective n m h)

/-- 標準表示の一出力削除は、元の頂点関数の同じ削除との合成。 -/
lemma cubeDeletionNormalVertex_erase {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n (m + 1))
    (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase d i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy m i ∘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d := by
  funext x j
  exact congrArg x (congrFun (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase_embedding d i) j)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateSelect_injective := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_injective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding_injective := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding_injective

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalVertex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalVertex_erase := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex_erase

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalVertex_injective := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex_injective
