module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal

/-! # 削除標準表示の元の頂点関数による判定
概要：保持・削除の標準表示は元の座標選択の関数から一意に回収できる。
方針：保持添字の単射性を入力次元で帰納し、一座標頂点で添字を検出する。
規約：形式語の等号を仮定しない。使われ方：元の削除語の Serre 評価の等号。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction

/-- 保持する元の添字は、保持・削除の標準表示を一意に決める。 -/
lemma cubeDeletionNormalEmbedding_injective (n m : ℕ) :
    Function.Injective (cubeDeletionNormalEmbedding (n := n) (m := m)) := by
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
        simpa only [cubeDeletionNormalEmbedding, Fin.succ_inj] using congrFun h i
      | keep e =>
        have hc := congrFun h 0
        simp [cubeDeletionNormalEmbedding] at hc
    | keep d =>
      cases e with
      | drop e =>
        have hc := congrFun h 0
        simp [cubeDeletionNormalEmbedding] at hc
        exact False.elim ((Fin.succ_ne_zero _) hc.symm)
      | keep e =>
        congr 1
        apply ih
        funext i
        simpa only [cubeDeletionNormalEmbedding, Fin.cons_succ, Fin.succ_inj] using
          congrFun h i.succ

/-- 座標選択の元の頂点関数は、選択した元の添字を一意に決める。 -/
lemma cubeCoordinateSelect_injective (n m : ℕ) :
    Function.Injective (cubeCoordinateSelect (n := n) (m := m)) := by
  intro e f h
  funext j
  have hj := congrFun (congrFun h (cubeVertexAtom n (e j))) j
  have hf : f j = e j := by
    simpa [cubeCoordinateSelect, _root_.SerrePositivity.InfinityCategories.Simplicial.cubeVertexAtom] using hj.symm
  exact hf.symm

/-- 標準表示の元の頂点での評価。 -/
def cubeDeletionNormalVertex {n m : ℕ} (d : CubeDeletionNormal n m) :
    CubeVertex n → CubeVertex m :=
  cubeCoordinateSelect (cubeDeletionNormalEmbedding d)

/-- 元の頂点関数は、保持・削除の標準表示の等号を検出する。 -/
lemma cubeDeletionNormalVertex_injective (n m : ℕ) :
    Function.Injective (cubeDeletionNormalVertex (n := n) (m := m)) := by
  intro d e h
  exact cubeDeletionNormalEmbedding_injective n m (cubeCoordinateSelect_injective n m h)

/-- 標準表示の一出力削除は、元の頂点関数の同じ削除との合成。 -/
lemma cubeDeletionNormalVertex_erase {n m : ℕ} (d : CubeDeletionNormal n (m + 1))
    (i : Fin (m + 1)) :
    cubeDeletionNormalVertex (cubeDeletionNormalErase d i) =
      cubeVertexDegeneracy m i ∘ cubeDeletionNormalVertex d := by
  funext x j
  exact congrArg x (congrFun (cubeDeletionNormalErase_embedding d i) j)

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateSelect_injective := _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect_injective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding_injective := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding_injective

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalVertex := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalVertex_erase := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalVertex_erase

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalVertex_injective := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalVertex_injective
