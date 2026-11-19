module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeThreeStageNormalForm

/-! # 削除語の標準的な保持・削除表示
概要：元の各入力を右端から一度ずつ保持または削除する標準表示を作る。
方針：入力次元で帰納し、保持する入力の順序つき添字を回収する。
規約：右端の入力が座標零。使われ方：削除語の Serre 評価の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 各入力を右端から保持または削除する標準表示。 -/
inductive CubeDeletionNormal : ℕ → ℕ → Type
  | nil : CubeDeletionNormal 0 0
  | drop {n m : ℕ} (d : CubeDeletionNormal n m) : CubeDeletionNormal (n + 1) m
  | keep {n m : ℕ} (d : CubeDeletionNormal n m) : CubeDeletionNormal (n + 1) (m + 1)

/-- 標準表示が保持する元の入力座標。 -/
def cubeDeletionNormalEmbedding : {n m : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m → (Fin m → Fin n)
  | _, _, .nil => Fin.elim0
  | _, _, .drop d => fun i => (cubeDeletionNormalEmbedding d i).succ
  | _, _, .keep d => Fin.cons 0 (fun i => (cubeDeletionNormalEmbedding d i).succ)

/-- 全入力を保持する標準表示。 -/
def cubeDeletionNormalId : (n : ℕ) → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n n
  | 0 => .nil
  | n + 1 => .keep (cubeDeletionNormalId n)

/-- 全入力を保持する標準表示の添字は恒等。 -/
lemma cubeDeletionNormalId_embedding (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId n) = _root_.id := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding]
    · simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding, ih]

/-- 一つの出力を削除して同じ保持・削除表示へ戻す。 -/
def cubeDeletionNormalErase : {n m : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n (m + 1) →
    Fin (m + 1) → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m
  | _, _, .drop d, i => .drop (cubeDeletionNormalErase d i)
  | _, 0, .keep d, _ => .drop d
  | _, _ + 1, .keep d, i =>
      Fin.cases (.drop d) (fun j => .keep (cubeDeletionNormalErase d j)) i

/-- 標準表示からの一出力削除は、元の選択添字から同じ座標を飛ばすこと。 -/
lemma cubeDeletionNormalErase_embedding {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n (m + 1))
    (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase d i) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding d ∘ i.succAbove := by
  induction n generalizing m with
  | zero => cases d
  | succ n ih =>
    cases d with
    | drop d =>
      funext j
      exact congrArg Fin.succ (congrFun (ih d i) j)
    | keep d =>
      cases m with
      | zero => funext j; exact Fin.elim0 j
      | succ m =>
        refine Fin.cases ?_ (fun i => ?_) i
        · funext j
          simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding]
        · funext j
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding]
          · simpa [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding] using
              congrArg Fin.succ (congrFun (ih d i) j)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
