module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardFamilyReplacementComparisons

/-!
# 元の中央 backward 語の全頂点・全列の位置

概要：左右の forward 区間と三つの backward 列を元の連結語の中で指定する。
方針：連結語の左右の頂点・列の埋め込みを繰り返して用いる。
規約：左から右の順序と向きを保持する。左右の長さ零も含む。
使われ方：元の zigzag 圏からのブロック抽出と再構成の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions
open ForwardPath

variable (n m : ℕ)

abbrev leftWithMiddle : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)

def leftVertex (i : Fin (n + 1)) : Fin ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (leftWithMiddle n) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord n) i))

def rightVertex (i : Fin (m + 1)) : Fin ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (leftWithMiddle n) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord m) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) i)

def firstColumn : Fin (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length :=
  (((0 : Fin 1).castAdd n).castAdd 1).castAdd (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m).length

def leftColumn (i : Fin n) : Fin (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length :=
  ((i.natAdd 1).castAdd 1).castAdd (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m).length

def middleColumn : Fin (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length :=
  ((0 : Fin 1).natAdd (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n).length).castAdd (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m).length

def rightColumn (i : Fin m) : Fin (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length :=
  (i.castAdd 1).natAdd (leftWithMiddle n).length

def lastColumn : Fin (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length :=
  ((0 : Fin 1).natAdd m).natAdd (leftWithMiddle n).length

lemma first_direction : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).direction (firstColumn n m) = .backward := by
  simp [firstColumn, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single]

lemma left_direction (i : Fin n) : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).direction (leftColumn n m i) = .forward := by
  simp [leftColumn, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single]

lemma middle_direction : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).direction (middleColumn n m) = .backward := by
  simp [middleColumn, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single]

lemma right_direction (i : Fin m) : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).direction (rightColumn n m i) = .forward := by
  simp [rightColumn, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, leftWithMiddle]

lemma last_direction : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).direction (lastColumn n m) = .backward := by
  simp [lastColumn, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, leftWithMiddle]

lemma first_source : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).source (firstColumn n m) = leftVertex n m 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source
  rw [first_direction]
  apply Fin.ext
  dsimp [firstColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]
  simp [Nat.mod_eq_of_lt (show 1 < 1 + n + 1 + 1 by omega)]

lemma first_target : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).target (firstColumn n m) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target
  rw [first_direction]
  apply Fin.ext
  dsimp [firstColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]

lemma left_source (i : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).source (leftColumn n m i) = leftVertex n m i.castSucc := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source
  rw [left_direction]
  apply Fin.ext
  dsimp [leftColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]

lemma left_target (i : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).target (leftColumn n m i) = leftVertex n m i.succ := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target
  rw [left_direction]
  apply Fin.ext
  dsimp [leftColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]
  omega

lemma middle_source : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).source (middleColumn n m) = rightVertex n m 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source
  rw [middle_direction]
  apply Fin.ext
  dsimp [middleColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]

lemma middle_target : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).target (middleColumn n m) = leftVertex n m (Fin.last n) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target
  rw [middle_direction]
  apply Fin.ext
  dsimp [middleColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]

lemma right_source (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).source (rightColumn n m i) = rightVertex n m i.castSucc := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source
  rw [right_direction]
  apply Fin.ext
  dsimp [rightColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]

lemma right_target (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).target (rightColumn n m i) = rightVertex n m i.succ := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target
  rw [right_direction]
  apply Fin.ext
  dsimp [rightColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]
  omega

lemma last_source : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).source (lastColumn n m) = Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source
  rw [last_direction]
  apply Fin.ext
  dsimp [lastColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]
  omega

lemma last_target : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).target (lastColumn n m) = rightVertex n m (Fin.last m) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target
  rw [last_direction]
  apply Fin.ext
  dsimp [lastColumn, leftVertex, rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word]

lemma length_eq : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length = n + m + 3 := by
  dsimp [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single]
  omega

lemma leftVertex_val (i : Fin (n + 1)) : (leftVertex n m i).val = 1 + i.val := rfl

lemma rightVertex_val (i : Fin (m + 1)) : (rightVertex n m i).val = n + 2 + i.val := by
  dsimp [rightVertex, leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex]
  omega

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions
