module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordBackwardBounds
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPadding

/-!
# padding された元の語の全内部 backward 列の境界

概要：元の任意の backward 列の前後には padding による backward 境界がある。
方針：元の内部包含の列番号と両端の実際の列を明示する。
規約：語の長さや元の forward 列の存在を仮定しない。
使われ方：padded な全語の各 backward 挿入への局所比較の適用。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

def paddedColumn (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length) : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w).length :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sandwichInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) w).orderHom p

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddedColumn)


def paddingFirstColumn (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w).length :=
  (0 : Fin 1).castAdd (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)).length

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddingFirstColumn)


def paddingLastColumn (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w).length :=
  ((0 : Fin 1).natAdd w.length).natAdd 1

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddingLastColumn)


lemma paddingFirst_direction (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w).direction (paddingFirstColumn w) = .backward :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddingFirst_direction)


lemma paddingLast_direction (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w).direction (paddingLastColumn w) = .backward :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _ _ _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddingLast_direction)


lemma paddingFirst_lt (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length) : paddingFirstColumn w < paddedColumn w p := by
  change 0 < 1 + p.val
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddingFirst_lt)


lemma lt_paddingLast (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length) : paddedColumn w p < paddingLastColumn w := by
  change 1 + p.val < 1 + (w.length + 0)
  have hp := p.isLt
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (lt_paddingLast)


def paddedBackwardBounds (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length) (hp : w.direction p = .backward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardBounds (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (paddedColumn w p) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_backwardBounds _ _
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sandwichInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) w).direction_eq p).trans hp)
    ⟨paddingFirstColumn w, paddingFirst_lt w p, paddingFirst_direction w⟩
    ⟨paddingLastColumn w, lt_paddingLast w p, paddingLast_direction w⟩)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddedBackwardBounds)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
