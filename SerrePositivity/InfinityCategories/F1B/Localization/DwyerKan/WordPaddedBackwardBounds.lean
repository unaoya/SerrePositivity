module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordBackwardBounds
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPadding

/-!
# padding された元の語の全内部 backward 列の境界

概要：元の任意の backward 列の前後には padding による backward 境界がある。
方針：元の内部包含の列番号と両端の実際の列を明示する。
規約：語の長さや元の forward 列の存在を仮定しない。
使われ方：padded な全語の各 backward 挿入への局所比較の適用。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Word

def paddedColumn (w : Word) (p : Fin w.length) : Fin (paddingFunctor.obj w).length :=
  (sandwichInclusion (single .backward) (single .backward) w).orderHom p

def paddingFirstColumn (w : Word) : Fin (paddingFunctor.obj w).length :=
  (0 : Fin 1).castAdd (append w (single .backward)).length

def paddingLastColumn (w : Word) : Fin (paddingFunctor.obj w).length :=
  ((0 : Fin 1).natAdd w.length).natAdd 1

lemma paddingFirst_direction (w : Word) :
    (paddingFunctor.obj w).direction (paddingFirstColumn w) = .backward :=
  append_direction_left _ _ _

lemma paddingLast_direction (w : Word) :
    (paddingFunctor.obj w).direction (paddingLastColumn w) = .backward :=
  (append_direction_right _ _ _).trans (append_direction_right _ _ _)

lemma paddingFirst_lt (w : Word) (p : Fin w.length) : paddingFirstColumn w < paddedColumn w p := by
  change 0 < 1 + p.val
  omega

lemma lt_paddingLast (w : Word) (p : Fin w.length) : paddedColumn w p < paddingLastColumn w := by
  change 1 + p.val < 1 + (w.length + 0)
  have hp := p.isLt
  omega

def paddedBackwardBounds (w : Word) (p : Fin w.length) (hp : w.direction p = .backward) :
    BackwardBounds (paddingFunctor.obj w) (paddedColumn w p) :=
  Classical.choice (exists_backwardBounds _ _
    (((sandwichInclusion (single .backward) (single .backward) w).direction_eq p).trans hp)
    ⟨paddingFirstColumn w, paddingFirst_lt w p, paddingFirst_direction w⟩
    ⟨paddingLastColumn w, lt_paddingLast w p, paddingLast_direction w⟩)

end SerrePositivity.EInfinity.Hammock.Word
