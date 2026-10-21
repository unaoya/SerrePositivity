module

public import SerrePositivity.EInfinity.Hammock.UnmarkedValueAppend
public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstColumn
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorTarget
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendArrowProperty

/-!
# 元の三因子を貼った語の最初の非指定列

概要：全指定 prefix・元の一生成矢・任意の残りを貼った語の最小非指定位置を回収する。
方針：元の左右の列の回収と firstColumn の最小性を使う。
規約：空の prefix と残りの語も含む。
使われ方：貼り戻しの後の抽出による同じ生成矢と元の因子の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} (g : FactorTarget.Index W)
  (S : Zigzag W.paths a X g.val.left) (T : Zigzag W.paths b g.val.right Y)

def obj := ZigzagAppend.obj
  (ZigzagAppend.obj S (ForwardZigzag.obj (W := W.paths) g.val.hom.toPath)) T

def columnIndex (a b : Word) : Fin (Word.append (Word.append a (Word.single .forward)) b).length :=
  ((0 : Fin 1).natAdd a.length).castAdd b.length

lemma column_generator : column W (obj W g S T) (columnIndex a b) = [g.val] := by
  classical
  rw [obj, columnIndex, column_append_left, column_append_right]
  change (if W g.val.hom then [] else [] ++ [g.val]) = _
  rw [ite_eq_right g.property]
  rfl

lemma before_column_mem (hs : ∀ j, W.paths (S.arrow j))
    (j : Fin (Word.append (Word.append a (Word.single .forward)) b).length)
    (hj : j < columnIndex a b) : W.paths ((obj W g S T).arrow j) := by
  have hjv : j.val < a.length := hj
  let i : Fin a.length := ⟨j.val, hjv⟩
  have he : j = (i.castAdd 1).castAdd b.length := Fin.ext rfl
  cases he
  exact ((ZigzagAppend.arrow_left_property W.paths _ _ _).trans
    (ZigzagAppend.arrow_left_property W.paths S
      (ForwardZigzag.obj (W := W.paths) g.val.hom.toPath) i)).2 (hs i)

lemma firstColumn_eq (hs : ∀ j, W.paths (S.arrow j))
    (h : ∃ j, column W (obj W g S T) j ≠ []) :
    firstColumn W (obj W g S T) h = columnIndex a b := by
  apply le_antisymm
  · exact firstColumn_le W _ h _ (fun he => List.cons_ne_nil _ _
      ((column_generator W g S T).symm.trans he))
  · by_contra hn
    have hlt := lt_of_not_ge hn
    exact firstColumn_nonempty W _ h (GeneratorWord.erase_marked W _
      (before_column_mem W g S T hs _ hlt))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
