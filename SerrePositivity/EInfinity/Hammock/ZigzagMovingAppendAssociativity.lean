module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendAssociativityObjects
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramWordChange
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramAppend
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramExt

/-!
# 動く全図式の連結の結合則

概要：局所端点も動く三図式の連結を、元の語の結合等式で照合する。
方針：元の全対象の結合則と三部分の全縦成分の回収を使う。
規約：空の語と両接合点を含み、元の全図式を保持する。
使われ方：元の refinedDiagram の括弧を保った三列圧縮。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}
  {a b c : Word} {X Y Z V X' Y' Z' V' : C}
  {S : Zigzag W a X Y} {S' : Zigzag W a X' Y'}
  {T : Zigzag W b Y Z} {T' : Zigzag W b Y' Z'}
  {U : Zigzag W c Z V} {U' : Zigzag W c Z' V'}

lemma app_assoc_heq (f : Zigzag.MovingHom S S') (g : Zigzag.MovingHom T T')
    (h : Zigzag.MovingHom U U')
    (hfg : HEq (f.app (Fin.last a.length)) (g.app 0))
    (hgh : HEq (g.app (Fin.last b.length)) (h.app 0))
    (i : Fin ((Word.append (Word.append a b) c).length + 1))
    (j : Fin ((Word.append a (Word.append b c)).length + 1)) (hij : i.val = j.val) :
    HEq (app (map f g hfg) h i) (app f (map g h hgh) j) := by
  let fg := map f g hfg
  let gh := map g h hgh
  have hfg_h : HEq (fg.app (Fin.last (Word.append a b).length)) (h.app 0) :=
    (app_right_heq f g hfg (Fin.last b.length)).trans hgh
  have hf_gh : HEq (f.app (Fin.last a.length)) (gh.app 0) :=
    hfg.trans (app_left_heq g h 0).symm
  by_cases ha : i.val ≤ a.length
  · let k : Fin (a.length + 1) := ⟨i.val, by omega⟩
    have hi : i = Word.leftVertex (Word.append a b) c (Word.leftVertex a b k) := Fin.ext rfl
    have hj : j = Word.leftVertex a (Word.append b c) k := Fin.ext hij.symm
    exact (((app_index_heq fg h hi).trans (app_left_heq fg h _)).trans
      (app_left_heq f g k)).trans
        ((app_index_heq f gh hj).trans (app_left_heq f gh k)).symm
  · by_cases hb : i.val ≤ a.length + b.length
    · let k : Fin (b.length + 1) := ⟨i.val - a.length, by omega⟩
      have hi : i = Word.leftVertex (Word.append a b) c (Word.rightVertex a b k) :=
        Fin.ext (by dsimp [Word.leftVertex, Word.rightVertex, k]; omega)
      have hj : j = Word.rightVertex a (Word.append b c) (Word.leftVertex b c k) :=
        Fin.ext (by dsimp [Word.leftVertex, Word.rightVertex, k]; omega)
      exact (((app_index_heq fg h hi).trans (app_left_heq fg h _)).trans
        (app_right_heq f g hfg k)).trans
          (((app_index_heq f gh hj).trans (app_right_heq f gh hf_gh _)).trans
            (app_left_heq g h k)).symm
    · let k : Fin (c.length + 1) := ⟨i.val - (a.length + b.length), by
        have := i.isLt
        change i.val < a.length + b.length + c.length + 1 at this
        omega⟩
      have hi : i = Word.rightVertex (Word.append a b) c k :=
        Fin.ext (by dsimp [Word.rightVertex, k]; omega)
      have hj : j = Word.rightVertex a (Word.append b c) (Word.rightVertex b c k) :=
        Fin.ext (by dsimp [Word.rightVertex, k]; omega)
      exact ((app_index_heq fg h hi).trans (app_right_heq fg h hfg_h k)).trans
        (((app_index_heq f gh hj).trans (app_right_heq f gh hf_gh _)).trans
          (app_right_heq g h hgh k)).symm


end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b c : Word} {A B E L : D ⥤ C}

lemma changeWord_append_assoc (F : MovingDiagram D C W a A B)
    (G : MovingDiagram D C W b B E) (H : MovingDiagram D C W c E L) :
    changeWord (Word.append_assoc a b c) ((F.append G).append H) = F.append (G.append H) := by
  apply ext
  · intro d
    exact eq_of_heq ((changeWord_obj_heq _ _ d).trans
      (ZigzagAppend.obj_assoc_heq (F.obj d) (G.obj d) (H.obj d)))
  · intro d e f j
    let i : Fin ((Word.append (Word.append a b) c).length + 1) := ⟨j.val, by
      have hj := j.isLt
      change j.val < a.length + (b.length + c.length) + 1 at hj
      change j.val < a.length + b.length + c.length + 1
      omega⟩
    exact (changeWord_map_app_heq (Word.append_assoc a b c) _ f i j rfl).trans
      (ZigzagAppend.Moving.app_assoc_heq (F.map f) (G.map f) (H.map f)
        ((F.last f).trans (G.first f).symm) ((G.last f).trans (H.first f).symm) i j rfl)

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
