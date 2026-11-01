module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramFixed
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordComposition

/-!
# 元の MovingDiagram の語の等式による表示変更

概要：語の等式で図式全体を移し、全対象・全縦射と元の WordAction を照合する。
方針：語の等式で帰納し、恒等語の作用の法則を使う。
規約：動く端点の元の関手を保持する。
使われ方：任意列の前後の図式の切り出しと元の語への貼り戻し。
-/

@[expose] public section
universe u v uD vD
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w w' : Word} {A B : D ⥤ C}

def changeWord (h : w = w') (F : MovingDiagram D C W w A B) : MovingDiagram D C W w' A B := h ▸ F

lemma changeWord_refl (F : MovingDiagram D C W w A B) : changeWord rfl F = F := rfl

lemma changeWord_roundtrip (h : w = w') (F : MovingDiagram D C W w A B) :
    changeWord h.symm (changeWord h F) = F := by cases h; rfl

lemma changeWord_obj_heq (h : w = w') (F : MovingDiagram D C W w A B) (d : D) :
    HEq ((changeWord h F).obj d) (F.obj d) := by cases h; rfl

lemma changeWord_map_heq (h : w = w') (F : MovingDiagram D C W w A B)
    {d e : D} (f : d ⟶ e) : HEq ((changeWord h F).map f) (F.map f) := by cases h; rfl

lemma changeWord_vertex (h : w = w') (F : MovingDiagram D C W w A B) (d : D)
    (i : Fin (w.length + 1)) (j : Fin (w'.length + 1)) (he : i.val = j.val) :
    ((changeWord h F).obj d).vertex j = (F.obj d).vertex i := by
  cases h
  have hij : i = j := Fin.ext he
  subst j
  rfl

lemma changeWord_map_app_heq (h : w = w') (F : MovingDiagram D C W w A B)
    {d e : D} (f : d ⟶ e) (i : Fin (w.length + 1)) (j : Fin (w'.length + 1))
    (he : i.val = j.val) : HEq (((changeWord h F).map f).app j) ((F.map f).app i) := by
  cases h
  have hij : i = j := Fin.ext he
  subst j
  rfl

lemma changeWord_arrow_mem (h : w = w') (F : MovingDiagram D C W w A B) (d : D)
    (i : Fin w.length) (j : Fin w'.length) (he : i.val = j.val) (hm : W ((F.obj d).arrow i)) :
    W (((changeWord h F).obj d).arrow j) := by
  cases h
  have hij : i = j := Fin.ext he
  subst j
  exact hm

lemma changeWord_arrow_heq (h : w = w') (F : MovingDiagram D C W w A B) (d : D)
    (i : Fin w.length) (j : Fin w'.length) (he : i.val = j.val) :
    HEq (((changeWord h F).obj d).arrow j) ((F.obj d).arrow i) := by
  cases h
  have hij : i = j := Fin.ext he
  subst j
  rfl

lemma changeWord_fixedFunctor (h : w = w') {X Y : C}
    (F : MovingDiagram D C W w ((Functor.const D).obj X) ((Functor.const D).obj Y)) :
    (changeWord h F).fixedFunctor = F.fixedFunctor ⋙ WordAction.functor (eqToHom h) := by
  cases h
  simp only [changeWord, eqToHom_refl, WordAction.functor_id, CategoryTheory.Functor.comp_id]

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
