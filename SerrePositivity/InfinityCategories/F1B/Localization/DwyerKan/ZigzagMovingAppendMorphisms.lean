module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendVertical

/-!
# Zigzag の連結の元の可換縦射

概要：元の二つの可換縦射を、連結した zigzag の可換縦射として構成する。
方針：左右の全列を元の列と比較し、元の可換正方形を移す。
規約：動く接合点の縦射の一致を入力し、局所端点の恒等射性を要求しない。
使われ方：固定語の graph の連結関手。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word} {X Y Z X' Y' Z' : C}
  {S : Zigzag W a X Y} {S' : Zigzag W a X' Y'}
  {T : Zigzag W b Y Z} {T' : Zigzag W b Y' Z'}

/-- 左側の全列の正方形は、元の同じ左の正方形。 -/
lemma left_comm (f : Zigzag.MovingHom S S') (g : Zigzag.MovingHom T T')
    (i : Fin a.length) :
    (obj S T).arrow (i.castAdd b.length) ≫
        app f g ((Word.append a b).target (i.castAdd b.length)) =
      app f g ((Word.append a b).source (i.castAdd b.length)) ≫
        (obj S' T').arrow (i.castAdd b.length) := by
  have ht := (app_index_heq f g (Word.target_left a b i)).trans (app_left_heq f g (a.target i))
  have hs := (app_index_heq f g (Word.source_left a b i)).trans (app_left_heq f g (a.source i))
  have hl := heq_comp (source_left_eq S T i) (target_left_eq S T i) (target_left_eq S' T' i)
    (arrow_left_heq S T i) ht
  have hr := heq_comp (source_left_eq S T i) (source_left_eq S' T' i) (target_left_eq S' T' i)
    hs (arrow_left_heq S' T' i)
  exact eq_of_heq (hl.trans ((heq_of_eq (f.comm i)).trans hr.symm))

/-- 右側の全列の正方形も、接合点を含めて元の同じ右の正方形。 -/
lemma right_comm (f : Zigzag.MovingHom S S') (g : Zigzag.MovingHom T T')
    (hj : HEq (f.app (Fin.last a.length)) (g.app 0)) (i : Fin b.length) :
    (obj S T).arrow (i.natAdd a.length) ≫
        app f g ((Word.append a b).target (i.natAdd a.length)) =
      app f g ((Word.append a b).source (i.natAdd a.length)) ≫
        (obj S' T').arrow (i.natAdd a.length) := by
  have ht := (app_index_heq f g (Word.target_right a b i)).trans (app_right_heq f g hj (b.target i))
  have hs := (app_index_heq f g (Word.source_right a b i)).trans (app_right_heq f g hj (b.source i))
  have hl := heq_comp (source_right_eq S T i) (target_right_eq S T i) (target_right_eq S' T' i)
    (arrow_right_heq S T i) ht
  have hr := heq_comp (source_right_eq S T i) (source_right_eq S' T' i) (target_right_eq S' T' i)
    hs (arrow_right_heq S' T' i)
  exact eq_of_heq (hl.trans ((heq_of_eq (g.comm i)).trans hr.symm))

/-- 動く接合点の射が整合する全縦弱同値を連結する。 -/
def map (f : Zigzag.MovingHom S S') (g : Zigzag.MovingHom T T')
    (hj : HEq (f.app (Fin.last a.length)) (g.app 0)) :
    Zigzag.MovingHom (obj S T) (obj S' T') where
  app := app f g
  app_mem := app_mem f g
  comm i := by
    cases i using Fin.addCases with
    | left i => exact left_comm f g i
    | right i => exact right_comm f g hj i

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
