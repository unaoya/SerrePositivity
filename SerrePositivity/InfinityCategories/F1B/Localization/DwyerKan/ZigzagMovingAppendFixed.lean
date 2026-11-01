module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendMorphisms

/-!
# 局所端点が動く二つの区間から固定端点の縦射を作る

概要：動く接合点で貼った全縦射を、元の全体の zigzag の射へ戻す。
方針：左右の成分回収を使い、全体の両端にだけ first・last を要求する。
規約：共有端点の縦射を恒等射とは仮定しない。
使われ方：元の X,Y を固定したままブロックを置換する比較自然変換。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word}
  {X Y Y' Z : C} {S : Zigzag W a X Y} {S' : Zigzag W a X Y'}
  {T : Zigzag W b Y Z} {T' : Zigzag W b Y' Z}

def fixedMap (f : Zigzag.MovingHom S S') (g : Zigzag.MovingHom T T')
    (hj : HEq (f.app (Fin.last a.length)) (g.app 0))
    (hf : f.app 0 = eqToHom (S.first.trans S'.first.symm))
    (hl : g.app (Fin.last b.length) = eqToHom (T.last.trans T'.last.symm)) :
    Zigzag.Hom (obj S T) (obj S' T') where
  app := app f g
  app_mem := app_mem f g
  first := by
    have h := (conj_eqToHom_iff_heq _ _ (vertex_left S T 0) (vertex_left S' T' 0)).2
      (app_left_heq f g 0)
    rw [hf, eqToHom_trans, eqToHom_trans] at h
    exact h
  last := by
    have h := (conj_eqToHom_iff_heq _ _ (vertex_right S T (Fin.last b.length))
      (vertex_right S' T' (Fin.last b.length))).2 (app_right_heq f g hj (Fin.last b.length))
    rw [hl, eqToHom_trans, eqToHom_trans] at h
    exact h
  comm := (map f g hj).comm

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
