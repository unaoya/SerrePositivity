module

public import SerrePositivity.EInfinity.Hammock.SegmentMapNaturality

/-!
# 元の zigzag 圏上の各列の自然変換

概要：元の一列の射と全縦射の正方形を、評価関手間の自然変換として回収する。
方針：元の列を端点の番号の等式で移し、first/last の等式を自然同型へ移す。
規約：元の列・元の縦射を使う。局所端点の縦射を恒等射に置き換えない。
使われ方：固定語の graph からブロック図式の三つの脚を抽出する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : Word} {X Y : C}

def columnDiagram (j : Fin w.length) (l r : Fin (w.length + 1))
    (hl : l = w.source j) (hr : w.target j = r) :
    evaluation (W := W) (X := X) (Y := Y) l ⟶ evaluation r where
  app S := eqToHom (congrArg S.vertex hl) ≫ S.arrow j ≫ eqToHom (congrArg S.vertex hr)
  naturality _ _ f := (Segment.square_transport f j l r hl hr).symm

lemma columnDiagram_mem (j : Fin w.length) (l r : Fin (w.length + 1))
    (hl : l = w.source j) (hr : w.target j = r) (hj : w.direction j = .backward)
    (S : Zigzag W w X Y) : W ((columnDiagram j l r hl hr).app S) :=
  (Direction.transport_mem _ _ _).2 (S.backward_mem j hj)

def firstEvaluationIso :
    evaluation (W := W) (w := w) (X := X) (Y := Y) 0 ≅
      (Functor.const (Zigzag W w X Y)).obj X :=
  NatIso.ofComponents (fun S => eqToIso S.first) (by
    intro S T f
    change f.app 0 ≫ eqToHom T.first = eqToHom S.first ≫ 𝟙 X
    rw [f.first, eqToHom_trans]
    simp)

def lastEvaluationIso :
    evaluation (W := W) (w := w) (X := X) (Y := Y) (Fin.last w.length) ≅
      (Functor.const (Zigzag W w X Y)).obj Y :=
  NatIso.ofComponents (fun S => eqToIso S.last) (by
    intro S T f
    change f.app (Fin.last w.length) ≫ eqToHom T.last = eqToHom S.last ≫ 𝟙 Y
    rw [f.last, eqToHom_trans]
    simp)

end SerrePositivity.EInfinity.Hammock.Zigzag
