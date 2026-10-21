module

public import SerrePositivity.EInfinity.Hammock.ZigzagFirstBoundaryBackwardMaps
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingHom
public import SerrePositivity.EInfinity.Hammock.Segment

/-!
# 元の接合点の射を保持する境界付き縦射

概要：元の接合点の指定射と全縦成分の対応を保つ。
方針：先頭成分だけを固定し、全列の正方形と元の端点移送を回収する。
規約：接合点の指定射を恒等射とは仮定しない。
使われ方：DK9.4・10.3の元の語の Grothendieck 分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : Word} {X X' Y : C}
structure BoundaryHom {d : Direction} (f : X ⟶ X')
    (S : Zigzag W (Word.cons d w) X Y) (T : Zigzag W (Word.cons d w) X' Y) where
  hom : MovingHom S T
  first : hom.app 0 = eqToHom S.first ≫ f ≫ eqToHom T.first.symm
  last : hom.app (Fin.last (Word.cons d w).length) = eqToHom (S.last.trans T.last.symm)

omit [W.IsMultiplicative] in
lemma BoundaryHom.ext {d : Direction} {f : X ⟶ X'}
    {S : Zigzag W (Word.cons d w) X Y} {T : Zigzag W (Word.cons d w) X' Y}
    (h k : BoundaryHom f S T) (hh : h.hom = k.hom) : h = k := by
  cases h
  cases k
  cases hh
  rfl

end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
