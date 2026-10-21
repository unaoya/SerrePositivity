module

public import SerrePositivity.EInfinity.Hammock.ZigzagBoundaryHomLaws
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendPartDiagrams

/-!
# 元の部分の接合点を始点として持つ境界付き縦射

概要：元の任意の前の語を残して、後ろの部分の接合点の射を回収する。
方針：元の全縦成分と両端の元の射を境界付き縦射にまとめる。
規約：両方向と前の空語を含む。
使われ方：DK9.4・10.3の元の全語の分解。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
open CategoryTheory Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a w : Word} {d : Direction} {X Y : C}
  {S T : Zigzag W (Word.append a (Word.cons d w)) X Y}
def rightBoundaryHom (h : S ⟶ T) : BoundaryHom (jointFunctor.map h) (rightObj S) (rightObj T) :=
  BoundaryHom.ofMoving (rightMap h) ((rightDiagram (a := a)).first h)
    ((rightDiagram (a := a)).last h)
end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
