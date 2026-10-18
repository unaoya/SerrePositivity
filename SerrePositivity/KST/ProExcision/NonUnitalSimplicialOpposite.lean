module
public import SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing
public import SerrePositivity.KST.ProExcision.IntegerUnitizationOpposite

/-!
# 非単位単体環の反対環

概要：非単位単体環の各次数で積を逆転した実単体図式を作る。
方針：非単位環準同型の op を各面・退化へ適用する。
規約：KST Proposition 4.14、SW92 §1.2 の行側と列側の比較。
使われ方：非可換な行側のアフィン比較を列側の実比較に結び付ける。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：非単位単体環の実反対環。
方針：台の図式を保ち、各次数の積を逆順にして各射に op を適用する。
規約：KST Proposition 4.14、可換性の仮定を追加しない。
使われ方：行側の比較に対する Claim 4.15 の適用。 -/
def NonUnitalSimplicialRing.mulOpposite (I : NonUnitalSimplicialRing.{u}) :
    NonUnitalSimplicialRing.{u} where
  obj k := NonUnitalRingObject.of (I.obj k)ᵐᵒᵖ
  map f := NonUnitalRingHom.op (I.map f)
  map_id k := by
    apply NonUnitalRingHom.ext
    intro x
    change MulOpposite.op (I.map (𝟙 k) (MulOpposite.unop x)) = x
    rw [I.map_id]
    rfl
  map_comp f g := by
    apply NonUnitalRingHom.ext
    intro x
    change MulOpposite.op (I.map (f ≫ g) (MulOpposite.unop x)) =
      MulOpposite.op (I.map g (I.map f (MulOpposite.unop x)))
    rw [I.map_comp]
    rfl

/-- 概要：反対単体環の零次の指定元。
方針：元の指定元に op を付ける。
規約：KST Proposition 4.14、a の向きを明示する。
使われ方：反対環への列側 Claim 4.15 の入力。 -/
def NonUnitalSimplicialRing.mulOppositeElement (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) : I.mulOpposite.obj (op ⦋0⦌) := MulOpposite.op a

end SerrePositivity.KST.ProExcision
