module

public import SerrePositivity.KST.Descent.SquareAction
public import SerrePositivity.KST.Descent.SquareSequence
public import SerrePositivity.KST.Descent.PresheafAction
public import SerrePositivity.KST.Descent.DescentNaturality
public import SerrePositivity.KST.Descent.EquivariantMayerVietoris
public import SerrePositivity.KST.Descent.InvariantProducts

/-!
# 同変な幾何正方形から長完全列の作用へ

## 概要
四辺の同変性から、前層 L の指定制限とその差の同変性を証明する。
境界の同変性が供給されれば、全次数の長完全列の作用を構成できる。

## 方針
逆元の引き戻しによる左表現を使い、前層の反変合成の可換式を二成分で適用する。

## 規約
境界の同変性は明示的な入力とする。四辺の関手性だけからは導かない。
この入力は実降下の長完全列の自然性から供給すべき条件である。

## 使われ方
論文 定理 3.1 の軌道正方形を有理不変部分の全次数完全列へ接続する。
-/

@[expose] public section

universe u v w t

open CategoryTheory Opposite Representation

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable (L : GradedPresheaf.{u, v, w, t} C Coefficient) (H : Coefficient)
variable {sq : Square C} {G : Type*} [Group G] (a : SquareAction sq G)

/-- 概要：同変な幾何正方形の指定制限は同変（論文 定理 3.1）。
方針：四頂点の引き戻し表現と、右辺・下辺の同変性を二成分で使う。
規約：積の二成分の符号はともに正。
使われ方：正方形の長完全列に G 作用を供給する。 -/
theorem SquareAction.restriction_equivariant (n : ℤ) :
    IsIntertwiningMap (L.pullbackRepresentation H n a.on4)
      ((L.pullbackRepresentation H n a.on2).prod (L.pullbackRepresentation H n a.on3))
      (L.squareRestriction H n sq) := by
  constructor
  intro g x
  apply Prod.ext
  · change L.pullback H n sq.f₂₄ (L.pullback H n (a.on4 g⁻¹).asIso.hom x) =
      L.pullback H n (a.on2 g⁻¹).asIso.hom (L.pullback H n sq.f₂₄ x)
    exact (LinearMap.congr_fun
      (L.pullback_action_comm H n sq.f₂₄ a.on2 a.on4 a.equivariant24 g⁻¹) x).symm
  · change L.pullback H n sq.f₃₄ (L.pullback H n (a.on4 g⁻¹).asIso.hom x) =
      L.pullback H n (a.on3 g⁻¹).asIso.hom (L.pullback H n sq.f₃₄ x)
    exact (LinearMap.congr_fun
      (L.pullback_action_comm H n sq.f₃₄ a.on3 a.on4 a.equivariant34 g⁻¹) x).symm

/-- 概要：同変な幾何正方形の制限の差は同変（論文 定理 3.1）。
方針：上辺・左辺の同変性と線形写像の差の保存を使う。
規約：上辺が正、左辺が負の既存の指定写像。
使われ方：正方形の長完全列の第二の射を不変部分へ制限する。 -/
theorem SquareAction.difference_equivariant (n : ℤ) :
    IsIntertwiningMap
      ((L.pullbackRepresentation H n a.on2).prod (L.pullbackRepresentation H n a.on3))
      (L.pullbackRepresentation H n a.on1) (L.squareDifference H n sq) := by
  constructor
  intro g x
  change L.pullback H n sq.f₁₂ (L.pullback H n (a.on2 g⁻¹).asIso.hom x.1) -
      L.pullback H n sq.f₁₃ (L.pullback H n (a.on3 g⁻¹).asIso.hom x.2) =
    L.pullback H n (a.on1 g⁻¹).asIso.hom
      (L.pullback H n sq.f₁₂ x.1 - L.pullback H n sq.f₁₃ x.2)
  rw [map_sub]
  congr 1
  · exact (LinearMap.congr_fun
      (L.pullback_action_comm H n sq.f₁₂ a.on1 a.on2 a.equivariant12 g⁻¹) x.1).symm
  · exact (LinearMap.congr_fun
      (L.pullback_action_comm H n sq.f₁₃ a.on1 a.on3 a.equivariant13 g⁻¹) x.2).symm

/-- 概要：同変な幾何正方形と自然な境界から長完全列の G 作用（論文 定理 3.1）。
方針：制限・差の同変性を証明済みの補題で供給し、境界の同変性と組み合わせる。
規約：境界の同変性を各次数の群の抽象同型だけから推論しない。
使われ方：有理不変部分の完全性と軌道貼り合わせ。 -/
noncomputable def SquareMayerVietoris.withSquareAction (T : SquareMayerVietoris L H sq)
    (boundary_equivariant : ∀ n,
      IsIntertwiningMap (L.pullbackRepresentation H (n + 1) a.on1)
        (L.pullbackRepresentation H n a.on4) (T.boundary n)) :
    GradedMayerVietoris.Action T.toGraded G where
  ρA n := L.pullbackRepresentation H n a.on4
  ρB n := (L.pullbackRepresentation H n a.on2).prod (L.pullbackRepresentation H n a.on3)
  ρC n := L.pullbackRepresentation H n a.on1
  restriction_equivariant := SquareAction.restriction_equivariant L H a
  difference_equivariant := SquareAction.difference_equivariant L H a
  boundary_equivariant := boundary_equivariant

end SerrePositivity.KST.Descent
