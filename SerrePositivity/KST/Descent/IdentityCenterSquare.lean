module

public import SerrePositivity.KST.Descent.BlowupGeometry
public import SerrePositivity.KST.Descent.SquareMapSequence
public import SerrePositivity.KST.Descent.SplitMayerVietoris

/-!
# 閉中心の恒等正方形と軌道正方形の比較元

## 概要
右辺を恒等射とする閉中心の正方形を構成し、一般の正方形からの指定比較を与える。
この正方形の長完全列の境界は完全性から零になる。

## 方針
正方形の射は中心上の射と基底への射から作る。
境界の零性には、指定差の全射性を用いる。

## 規約
恒等正方形の特別な分裂を使う。他の抽象 blowup の境界を零とはしない。

## 使われ方
論文 定理 3.1 の (3.8) と中心の帰納仮定を軌道正方形へ貼り合わせる比較元。
-/

@[expose] public section

universe u v w t

open CategoryTheory Opposite AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：閉中心と恒等変形の可換正方形（論文 定理 3.1）。
方針：上辺と下辺を i、左右の辺を恒等射にする。
規約：この定義自体は任意の圏で使える。
使われ方：軌道正方形と比較する幾何的な分裂正方形。 -/
def identityCenterSquare {C : Type u} [Category.{v} C] {X Z : C} (i : Z ⟶ X) : Square C where
  f₁₂ := i
  f₁₃ := 𝟙 Z
  f₂₄ := 𝟙 X
  f₃₄ := i
  fac := by simp

/-- 概要：中心への可換式から恒等中心正方形への射を作る（論文 定理 3.1）。
方針：上の二頂点の射を、下の二頂点の射と元の正方形の辺から合成する。
規約：四辺の可換性を保持する指定された立方体。
使われ方：軌道正方形から基底とその閉中心への比較。 -/
def toIdentityCenterSquare {C : Type u} [Category.{v} C] (sq : Square C)
    {X Z : C} (i : Z ⟶ X) (base : sq.X₄ ⟶ X) (center : sq.X₃ ⟶ Z)
    (comm : sq.f₃₄ ≫ base = center ≫ i) : sq ⟶ identityCenterSquare i where
  τ₁ := sq.f₁₃ ≫ center
  τ₂ := sq.f₂₄ ≫ base
  τ₃ := center
  τ₄ := base
  comm₁₂ := by
    simp only [identityCenterSquare, ← Category.assoc]
    rw [sq.fac, Category.assoc, comm, Category.assoc]
  comm₁₃ := by simp [identityCenterSquare]
  comm₂₄ := by simp [identityCenterSquare]
  comm₃₄ := comm

/-- 概要：恒等中心正方形の指定差は全射（論文 定理 3.1）。
方針：成分 (0,-x) を取る。
規約：中心への引き戻しの全射性は不要。
使われ方：この正方形の境界の零性。 -/
theorem identityCenterSquare_difference_surjective {C : Type u} [Category.{v} C]
    {Coefficient : Type w} (L : GradedPresheaf.{u, v, w, t} C Coefficient)
    (H : Coefficient) {X Z : C} (i : Z ⟶ X) (n : ℤ) :
    Function.Surjective (L.squareDifference H n (identityCenterSquare i)) := by
  intro x
  refine ⟨(0, -x), ?_⟩
  change L.pullback H n i 0 - L.pullback H n (𝟙 Z) (-x) = x
  simp only [map_zero, GradedPresheaf.pullback_id, zero_sub]
  change - -x = x
  exact neg_neg x

/-- 概要：恒等中心正方形の長完全列の境界は零（論文 定理 3.1）。
方針：差の全射性と、その像で境界が零になる完全性を使う。
規約：実降下で選ばれた境界に対しても零性が強制される。
使われ方：軌道比較の分裂長完全列との整合性。 -/
theorem SquareMayerVietoris.identityCenter_boundary_eq_zero
    {C : Type u} [Category.{v} C] {Coefficient : Type w}
    {L : GradedPresheaf.{u, v, w, t} C Coefficient} {H : Coefficient} {X Z : C} (i : Z ⟶ X)
    (T : SquareMayerVietoris L H (identityCenterSquare i)) (n : ℤ) : T.boundary n = 0 := by
  apply LinearMap.ext
  intro x
  exact (T.exact_difference_boundary n x).mpr
    (identityCenterSquare_difference_surjective L H i (n + 1) x)

/-- 概要：恒等中心正方形は任意の閉中心の抽象 blowup（論文 定理 3.1）。
方針：恒等射の固有性・制限の同型性と、恒等射の引き戻しを使う。
規約：中心に被約性は要求しない。
使われ方：自然な blowup 列を適用する比較元。 -/
def identityCenterBlowup {S : Scheme.{u}} {X Z : FiniteTypeSchemes S} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] (U : X.obj.left.Opens)
    (complement_eq : (U : Set X.obj.left) = (Set.range i.hom.left)ᶜ) :
    AbstractBlowupSquare S where
  square := identityCenterSquare i
  cartesian := IsPullback.id_vert i.hom.left
  proper := show IsProper (𝟙 X.obj.left) from inferInstance
  closed := show IsClosedImmersion i.hom.left from inferInstance
  complement := U
  complement_eq := complement_eq
  iso_on_complement := show IsIso ((𝟙 X.obj.left) ∣_ U) from inferInstance

end SerrePositivity.KST.Descent
