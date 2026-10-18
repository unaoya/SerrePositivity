module

public import SerrePositivity.InfinityCategories.DoldKanComparison.HomSpace
public import SerrePositivity.InfinityCategories.DGNerve.PinchedHom

/-!
# 小さい Hom の頂点と閉次数零射

概要：線形単体的 Hom の零単体は閉次数零の元、したがって ClosedCategory の射と同値である。
方針：N4 の線形表示と右 pinched Hom の辺の比較を合成する。
規約：この段階では合成の保存や coherent nerve の比較を主張しない。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.3 の通常の圏との対応。
-/

@[expose] public section
noncomputable section

universe u v

namespace SerrePositivity.InfinityCategories.DoldKanComparison

open CategoryTheory DifferentialGraded
open DGNerve.PinchedHom
open scoped Simplicial

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：小さい線形 Hom の頂点を閉次数零元に同定する。
方針：全次数の線形表示の零次数の逆と、N4 の頂点と閉元の同値を合成する。
規約：係数環と対象の宇宙を独立に保つ。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.3 の Hom の零単体の読み方。 -/
def homSpaceVertexCycleEquiv (x y : D) :
    (homSpace (R := R) x y) _⦋0⦌ ≃ zeroCycles (homObject R D x y) :=
  (linearEquiv x y 0).symm.trans (vertexCycleEquiv x y)

/-- 概要：閉次数零射の圏の Hom は小さい線形 Hom の頂点と同値である。
方針：単位複体からの射と閉元の同値の後に、線形 Hom の頂点の同値の逆を取る。
規約：DGCategory に任意の通常の圏構造を要求しない。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.3 の SimplicialCategory との比較の準備。 -/
def closedHomVertexEquiv (x y : ClosedCategory R D) :
    (x ⟶ y) ≃ (homSpace (R := R) (D := D) x y) _⦋0⦌ :=
  (closedHomEquiv R D x y).trans (homSpaceVertexCycleEquiv (R := R) (D := D) x y).symm

end SerrePositivity.InfinityCategories.DoldKanComparison
