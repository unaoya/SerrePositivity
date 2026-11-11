module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom

/-!
# 小さい Hom の頂点と閉次数零射

概要：線形単体的 Hom の零単体は閉次数零の元、したがって ClosedCategory の射と同値である。
方針：N4 の線形表示と右 pinched Hom の辺の比較を合成する。
規約：この段階では合成の保存や coherent nerve の比較を主張しない。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.3（Tag 00SF） の通常の圏との対応。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

open scoped _root_.Simplicial

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 概要：小さい線形 Hom の頂点を閉次数零元に同定する。
方針：全次数の線形表示の零次数の逆と、N4 の頂点と閉元の同値を合成する。
規約：係数環と対象の宇宙を独立に保つ。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.3（Tag 00SF） の Hom の零単体の読み方。 -/
def homSpaceVertexCycleEquiv (x y : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpace (R := R) x y) _⦋0⦌ ≃ zeroCycles (homObject R D x y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y 0).symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.PinchedHom.vertexCycleEquiv x y)

/-- 概要：閉次数零射の圏の Hom は小さい線形 Hom の頂点と同値である。
方針：単位複体からの射と閉元の同値の後に、線形 Hom の頂点の同値の逆を取る。
規約：DGCategory に任意の通常の圏構造を要求しない。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.3（Tag 00SF） の SimplicialCategory との比較の準備。 -/
def closedHomVertexEquiv (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :
    (x ⟶ y) ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpace (R := R) (D := D) x y) _⦋0⦌ :=
  (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D x y).trans (homSpaceVertexCycleEquiv (R := R) (D := D) x y).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
