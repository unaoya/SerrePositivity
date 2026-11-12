module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeInternalBoundary

/-!
# 零次・一次の立方体の基本鎖の評価

概要：零次・一次では基本鎖の最大旗は一つだけなので、符号付き評価はその旗の評価である。
方針：Fin 0 と Fin 1 の置換が恒等置換だけであることを使う。
規約：零次の評価は閉零元であり、一次の旗には追加の符号はない。
使われ方：HA 1.3.1.16 の比較写像の辺と三角形の低次検査。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：零次の立方体の評価は唯一の最大旗の評価である。
方針：空集合の置換の型の和を一項として評価する。
規約：符号は +1。
使われ方：HA 1.3.1.16 の比較の辺の成分。 -/
lemma cubeEvaluation_zero {T : Type u} (e : Fin 0 ≃ T)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e φ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e φ := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation]
  rfl

/-- 概要：一次の立方体の評価は唯一の最大旗の評価である。
方針：一点集合の置換の型の和を一項として評価する。
規約：旗の向きは空集合から全体集合。
使われ方：HA 1.3.1.16 の比較の三角形のホモトピー成分。 -/
lemma cubeEvaluation_one {T : Type u} (e : Fin 1 ≃ T)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e φ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e φ := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation]
  rfl

/-- 概要：標準零単体の最上位成分は閉次数零の元である。
方針：標準単体の方程式で一点集合の境界が零であることを使う。
規約：ホモロジーへの商を取る前の閉性。
使われ方：HA 1.3.1.16 の零次立方体からの閉射。 -/
lemma standardTopEval_zero_closed (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y 0) :
    differential R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y 0 f) = 0 := by
  have h := f.property Finset.univ 0 Finset.univ_nonempty (by simp)
  simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs] using h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
