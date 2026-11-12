module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexSimplexArrow
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberSquare

/-! # 任意の複体 dg nerve の cospan の表示

概要：任意の cospan を三つの複体と二つの chain map からなる標準 cospan として表示する。
方針：二つの辺の一単体から射を取り出し、共通の終頂点を合わせてホーンの押し出しで比較する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：任意の四角形の頂点から標準 fiber への比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A]

/-- 概要：cospan の三複体・二射と、その標準 fiber 四角形の cospan が元と一致する証明。
方針：ホーンの二辺から得る通常の図式を記録する。
規約：二つの脚の終域は同じ複体。使われ方：標準 fiber を任意の cospan の上に構成する。 -/
structure ComplexCospanPresentation
    (p : (SSet.horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) where
  /-- 左の複体。 -/
  leftObj : Complex A
  /-- 右の複体。 -/
  rightObj : Complex A
  /-- 共通の終域の複体。 -/
  targetObj : Complex A
  /-- 左の射。 -/
  leftMap : leftObj ⟶ targetObj
  /-- 右の射。 -/
  rightMap : rightObj ⟶ targetObj
  /-- 標準四角形の cospan と元の図式の一致。 -/
  cospan_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare leftMap rightMap) = p

/-- 概要：任意の複体 dg nerve の cospan を通常の二つの chain map で表示する。
方針：二辺の一単体を通常の射に直し、共通の終頂点の等式で右の射の終域を合わせる。
規約：HA Example 1.3.1.8。使われ方：追加の図式一致の仮定なしに標準 fiber へ比較する。 -/
def presentComplexCospan
    (p : (SSet.horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) :
    ComplexCospanPresentation p := by
  let s₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 1 := SSet.yonedaEquiv (SSet.horn₂₂.ι₀₂ ≫ p)
  let s₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 1 := SSet.yonedaEquiv (SSet.horn₂₂.ι₁₂ ≫ p)
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).δ 0 s₀ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).δ 0 s₁ := by
    have H := congrArg (fun f => SSet.yonedaEquiv (f ≫ p)) SSet.horn₂₂.isPushout.w
    simpa only [Category.assoc, SSet.stdSimplex.yonedaEquiv_δ_comp] using H
  have hD : s₁.obj 1 = s₀.obj 1 :=
    congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 0 => s.obj 0) he.symm
  refine ⟨s₀.obj 0, s₁.obj 0, s₀.obj 1, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap s₀,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap s₁ ≫ eqToHom hD, ?_⟩
  apply SSet.horn₂₂.isPushout.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_right,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_simplexChainMap]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_top,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_comp_eqToHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_simplexChainMap]
    exact SSet.yonedaEquiv.symm_apply_apply _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
