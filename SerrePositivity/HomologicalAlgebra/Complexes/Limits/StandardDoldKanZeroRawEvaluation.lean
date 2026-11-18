module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.TruncationZeroCyclesInclusion
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.StandardDoldKanZeroEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanNormalizationComponents

/-!
# 元の標準 DK 零次数像の同じ Hom 複体での直接値

概要：元の標準 DK 像を同じ包含で評価すると元の標準零単体の全体集合成分になる。
方針：同じ cycles 包含・零次数 Moore 逆・元の正規化成分式を使う。
規約：元の標準同型と同じ直接評価を保つ。
使われ方：正規化 augmentation と標準閉恒等辺を単射な同じ評価で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.AlgebraicTopology
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

lemma standardMooreZeroIso_inv_value (x y : D) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y 0) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y 0).hom
      ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).inv s)).val = s := by
  have h := ConcreteCategory.congr_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso_hom_subtype x y 0)
    ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).inv s)
  change _ = (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).hom
    ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).inv s) at h
  exact h.trans (ConcreteCategory.congr_hom
    (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).inv_hom_id s)

lemma standardDoldKanModuleIso_zero_raw (x y : D) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y 0) :
    _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion R ComplexShape.embeddingDownNat
      _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl (homObject R D x y)
      ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := R) x y)).hom
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋0⦌) s)) =
    s.val.component Finset.univ 0 Finset.univ_nonempty (by simp) := by
  have h := ConcreteCategory.congr_hom (_root_.SerrePositivity.ComplexLimits.standardDoldKanModuleIso_zero_eval (R := R) x y) s
  change (_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := R) x y)).hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋0⦌) s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f 0
        ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).inv s) at h
  rw [h, _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion_cycles]
  change (homObject R D x y).iCycles 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x y).hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f 0
      ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).inv s))) = _
  rw [_root_.SerrePositivity.ComplexLimits.standardNormalizationIso_zero_eval, _root_.SerrePositivity.ComplexLimits.standardMooreZeroIso_inv_value]

end SerrePositivity.ComplexLimits
