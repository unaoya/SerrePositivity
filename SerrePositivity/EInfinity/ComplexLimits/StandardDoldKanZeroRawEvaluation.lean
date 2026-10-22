module

public import SerrePositivity.EInfinity.ComplexLimits.TruncationZeroCyclesInclusion
public import SerrePositivity.EInfinity.ComplexLimits.StandardDoldKanZeroEvaluation
public import SerrePositivity.EInfinity.ComplexLimits.DoldKanNormalizationComponents

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGNerve.PinchedHom DoldKanComparison
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

lemma standardMooreZeroIso_inv_value (x y : D) (s : StandardSimplex R x y 0) :
    ((standardMooreTermIso (R := R) x y 0).hom
      ((mooreDegreeZeroIso (standardModule (R := R) x y)).inv s)).val = s := by
  have h := ConcreteCategory.congr_hom (standardMooreTermIso_hom_subtype x y 0)
    ((mooreDegreeZeroIso (standardModule (R := R) x y)).inv s)
  change _ = (mooreDegreeZeroIso (standardModule (R := R) x y)).hom
    ((mooreDegreeZeroIso (standardModule (R := R) x y)).inv s) at h
  exact h.trans (ConcreteCategory.congr_hom
    (mooreDegreeZeroIso (standardModule (R := R) x y)).inv_hom_id s)

lemma standardDoldKanModuleIso_zero_raw (x y : D) (s : StandardSimplex R x y 0) :
    truncationExtendedZeroInclusion R ComplexShape.embeddingDownNat
      embeddingDownNat_eq_upIntLE_zero rfl (homObject R D x y)
      ((gammaDegreeZeroIso (connectiveHomComplex (R := R) x y)).hom
        ((standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋0⦌) s)) =
    s.val.component Finset.univ 0 Finset.univ_nonempty (by simp) := by
  have h := ConcreteCategory.congr_hom (standardDoldKanModuleIso_zero_eval (R := R) x y) s
  change (gammaDegreeZeroIso (connectiveHomComplex (R := R) x y)).hom
    ((standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋0⦌) s) =
      (standardNormalizationIso (R := R) x y).hom.f 0
        ((mooreDegreeZeroIso (standardModule (R := R) x y)).inv s) at h
  rw [h, truncationExtendedZeroInclusion_cycles]
  change (homObject R D x y).iCycles 0 ((connectiveHomComplex_zeroIso (R := R) x y).hom
    ((standardNormalizationIso (R := R) x y).hom.f 0
      ((mooreDegreeZeroIso (standardModule (R := R) x y)).inv s))) = _
  rw [standardNormalizationIso_zero_eval, standardMooreZeroIso_inv_value]

end SerrePositivity.EInfinity.ComplexLimits
