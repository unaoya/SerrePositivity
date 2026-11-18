module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomZeroEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendedTruncationZeroInclusion

/-!
# 実正規化 Hom の零次数像の元の複体射による直接評価

概要：元の Γ 零次数像を同じ切断包含で戻すと、元の複体射を同じ生成元で評価した値になる。
方針：元の切断 Hom 回収式と同じ Moore/延長零次数同型を相殺する。
規約：入力単体集合は小さい元の標準単体、係数環の宇宙は任意。
使われ方：同じ augmentation の零次数像を恒等辺へ同定する成分計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.AlgebraicTopology _root_.SSet
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedChainsTruncationHomEquiv_zero (S : SSet.{0}) (H : Complex A)
    (f : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj S ⟶ H) :
    (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S H f).f 0 ≫
      _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
        _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl H =
    (((normalizedMooreComplex (ModuleCat A)).obj ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S)).extendXIso
      ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).inv ≫
      f.f 0 :=
  _root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape_zero A _ _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl _ H f

def normalizedSimplexZeroGenerator :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj ⦋0⦌)).X 0 :=
  let W := (_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj ⦋0⦌)
  let L := (normalizedMooreComplex (ModuleCat A)).obj W
  (L.extendXIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).inv
    ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A ⦋0⦌))

lemma normalizedSimplexHomEquiv_zero_raw (H : Complex A)
    (f : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj ⦋0⦌) ⟶ H) :
    _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
      _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl H
      ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A H ⦋0⦌ f)) = f.f 0 (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A) := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_zero_eval]
  exact ConcreteCategory.congr_hom
    (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv_zero A (SSet.stdSimplex.obj ⦋0⦌) H f)
    ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
      (SSet.stdSimplex.obj ⦋0⦌))).inv (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A ⦋0⦌))

end SerrePositivity.ComplexLimits
