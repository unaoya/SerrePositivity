module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanZeroAdjunction
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorHom

/-!
# 実正規化鎖 Hom と正規化単体 Hom の零次数評価

概要：元の実 DK Hom の零次数像を、同じ smart 切断鎖射と同じ自由生成元で計算する。
方針：同じ随伴の零次数公式を実正規化鎖 Hom 同値と標準単体評価へ適用する。
規約：元の線形化・生成元・Hom 同値を保つ。
使われ方：元の augmentation の零次数像が恒等辺となることの成分計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedChainsHomEquiv_zero_eval (S : SSet.{0}) (H : Complex A)
    (f : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj S ⟶ H) :
    (_root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv A S H f).app (Opposite.op ⦋0⦌) ≫
      (_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom =
    (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S)).inv ≫
      (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S H f).f 0 :=
  _root_.SerrePositivity.ComplexLimits.doldKanAdjunction_zero_eval _ _ (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S H f)

lemma normalizedSimplexHomEquiv_zero_eval (H : Complex A)
    (f : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj ⦋0⦌) ⟶ H) :
    (_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A H ⦋0⦌ f) =
    (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A (SSet.stdSimplex.obj ⦋0⦌) H f).f 0
      ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
        (SSet.stdSimplex.obj ⦋0⦌))).inv (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A ⦋0⦌)) := by
  exact ConcreteCategory.congr_hom
    (_root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv_zero_eval A (SSet.stdSimplex.obj ⦋0⦌) H f)
    (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A ⦋0⦌)

end SerrePositivity.ComplexLimits
