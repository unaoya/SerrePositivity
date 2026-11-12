module

public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransIso
public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitProbeFunctor
public import SerrePositivity.EInfinity.ComplexLimits.SemifreeClosedDerivedComparison

/-!
# 元の複体 probe と半自由頂点の実 D(R) 比較

概要：同じ probe augmentation を全源で反転し、半自由入力では元の D(R) 頂点へ戻す。
方針：元の自然変換比較と同じ半自由閉 nerve の全比較を使う。
規約：元の導来源と augmentation を保持する。
使われ方：自由 probe への導来単位の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

def complexProbeDerivedSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (framedLimitProbeFunctor A) ≫ complexOrdinaryDerivedSource A)
      (complexOrdinaryDerivedSource A) := by
  have e := complexOrdinaryDerivedNatTransIso A (framedLimitProbeComparisonNatTrans A)
    (framedLimitProbeComparison_quasiIso A)
  have hid : nerveMap (𝟭 (Complex A)) = 𝟙 (nerve (Complex A)) :=
    nerveFunctor.map_id (Cat.of (Complex A))
  rw [hid, Category.id_comp] at e
  exact e

def complexOrdinaryDerivedSource_semifreeVertexIso (K : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex K.val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex K) := by
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ForgetEnrichment.of (Complex A) K : ClosedCategory A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A))
  have h₀ : (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A)).app (Opposite.op ⦋0⦌) z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex K.val := by
    change (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (ForgetEnrichment.of (Complex A) K)) = _
    rw [nerveMap_app_mk₀]
    rfl
  have h₁ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A)).app (Opposite.op ⦋0⦌) z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex K := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A)).injective
    rfl
  exact (eqToIso (congrArg HomotopyCategory.mk
    (congrArg ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)) h₀))).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (semifreeClosedDerivedSourceIso A) z ≪≫
        eqToIso (congrArg HomotopyCategory.mk h₁)

end SerrePositivity.EInfinity.ComplexLimits
