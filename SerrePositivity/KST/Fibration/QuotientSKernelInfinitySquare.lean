module
public import SerrePositivity.KST.Fibration.QuotientSKernelPullback
public import SerrePositivity.KST.Fibration.HomotopyPullbackInfinitySquare

/-! # 商実現比較を正確に入力した、元の S• 核四角形の native な ∞ 引き戻し -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)

/-- 元の core S 包含と商射を持つ核四角形を、同じ全 Ex∞ coherent 四角形へ送る。 -/
def quotientSKernelInfinitySquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  exInfinityCommSqInfinitySquare (quotientSKernelRealizationSquare i q)

/-- 元の core S(A) の実現の Kan 値を、同じ四角形の頂点として厳密に回収する。 -/
theorem quotientSKernelInfinitySquare_apex :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (quotientSKernelInfinitySquare i q) 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (simplicialDiagonalFunctor.obj
        (simplicialSConstruction A.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor)),
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :=
  kanCommSqInfinitySquare_apex _

/-- 未証明の商実現比較を正確に入力したとき、同じ全 coherent 核四角形は引き戻し。 -/
theorem quotientSKernelInfinitySquare_isPullback (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (hq : IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (quotientSKernelInfinitySquare i q) :=
  exInfinityCommSqInfinitySquare_isPullback _
    (quotientSKernelRealizationSquare_homotopyPullback i q h hq)

end SerrePositivity.KST.Fibration
