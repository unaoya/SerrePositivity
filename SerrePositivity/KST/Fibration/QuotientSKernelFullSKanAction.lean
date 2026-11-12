module
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSCoreRestriction
public import SerrePositivity.KST.Fibration.QuotientSKernelZeroFunctorMap

/-!
概要：元の相対商核円柱の全 Ex∞ 評価を、全 S• 上の同じ零値作用へ照合する。
方針：元の核包含同型で全図式族を移し、対角と strength の厳密な自然性を使う。
規約：相対核・全パラメータ・元の実包含を保持する。
使われ方：商核四角形と指定 Verdier 二胞体を比較する三角柱の境界条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 元の核上の全 S• 同型を通した core 包含は、同じ全 S• への元の実包含。 -/
theorem relativeSKernelSimplicialIso_core (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom) ≫
        (relativeSKernelSimplicialIso h).hom =
      relativeSimplicialSConstructionCoreInclusion (𝟙 A.obj) ≫
        relativeSimplicialSConstructionInclusion (𝟙 A.obj) := by
  apply NatTrans.ext
  funext n
  exact relativeSKernelCoreInclusion_fullS h n.unop.len

/-- 元の核包含同型の実現は、同じ core から全 S• への包含を厳密に回収する。 -/
theorem relativeSKernelSimplicialIso_realization_core (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    simplicialDiagonalFunctor.map
        (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom)) ≫
      simplicialDiagonalFunctor.map (relativeSKernelSimplicialIso h).hom =
        coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) := by
  rw [← Functor.map_comp, relativeSKernelSimplicialIso_core]
  rfl

/-- 元の全相対核円柱は、同じ全図式 Hom の実対角作用。 -/
theorem quotientSKernelContractionImage_fullS_diagonal (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    simplicialCylinderDiagonal _ _ (Δ[1] : SSet.{u}) (quotientSKernelContractionImage h) =
      (simplicialDiagonalFunctor.map (relativeSKernelSimplicialIso h).hom ▷ (Δ[1] : SSet.{u})) ≫
        uncurry ((quotientSKernelZeroFunctorParameter h ≫ zeroFunctorFullSDiagramFamily A C) ≫
          simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _) := by
  have he : quotientSKernelContractionImage h =
      CategoryTheory.Functor.whiskerRight (relativeSKernelSimplicialIso h).hom
        (tensorRight (Δ[1] : SSet.{u})) ≫
          diagramFamilyCylinder _ _ (Δ[1] : SSet.{u})
            (quotientSKernelZeroFunctorParameter h ≫ zeroFunctorFullSDiagramFamily A C) := by
    apply NatTrans.ext
    funext n
    exact quotientSKernelContractionImage_diagramFamily h n
  rw [he, simplicialCylinderDiagonal_precomp]
  exact congrArg (_ ≫ ·) (diagramFamilyCylinder_diagonal _ _ _
    (quotientSKernelZeroFunctorParameter h ≫ zeroFunctorFullSDiagramFamily A C))

/-- 元の相対核円柱の Ex∞ 像は、同じ全 S• 上の全零値パラメータ作用そのもの。 -/
theorem quotientSKernelContractionImage_fullSKan (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    coaugmentedTensorRightStrength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
        (simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction (i.hom ≫ q.hom)))
          (Δ[1] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialCylinderDiagonal _ _ (Δ[1] : SSet.{u})
        (quotientSKernelContractionImage h)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (relativeSKernelSimplicialIso h).hom) ▷
        (Δ[1] : SSet.{u})) ≫
        uncurry (quotientSKernelZeroFunctorParameter h ≫ zeroFunctorFullSKanFamily A C) := by
  rw [quotientSKernelContractionImage_fullS_diagonal, Functor.map_comp, ← Category.assoc,
    ← coaugmentedTensorRightStrength_naturality, Category.assoc]
  apply congrArg (_ ≫ ·)
  exact (coaugmentedClosedFamilyMap_strength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
    ((quotientSKernelZeroFunctorParameter h ≫ zeroFunctorFullSDiagramFamily A C) ≫
      simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _)).symm

end SerrePositivity.KST.Fibration
