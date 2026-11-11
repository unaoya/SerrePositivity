module
public import SerrePositivity.KST.Fibration.StableSingleSCoreFamily
public import SerrePositivity.KST.Fibration.QuotientSKernelContractionFullS
public import SerrePositivity.KST.Fibration.QuotientSKernelNullHomotopy

/-! # 商核からの元の零化円柱と、K-S• の同じ全 core S• 入力族との厳密な照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 元の商核円柱を、元の core 包含によって全単体で制限した実零化円柱。 -/
def quotientSKernelNullNatTrans (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    (simplicialSConstruction A.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) ⋙
        tensorRight (Δ[1] : SSet.{u}) ⟶
      simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor :=
  CategoryTheory.Functor.whiskerRight
    (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom))
      (tensorRight (Δ[1] : SSet.{u})) ≫ quotientSKernelContractionImage h

/-- 全単体的零化円柱の対角は、元の包含・商の実現合成の同じ零化円柱である。 -/
theorem quotientSKernelNullNatTrans_diagonal (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    simplicialCylinderDiagonal _ _ _ (quotientSKernelNullNatTrans h) =
      quotientSKernelNullCylinder h :=
  simplicialCylinderDiagonal_precomp _ _

/-- 元の core 包含は、核上の同じ包含同型を通って元の全 S_n 包含を回収する。 -/
theorem relativeSKernelCoreInclusion_fullS (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    relativeDiagramCoreInclusion (i.hom ≫ q.hom) (sComponentEvaluation A.obj n) ≫
        (relativeSKernelTopIso h n).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n A.obj)).ι := by
  rw [relativeSKernelTopIso_hom_inclusion]
  rfl

/-- 元の零化円柱の全段は、K-S• の同じ全 Kan Hom 族の core 作用そのもの。 -/
theorem quotientSKernelNullNatTrans_app (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (n : SimplexCategoryᵒᵖ) :
    (quotientSKernelNullNatTrans h).app n =
      uncurry (zeroEndPostcompFamily
        (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
          (verdierSequenceComposite_zero h) ≫
            ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map
              (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι).1
  change ((relativeDiagramCoreInclusion (i.hom ≫ q.hom)
    (sComponentEvaluation A.obj n.unop.len) ▷ (Δ[1] : SSet.{u})) ≫
      (quotientSKernelContractionImage h).app n) ≫ _ = _
  rw [Category.assoc, quotientSKernelContractionImage_fullS,
    ← Category.assoc, ← comp_whiskerRight, relativeSKernelCoreInclusion_fullS h]
  exact (zeroEndPostcompCoreSAction_inclusion _ _ n).symm

end SerrePositivity.KST.Fibration
