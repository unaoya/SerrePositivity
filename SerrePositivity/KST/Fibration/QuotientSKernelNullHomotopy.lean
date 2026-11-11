module
public import SerrePositivity.KST.Fibration.QuotientSKernelContractionImage

/-! # 元の包含・商の core S• 実現射の合成に対する、同じ相対核円柱の零化 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 元の包含と商の合成を零化する円柱は、同じ相対核包含による元の円柱の制限。 -/
def quotientSKernelNullCylinder (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    simplicialDiagonalFunctor.obj
      (simplicialSConstruction A.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) ⊗ (Δ[1] : SSet.{u}) ⟶
        simplicialDiagonalFunctor.obj
          (simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) :=
  (simplicialDiagonalFunctor.map
    (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom)) ▷ (Δ[1] : SSet.{u})) ≫
      (quotientSKernelDiagonalContractionImage h).h

/-- 同じ制限円柱の零端は、元の相対零図式の商像で指定した同じ点を通る。 -/
theorem quotientSKernelNullCylinder_zero (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    SSet.ι₀ ≫ quotientSKernelNullCylinder h =
      toUnit _ ≫ quotientSKernelDiagonalPoint h := by
  rw [quotientSKernelNullCylinder, SSet.ι₀_comp_assoc,
    (quotientSKernelDiagonalContractionImage h).h₀, ← Category.assoc]
  have ht : simplicialDiagonalFunctor.map
      (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom)) ≫ toUnit _ =
        toUnit _ := isTerminalTensorUnit.hom_ext _ _
  rw [ht]

/-- 同じ制限円柱の終端は、元の包含の実現射と元の商の実現射の実合成。 -/
theorem quotientSKernelNullCylinder_one (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    SSet.ι₁ ≫ quotientSKernelNullCylinder h =
      simplicialDiagonalFunctor.map (coreSExactMap i) ≫
        simplicialDiagonalFunctor.map (coreSExactMap q) := by
  rw [quotientSKernelNullCylinder, SSet.ι₁_comp_assoc,
    (quotientSKernelDiagonalContractionImage h).h₁]
  exact (quotientSKernelRealizationSquare i q).w

/-- 元の包含・商の合成に対する、指定した相対核円柱から来る具体的な零化。 -/
def quotientSKernelNullHomotopy (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    SSet.Homotopy (toUnit _ ≫ quotientSKernelDiagonalPoint h)
      (simplicialDiagonalFunctor.map (coreSExactMap i) ≫
        simplicialDiagonalFunctor.map (coreSExactMap q)) where
  h := quotientSKernelNullCylinder h
  h₀ := quotientSKernelNullCylinder_zero h
  h₁ := quotientSKernelNullCylinder_one h
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.KST.Fibration
