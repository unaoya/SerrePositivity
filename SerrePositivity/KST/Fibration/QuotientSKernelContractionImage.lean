module
public import SerrePositivity.KST.Fibration.RelativeSKernelDiagonalCylinder
public import SerrePositivity.KST.Fibration.QuotientSKernelPullback

/-! # 元の相対 S 核円柱の、同じ商比較による全単体的な像 -/

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

/-- 元の相対核円柱の全単体を、商四角形の同じ上辺へ送る。 -/
def quotientSKernelContractionImage (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    relativeSimplicialSConstruction (i.hom ≫ q.hom) ⋙ tensorRight (Δ[1] : SSet.{u}) ⟶
      simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor :=
  relativeSKernelContractionCylinder h ≫
    relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q

/-- 同じ全単体的商像の対角は、元の実対角円柱の同じ商への後合成と厳密に一致。 -/
theorem quotientSKernelContractionImage_diagonal (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    simplicialCylinderDiagonal _ _ _ (quotientSKernelContractionImage h) =
      relativeSKernelDiagonalCylinder h ≫ simplicialDiagonalFunctor.map
        (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q) := by
  exact simplicialCylinderDiagonal_postcomp (relativeSKernelContractionCylinder h) _

/-- 元の相対核の同じ零図式点を、同じ商比較へ送った実際の点。 -/
def quotientSKernelDiagonalPoint (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    𝟙_ SSet.{u} ⟶ simplicialDiagonalFunctor.obj
      (simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) :=
  relativeSKernelDiagonalPoint h ≫ simplicialDiagonalFunctor.map
    (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q)

/-- 商比較の元の上辺の収縮は、同じ全単体的円柱の像そのものである。 -/
def quotientSKernelDiagonalContractionImage (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    SSet.Homotopy (toUnit _ ≫ quotientSKernelDiagonalPoint h)
      (simplicialDiagonalFunctor.map
        (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q)) where
  h := simplicialCylinderDiagonal _ _ _ (quotientSKernelContractionImage h)
  h₀ := by
    rw [quotientSKernelContractionImage_diagonal, ← Category.assoc,
      relativeSKernelDiagonalCylinder_zero, Category.assoc]
    rfl
  h₁ := by
    rw [quotientSKernelContractionImage_diagonal, ← Category.assoc,
      relativeSKernelDiagonalCylinder_one, Category.id_comp]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.KST.Fibration
