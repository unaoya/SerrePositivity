module
public import SerrePositivity.KST.Fibration.WeakStringOctahedronEvaluations
public import SerrePositivity.KST.Fibration.KernelMultiAddition

/-! # 八面体比較列の中間評価と全正有限反復加法性

中間評価を核に値を持つ完全関手として構成し、元の長辺の共通 cofiber と比較する。
K-1 の加法性を同じ相対完全関手に適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の八面体の中間評価を、核に値を持つ完全関手として保持する。 -/
def weakStringOctahedronMiddleExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    weakStringModel q n ⟶ closedStableModel (kernelClosedPredicate q) :=
  weakStringOctahedronRelativeExact q β ≫ kernelRelativeMiddle q

/-- 中間評価は、包含後に元の実比較列の同じ頂点を回収する。 -/
lemma weakStringOctahedronMiddleExact_ambient {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    (weakStringOctahedronMiddleExact q β).val ≫
      (closedStableInclusion (kernelClosedPredicate q)).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm
          (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 1 0) := by
  change (weakStringOctahedronRelativeFamily q β ≫ kernelRelativeMiddleMap q) ≫ _ = _
  rw [Category.assoc, kernelRelativeMiddleMap_ι, ← Category.assoc,
    weakStringOctahedronRelativeFamily_ι]
  exact cofiberFamilyUntranspose_corner _ _
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0)

/-- 元の長辺の共通 cofiber と中間評価は、核の実関手圏で自然同型である。 -/
def weakStringOctahedronMiddleExact_comparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakStringOctahedronMiddleExact q β).val
      (weakStringKernelCofiber q (SimplexCategory.δ (1 : Fin 3) ≫ β)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexFunctorInclusion (weakStringCategory q n) B.obj
    (kernelClosedPredicate q).predicate).preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((weakStringOctahedronMiddleExact q β).val ≫
    (closedStableInclusion (kernelClosedPredicate q)).val)
      ((weakStringKernelCofiber q (SimplexCategory.δ (1 : Fin 3) ≫ β)).val ≫
        (closedStableInclusion (kernelClosedPredicate q)).val)
  rw [weakStringOctahedronMiddleExact_ambient]
  have he := cofiberFamilyCornerIso (weakStringOctahedronFamily_compositeComparison q β)
  rw [weakStringCofiberFamily_quotient] at he
  have hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 1 0)) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 1 0 :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm _)) _
  rw [hi, (weakStringOctahedronFamily q β).last_middle]
  exact he

/-- 同じ実八面体比較関手に対する K-1 の全正有限反復加法性。 -/
lemma weakStringOctahedronMultiAddition {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) (r : ℕ) :
    AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map
      (weakStringOctahedronMiddleExact q β)) =
        AnodyneHomotopy.anodyneQ.map (lift
          ((multiRealizationFunctor (r + 1)).map
            (weakStringKernelCofiber q (SimplexCategory.δ (2 : Fin 3) ≫ β)))
          ((multiRealizationFunctor (r + 1)).map (weakStringOctahedronTargetExact q β))) ≫
              kernelMultiAddition q r := by
  have h := kernelMultiAddition_of_relativeFunctor q r (weakStringOctahedronRelativeExact q β)
  change AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map
    (weakStringOctahedronMiddleExact q β)) =
      AnodyneHomotopy.anodyneQ.map (lift
        ((multiRealizationFunctor (r + 1)).map (weakStringOctahedronSourceExact q β))
        ((multiRealizationFunctor (r + 1)).map (weakStringOctahedronTargetExact q β))) ≫
          kernelMultiAddition q r at h
  rw [weakStringOctahedronSourceExact_eq] at h
  exact h

end SerrePositivity.KST.Fibration
