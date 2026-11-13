module
public import SerrePositivity.KST.Fibration.WeakStringOctahedronRelative
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexFunctorFaithful

/-! # 核内の八面体比較関手の元の辺との照合

始点は第一短辺の共通 cofiber 関手そのもの、cofiber は第二短辺の共通 cofiber と
核の実関手圏で自然同型である。比較は全高次パラメーターを保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 核内の比較関手の始点は、元の第一短辺の共通 cofiber 完全関手そのもの。 -/
lemma weakStringOctahedronSourceExact_eq {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    weakStringOctahedronSourceExact q β =
      weakStringKernelCofiber q (SimplexCategory.δ (2 : Fin 3) ≫ β) := by
  apply Subtype.ext
  have : Mono (closedStableInclusion (kernelClosedPredicate q)).val :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (sInputModel B).carrier
      (kernelClosedPredicate q).predicate).ι)
  apply (cancel_mono (closedStableInclusion (kernelClosedPredicate q)).val).1
  change (weakStringOctahedronRelativeFamily q β ≫
    relativeCofiberSubobjectMap (kernelClosedPredicate q) (kernelClosedPredicate q)) ≫ _ = _
  rw [Category.assoc, relativeCofiberSubobjectMap_ι, ← Category.assoc,
    weakStringOctahedronRelativeFamily_ι]
  change cofiberFamilyUntranspose _ _ ≫
    (cofiberStableEvaluation (sInputModel B)
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)).val = _
  rw [cofiberFamilyUntranspose_corner]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 0 0) = _
  rw [(weakStringOctahedronFamily q β).last_source, weakStringCofiberFamily_quotient]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm_apply_apply _

/-- 核値の cofiber 評価を含めると、元の比較列の同じ頂点が表す関手を回収する。 -/
lemma weakStringOctahedronTargetExact_ambient {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    (weakStringOctahedronTargetExact q β).val ≫
      (closedStableInclusion (kernelClosedPredicate q)).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 1 1) := by
  change (weakStringOctahedronRelativeFamily q β ≫
    relativeCofiberQuotientMap (kernelClosedPredicate q) (kernelClosedPredicate q)) ≫ _ = _
  rw [Category.assoc, relativeCofiberQuotientMap_ι, ← Category.assoc,
    weakStringOctahedronRelativeFamily_ι]
  exact cofiberFamilyUntranspose_corner _ _
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)

/-- 核内の cofiber 評価は、第二短辺の元の共通 cofiber と全族で自然同型。 -/
def weakStringOctahedronTargetExact_comparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakStringOctahedronTargetExact q β).val
      (weakStringKernelCofiber q (SimplexCategory.δ (0 : Fin 3) ≫ β)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexFunctorInclusion (weakStringCategory q n) B.obj
    (kernelClosedPredicate q).predicate).preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((weakStringOctahedronTargetExact q β).val ≫
    (closedStableInclusion (kernelClosedPredicate q)).val)
      ((weakStringKernelCofiber q (SimplexCategory.δ (0 : Fin 3) ≫ β)).val ≫
        (closedStableInclusion (kernelClosedPredicate q)).val)
  rw [weakStringOctahedronTargetExact_ambient]
  have he := cofiberFamilyCornerIso (weakStringOctahedronFamily_nextComparison q β)
  rw [weakStringCofiberFamily_quotient] at he
  have hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 1 1)) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 1 1 :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm _)) _
  rw [hi, (weakStringOctahedronFamily q β).last_target]
  exact he

end SerrePositivity.KST.Fibration
