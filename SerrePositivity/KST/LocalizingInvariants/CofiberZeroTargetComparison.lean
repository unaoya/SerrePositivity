module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberZeroTargetComparison

public import SerrePositivity.KST.LocalizingInvariants.SuspensionExactFunctor
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyComparison

/-!
概要：零終点矢印族の cofiber は、元の始点の suspension と全関手として同型。
方針：零終点矢印の始点評価の同値で同じ切断と比較し、cofiber 関手で写す。
規約：対象ごとの同型に弱めない。使われ方：差の C 側を shift に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
attribute [local instance] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroTargetComparisonQuasicategory
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (ha : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (a.app (Opposite.op ⦋0⦌) x))

def zeroTargetArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X) := by
  let a₀ : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrows X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow a ha
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a₀
      ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrowSection X) := by
    apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X)).postcompose A
      ).isFullyFaithful.preimageVertexIso
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X)
      (((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrowSection X) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrowSection_source, Category.comp_id]
    exact eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]))
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow).ι
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow, Category.assoc, a₀, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι] using hi

def cofiberZeroTargetIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X a)
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map X) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (zeroTargetArrowComparison X a ha)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (𝟙 _))
  exact CofiberFamily.compositionIso X a ≪≫ (by
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map, Category.assoc] using h)

end SerrePositivity.KST.LocalizingInvariants
