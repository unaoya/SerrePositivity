module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionPrism
public import SerrePositivity.KST.LocalizingInvariants.InitialFiberRetraction

/-!
概要：標準単体上の cartesian fibration の最初の fiber の包含は、亜群化後に実同値。
方針：最初の fiber の厳密な退縮と逆向きの prism を全辺局所化へ移す。
規約：元の包含を順方向に保持。使われ方：分母上の始点 fiber と全空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def initialFiberGroupoidCompletionEquivalence (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion E) := by
  let R := Classical.choose (exists_initialFiberRetraction n p)
  let H := Classical.choose (Classical.choose_spec (exists_initialFiberRetraction n p))
  have h := Classical.choose_spec
    (Classical.choose_spec (exists_initialFiberRetraction n p))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfReversePrismRetraction
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))) R h.1 H h.2.1 h.2.2.1

lemma initialFiberGroupoidCompletionEquivalence_hom (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] :
    (initialFiberGroupoidCompletionEquivalence n p).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))) := rfl

lemma initialFiberInclusion_groupoidCompletion_isEquivalence (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) :=
  (initialFiberGroupoidCompletionEquivalence n p).isQCatEquivalence
    |>.isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
