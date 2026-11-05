module

public import SerrePositivity.KST.LocalizingInvariants.FinalFiberGroupoidCompletion
public import SerrePositivity.KST.LocalizingInvariants.InitialFiberGroupoidCompletion
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-!
概要：区間上の両側 fibration の両端 fiber は亜群化後に同値で、実輸送もその同値を与える。
方針：両包含を全空間への同値にし、輸送 prism の自然同型を使って右因子を消去する。
規約：与えた輸送関手を変更しない。使われ方：分母上の実輸送の亜群化の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def intervalFiberGroupoidCompletionEquivalence {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [CartesianFibration p] [CocartesianFibration p] :
    QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
      (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) :=
  (initialFiberGroupoidCompletionEquivalence 1 p).trans
    (finalFiberGroupoidCompletionEquivalence 1 p).symm

lemma intervalFiberTransport_groupoidCompletion_isEquivalence {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [CartesianFibration p] [CocartesianFibration p]
    (f : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf f) := by
  let i₀ := vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let i₁ := vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have h : FunctorIso (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf f ≫ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf i₁)
      (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf i₀) :=
    _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf_compIso f i₁ ≪≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf_functorHomIso (_root_.SerrePositivity.InfinityCategories.Derived.Localization.functorHomOfPrism H h₀ h₁)).symm
  have h₀e : IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf i₀) :=
    (initialFiberGroupoidCompletionEquivalence 1 p).isQCatEquivalence
  have h₁e : IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf i₁) :=
    (finalFiberGroupoidCompletionEquivalence 1 p).isQCatEquivalence
  exact (h₁e.cancel_right (h₀e.ofFunctorIso h.symm)).isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
