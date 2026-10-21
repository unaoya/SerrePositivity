module

public import SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionPrism
public import SerrePositivity.InfinityCategories.F1B.KanFinalFiberRetraction

/-!
概要：標準単体上の cocartesian fibration の最終 fiber の包含は、亜群化後に実同値。
方針：既存の最終 fiber の厳密な退縮と相対 prism を全辺局所化へ移す。
規約：元の包含の亜群化を順方向に保持。使われ方：分母上の終点 fiber と全空間の比較。
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

def finalFiberGroupoidCompletionEquivalence (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ (Δ[n] : SSet.{u})) [CocartesianFibration p] :
    QCatEquivalence (groupoidCompletion (vertexFiber p (stdSimplex.obj₀Equiv.symm (Fin.last n))))
      (groupoidCompletion E) := by
  let R := Classical.choose (exists_kanFinalFiberRetraction n p)
  let H := Classical.choose (Classical.choose_spec (exists_kanFinalFiberRetraction n p))
  have h := Classical.choose_spec
    (Classical.choose_spec (exists_kanFinalFiberRetraction n p))
  exact groupoidCompletionEquivalenceOfPrismRetraction
    (vertexFiberι p (stdSimplex.obj₀Equiv.symm (Fin.last n))) R h.1 H h.2.1 h.2.2.1

lemma finalFiberGroupoidCompletionEquivalence_hom (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ (Δ[n] : SSet.{u})) [CocartesianFibration p] :
    (finalFiberGroupoidCompletionEquivalence n p).hom =
      groupoidCompletionMapOf (vertexFiberι p (stdSimplex.obj₀Equiv.symm (Fin.last n))) := rfl

lemma finalFiberInclusion_groupoidCompletion_isEquivalence (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ (Δ[n] : SSet.{u})) [CocartesianFibration p] :
    IsSimplicialHomotopyEquivalence
      (groupoidCompletionMapOf (vertexFiberι p (stdSimplex.obj₀Equiv.symm (Fin.last n)))) :=
  (finalFiberGroupoidCompletionEquivalence n p).isQCatEquivalence
    |>.isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
