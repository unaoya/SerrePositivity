module

public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberReflection

/-!
概要：left fibrations の底上の前合成同値は、任意の底変換で保たれる。
方針：元の比較の fiber 同値を反映し、底変換の厳密な fiber 同型で移して全空間を判定する。
規約：元の底は quasicategory。制限先の底には充填性を仮定しない。
使われ方：twisted arrow 全体の復元射を、同じ終点固定の射影へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance {E B K : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (g : K ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 元の底上の比較の前合成同値性は、任意の底変換後にも保たれる。 -/
lemma fiberComparisonBaseChange_isPrecompositionEquivalence
    {E F B K : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (he : IsPrecompositionEquivalence f) (g : K ⟶ B) :
    IsPrecompositionEquivalence (fiberComparisonBaseChange p q f hf g) := by
  apply isPrecompositionEquivalence_of_leftFibration_fibers (pullback.snd p g)
    (pullback.snd q g) (fiberComparisonBaseChange p q f hf g)
    (fiberComparisonBaseChange_projection p q f hf g)
  intro k
  apply (qCatEquivalenceOfIso (vertexFiberPullbackIso q g k)).isQCatEquivalence.cancel_right
  change IsQCatEquivalence
    (vertexFiberMap (pullback.snd p g) (pullback.snd q g)
      (fiberComparisonBaseChange p q f hf g) (fiberComparisonBaseChange_projection p q f hf g) k ≫
      (vertexFiberPullbackIso q g k).hom)
  rw [fiberComparisonBaseChange_fiber]
  exact (qCatEquivalenceOfIso (vertexFiberPullbackIso p g k)).isQCatEquivalence.comp
    (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p q f hf he _)

end SerrePositivity.InfinityCategories
