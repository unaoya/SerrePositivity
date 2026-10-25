module

public import SerrePositivity.InfinityCategories.F1B.Localization.Localization
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullRestrictionPullback
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace

/-!
概要：辺を反転する関手の全圏に、left fibration の後合成を制限する。
方針：可逆性の反映から反転条件の逆像を照合し、実際の pullback として表す。
規約：指定辺集合を保ち、元の全後合成との可換性は厳密な等号。
使われ方：局所化に沿う相対切断の制限を、同じ底の fiber で判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- left fibration による後合成は、元の全関手の辺の反転を反映する。 -/
lemma InvertsEdges.of_leftFibration_comp {N E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (F : N ⟶ E) {W : Set (N _⦋1⦌)} (h : InvertsEdges (F ≫ p) W) : InvertsEdges F W := by
  intro s hs
  apply leftFibration_reflects_invertibleEdge p
  exact h hs

/-- 指定辺を反転する全関手圏での後合成。 -/
def invertingFunctorPostcomp {N E B : SSet.{u}} (p : E ⟶ B) (W : Set (N _⦋1⦌)) :
    (invertingFunctors N E W : SSet.{u}) ⟶ invertingFunctors N B W :=
  fullSubcomplexLift (IsInvertingFunctorVertex N B W)
    ((invertingFunctors N E W).ι ≫ (ihom N).map p) (by
      intro v
      obtain ⟨F, hF⟩ := (functorVertexEquiv N E).surjective v.val
      have hv := fullSubcomplexOnVertices_vertex v
      change IsInvertingFunctorVertex N E W v.val at hv
      unfold IsInvertingFunctorVertex at hv ⊢
      change InvertsEdges ((functorVertexEquiv N B).symm
        (((ihom N).map p).app (Opposite.op ⦋0⦌) v.val)) W
      rw [← hF] at hv ⊢
      rw [Equiv.symm_apply_apply] at hv
      change InvertsEdges ((functorVertexEquiv N B).symm
        ((functorVertexEquiv N B) (F ≫ p))) W
      rw [Equiv.symm_apply_apply]
      exact hv.comp p)

/-- 包含後の後合成は、元の全関手圏の後合成そのもの。 -/
lemma invertingFunctorPostcomp_ι {N E B : SSet.{u}} (p : E ⟶ B) (W : Set (N _⦋1⦌)) :
    invertingFunctorPostcomp p W ≫ (invertingFunctors N B W).ι =
      (invertingFunctors N E W).ι ≫ (ihom N).map p := fullSubcomplexLift_ι _ _ _

/-- left fibration による反転関手圏の後合成は、全後合成の厳密な pullback。 -/
lemma invertingFunctorPostcomp_isPullback {N E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (W : Set (N _⦋1⦌)) :
    IsPullback (invertingFunctors N E W).ι (invertingFunctorPostcomp p W)
      ((ihom N).map p) (invertingFunctors N B W).ι := by
  apply fullRestriction_isPullback _ _ _ _ (invertingFunctorPostcomp_ι p W)
  intro v hv
  obtain ⟨F, rfl⟩ := (functorVertexEquiv N E).surjective v
  change InvertsEdges F W
  change InvertsEdges ((functorVertexEquiv N B).symm
    ((functorVertexEquiv N B) (F ≫ p))) W at hv
  rw [Equiv.symm_apply_apply] at hv
  exact hv.of_leftFibration_comp p F

/-- 制限した後合成も left fibration。 -/
instance invertingFunctorPostcomp_leftFibration {N E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (W : Set (N _⦋1⦌)) : LeftFibration (invertingFunctorPostcomp p W) :=
  ⟨leftFibrations.of_isPullback (invertingFunctorPostcomp_isPullback p W)
    LeftFibration.mem⟩

end SerrePositivity.InfinityCategories
