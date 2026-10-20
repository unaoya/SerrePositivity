module
public import SerrePositivity.InfinityCategories.Derived.LocalizationFunctorExtension
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus
/-!
概要：全前合成の充満忠実性と実延長から局所化を判定する。
方針：反転関手への全包含を消去し、全反転関手圏の同値を得る。
規約：任意の quasicategory 標的。使われ方：平坦分解による局所化の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
/-- 全前合成が充満忠実で全反転関手が実延長を持つなら、同じ射は局所化。 -/
lemma isLocalization_of_fullyFaithful_extensions {X Q : SSet.{u}} (q : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hq : InvertsEdges q W)
    (hf : ∀ (Y : SSet.{u}) [Quasicategory Y], IsFullyFaithful ((pre q).app Y))
    (he : ∀ (Y : SSet.{u}) [Quasicategory Y] (F : X ⟶ Y), InvertsEdges F W →
      ∃ G : Q ⟶ Y, Nonempty (FunctorIso (q ≫ G) F)) : IsLocalization q W := by
  refine ⟨hq, fun Y _ => ?_⟩
  apply isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · have hi := isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj Y)
      (IsInvertingFunctorVertex X Y W)
    change IsFullyFaithful (invertingFunctors X Y W).ι at hi
    apply hi.cancel_right
    rw [localizationPrecomposition_ι]
    exact hf Y
  · exact localizationPrecomposition_isEssentiallySurjective_of_extensions q W hq (he Y)
end SerrePositivity.InfinityCategories
