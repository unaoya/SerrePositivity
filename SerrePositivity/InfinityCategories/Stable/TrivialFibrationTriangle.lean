module
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationComparisonProjection
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoPrecompositionCoherence
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
/-!
概要：trivial Kan fibration の指定二比較の三角整合性を、元の全関手上で示す。
方針：実 fiber の射影の恒等性と、指定二比較の前後合成を照合する。
規約：元の指定射と同型を保持する。使われ方：入力分解の同じ余単位の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Bicategory
open MonoidalClosed SSet
open scoped Simplicial

/-- trivial Kan fibration の指定比較を底へ後合成した射は、Arrow として恒等。 -/
lemma trivialKanEquivalence_homInvIso_projection_arrow {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p] :
    Arrow.mk ((qCatEquivalenceOfTrivialKanFibration p).homInvIso.postcomp p).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex p))) := by
  unfold qCatEquivalenceOfTrivialKanFibration
  simp only [FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    eqToIso.inv, eqToHom_refl, Category.id_comp, Category.comp_id]
  let q := (ihom E).map p
  let b := functorVertex p
  have hc := vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  dsimp only [VertexIso.map, Functor.mapIso]
  exact vertexFiberHo_projection_arrow q b _

/-- 厳密切断の指定比較を射影で前合成した射も、Arrow として恒等。 -/
lemma trivialKanEquivalence_invHomIso_precomp_arrow {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p] :
    Arrow.mk ((qCatEquivalenceOfTrivialKanFibration p).invHomIso.precomp p).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex p))) := by
  let s := Classical.choose (trivialKanFibration_exists_section p)
  have hs : s ≫ p = 𝟙 B := Classical.choose_spec (trivialKanFibration_exists_section p)
  change Arrow.mk (FunctorIso.precomp (eqToIso
    (congrArg (fun f : B ⟶ B ↦ HomotopyCategory.mk (functorVertex f)) hs)) p).hom = _
  rw [FunctorIso.precomp_eqToIso hs p]
  simp only [eqToIso.hom]
  rw [← Category.comp_id (eqToHom _), Arrow.arrow_mk_eqToHom_comp]
  rfl

/-- trivial Kan fibration の同じ指定二比較は、全関手上の三角整合性を満たす。 -/
lemma trivialKanEquivalence_comparison_triangle {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p] :
    ((qCatEquivalenceOfTrivialKanFibration p).homInvIso.postcomp p) =
      ((qCatEquivalenceOfTrivialKanFibration p).invHomIso.precomp p) := by
  apply Iso.ext
  apply (Arrow.mk_injective _ _)
  exact (trivialKanEquivalence_homInvIso_projection_arrow p).trans
    (trivialKanEquivalence_invHomIso_precomp_arrow p).symm
end SerrePositivity.InfinityCategories
