module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationComparisonProjection
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPrecompositionCoherence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory Bicategory
open MonoidalClosed SSet
open scoped _root_.Simplicial

/-- trivial Kan fibration の指定比較を底へ後合成した射は、Arrow として恒等。 -/
lemma trivialKanEquivalence_homInvIso_projection_arrow {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration p).homInvIso.postcomp p).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    eqToIso.inv, eqToHom_refl, Category.id_comp, Category.comp_id]
  let q := (ihom E).map p
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map, Functor.mapIso]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.vertexFiberHo_projection_arrow q b _

/-- 厳密切断の指定比較を射影で前合成した射も、Arrow として恒等。 -/
lemma trivialKanEquivalence_invHomIso_precomp_arrow {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration p).invHomIso.precomp p).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))) := by
  let s := Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section p)
  have hs : s ≫ p = 𝟙 B := Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section p)
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (eqToIso
    (congrArg (fun f : B ⟶ B ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) hs)) p).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.precomp_eqToIso hs p]
  simp only [eqToIso.hom]
  rw [← Category.comp_id (eqToHom _), Arrow.arrow_mk_eqToHom_comp]
  rfl

/-- trivial Kan fibration の同じ指定二比較は、全関手上の三角整合性を満たす。 -/
lemma trivialKanEquivalence_comparison_triangle {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration p).homInvIso.postcomp p) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration p).invHomIso.precomp p) := by
  apply Iso.ext
  apply (Arrow.mk_injective _ _)
  exact (trivialKanEquivalence_homInvIso_projection_arrow p).trans
    (trivialKanEquivalence_invHomIso_precomp_arrow p).symm
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
