module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedRealizationValueHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoValueComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoValueCurry
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOrdinaryLift

/-!
概要：指定した係数反転比較の同じ値を、共通解像の左右の比較の値として表示する。
方針：元の大域比較の逆・合成を評価し、既存の同じ端点移送だけを相殺する。
規約：HTT §1.1.5・Kerodon §3.1、§5.6（Tag 028T）の構成の特殊な照合。
  源の局所Kan性を仮定せず、指定された比較を保つ。
使われ方：P3-C1PNの元の反転比較の類を通常の自然変換で計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

private lemma value_symm {K Y : SSet.{u}} {F G : K ⟶ Y} (e : FunctorIso F G) (x : K _⦋0⦌) :
    functorIsoValue e.symm x = (functorIsoValue e x).symm := by
  apply Iso.ext
  exact (functorIsoValue_inv e x).symm

private lemma right_realization_heq {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J) :
    HEq D.edgewiseRightRealizationIso
      (D.edgewiseRightComparison.realizationIso (fun j X =>
        isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj X.val).obj))) := by
  unfold KanEnrichedDiagram.edgewiseRightRealizationIso
  dsimp only
  have hcast {A B : Sort (u+2)} (h : A = B) (a : A) : HEq (Eq.mp h a) a := by
    cases h
    rfl
  exact hcast _ _

/-- 指定した反転比較の値は、同じ共通解像の右比較の逆と左比較の値の合成。 -/
@[cite HTT "1.1.5" (partial := special) "Kan値豊穣図式の指定した反転比較の値の分解則。"]
lemma kanEnrichedOppositeValueIso_factor : ∀ {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J) (X : C),
  let Z := edgewiseOrdinaryObject X
  let z := coherentNerveVertex Z
  let j := edgewiseEnrichedInfinityMap C
  let hf : (j ≫ D.realization).app _ z =
      functorVertex (kanDiagramCoherentNerve (D.evaluate X)) := by
    change D.realization.app _ ((coherentNerveMap (edgewiseEnrichedRight C)).app _ z) = _
    rw [coherentNerveMap_vertex]
    exact D.realization_vertex X
  let hR := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj Y.val).obj)
  let hL := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj Y.val).obj)
  (eqToIso (congrArg (fun v => HomotopyCategory.mk v) hf)).symm ≪≫
    functorIsoValue D.oppositeRealizationIso z ≪≫
    eqToIso (congrArg (fun v => HomotopyCategory.mk v) (D.opposite.realization_vertex Z)) =
  (kanEnrichedRealizationValueIso D.edgewiseRightComparison hR Z).symm ≪≫
    kanEnrichedRealizationValueIso D.edgewiseLeftComparison hL Z := by
  intro C instC instS J instJ D X
  dsimp only
  let Z := edgewiseOrdinaryObject X
  let z := coherentNerveVertex Z
  let j := edgewiseEnrichedInfinityMap C
  let hR := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj Y.val).obj)
  let hL := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj Y.val).obj)
  let R := kanEnrichedRealizationValueIso D.edgewiseRightComparison hR Z
  let L := kanEnrichedRealizationValueIso D.edgewiseLeftComparison hL Z
  let r := functorIsoValue D.edgewiseRightRealizationIso z
  let l := functorIsoValue D.edgewiseLeftRealizationIso z
  have hf : (j ≫ D.realization).app _ z =
      functorVertex (kanDiagramCoherentNerve (D.evaluate X)) := by
    change D.realization.app _ ((coherentNerveMap (edgewiseEnrichedRight C)).app _ z) = _
    rw [coherentNerveMap_vertex]
    exact D.realization_vertex X
  have hr : HEq r (functorIsoValue (D.edgewiseRightComparison.realizationIso hR) z) :=
    functorIsoValue_heq_of_heq _ _ rfl (D.realization_precompose (edgewiseEnrichedRight C)).symm
      (right_realization_heq D) z
  have hRraw : HEq R (functorIsoValue (D.edgewiseRightComparison.realizationIso hR) z) := by
    exact iso_endpoints_heq _ _ _
  have hLraw : HEq L l := by
    exact iso_endpoints_heq _ _ _
  have hRn : (eqToIso (congrArg (fun v => HomotopyCategory.mk v)
      (D.edgewise.realization_vertex Z))).symm ≪≫ r ≪≫
      eqToIso (congrArg (fun v => HomotopyCategory.mk v) hf) = R :=
    eq_of_heq ((iso_endpoints_heq r _ _).trans (hr.trans hRraw.symm))
  have hLn : (eqToIso (congrArg (fun v => HomotopyCategory.mk v)
      (D.edgewise.realization_vertex Z))).symm ≪≫ l ≪≫
      eqToIso (congrArg (fun v => HomotopyCategory.mk v)
        (D.opposite.realization_vertex Z)) = L :=
    eq_of_heq ((iso_endpoints_heq l _ _).trans hLraw.symm)
  have hop : functorIsoValue D.oppositeRealizationIso z = r.symm ≪≫ l := by
    rw [KanEnrichedDiagram.oppositeRealizationIso, functorIsoValue_trans, value_symm]
  change (eqToIso (congrArg (fun v => HomotopyCategory.mk v) hf)).symm ≪≫
    functorIsoValue D.oppositeRealizationIso z ≪≫
    eqToIso (congrArg (fun v => HomotopyCategory.mk v)
      (D.opposite.realization_vertex Z)) = R.symm ≪≫ L
  rw [hop, ← hRn, ← hLn]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
