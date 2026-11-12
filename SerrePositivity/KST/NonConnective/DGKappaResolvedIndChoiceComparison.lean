module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedIndComparison

/-!
概要：固定 κ の実小核の選択を変えたとき、元の Indω 評価と P 比較を保つ同値を構成する。
方針：同じ元の入力の Indω を介し、指定した順逆射と逆二胞体だけを合成する。
規約：元の実小核・I・P は変更しない。比較は指定同型であり厳密等号に弱めない。
使われ方：K-7 d4 の実小核比較の選択整合と三選択の合成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}}
  (I J K : DGKappaConeInput R A κ)
  (P : DGKappaPerfectInput R A I) (Q : DGKappaPerfectInput R A J)
  (H : DGKappaPerfectInput R A K)

/-- 同じ固定 κ の二つの実小核の Indω を、元の実評価同値で比較する。 -/
def dgKappaResolvedIndChoiceEquivalence :=
  (dgKappaResolvedIndEquivalence R A I P).symm.trans
    (dgKappaResolvedIndEquivalence R A J Q)

/-- 同じ選択を比較すると、指定比較は実核の Indω の恒等と同型。 -/
def dgKappaResolvedIndChoiceEquivalence_selfIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaResolvedIndChoiceEquivalence R A I I P P).hom (𝟙 _) :=
  (dgKappaResolvedIndEquivalence R A I P).invHomIso

/-- 元の入力からの実評価 Morita 延長は、選択比較の下で全関手として可換する。 -/
def dgKappaResolvedIndChoiceEquivalence_sourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaResolvedIndMoritaMap R A I P ≫
      (dgKappaResolvedIndChoiceEquivalence R A I J P Q).hom)
      (dgKappaResolvedIndMoritaMap R A J Q) := by
  have e := (dgKappaResolvedIndEquivalence R A I P).homInvIso.postcomp
    (dgKappaResolvedIndEquivalence R A J Q).hom
  simpa only [dgKappaResolvedIndChoiceEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm, dgKappaResolvedIndEquivalence_hom,
    Category.assoc, Category.id_comp] using! e

/-- P の元の指定全合成を延長した作用も、同じ選択比較で可換する。 -/
def dgKappaResolvedIndChoiceEquivalence_PIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaResolvedIndPMap R A I P ≫
      (dgKappaResolvedIndChoiceEquivalence R A I J P Q).hom)
      (dgKappaResolvedIndPMap R A J Q) :=
  (dgKappaResolvedIndPComparisonIso R A I P).postcomp _ ≪≫
    dgKappaResolvedIndChoiceEquivalence_sourceIso R A I J P Q ≪≫
      (dgKappaResolvedIndPComparisonIso R A J Q).symm

/-- 三つの実小核間の選択比較は、元の評価同値の同じ逆二胞体で合成する。 -/
def dgKappaResolvedIndChoiceEquivalence_compIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgKappaResolvedIndChoiceEquivalence R A I J P Q).hom ≫
        (dgKappaResolvedIndChoiceEquivalence R A J K Q H).hom)
      (dgKappaResolvedIndChoiceEquivalence R A I K P H).hom := by
  have e := ((dgKappaResolvedIndEquivalence R A J Q).homInvIso.postcomp
    (dgKappaResolvedIndEquivalence R A K H).hom).precomp
      (dgKappaResolvedIndEquivalence R A I P).inv
  simpa only [dgKappaResolvedIndChoiceEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm, Category.assoc, Category.id_comp] using! e

end SerrePositivity.KST.NonConnective
