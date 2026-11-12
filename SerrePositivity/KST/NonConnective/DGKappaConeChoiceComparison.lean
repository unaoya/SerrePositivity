module
public import SerrePositivity.KST.NonConnective.DGKappaConeCompactComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FunctorIsoInverseHEq

/-!
概要：固定 κ の実 dg cone の選択を、同じ実導来 κ-compact 部分を介して比較する。
方針：指定された包含順射と実逆二胞体を合成し、元の導来包含との比較を保持する。
規約：P と perfect 代表所属を使わない。厳密 dg 比較射や全入力懸垂作用は主張しない。
使われ方：K-7 d4 の非可算 κ 側の選択比較と高次パラメータへの制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I J K : DGKappaConeInput R D κ)

/-- 同じ導来 κ-compact 部分を介した、実 cone 間の全関手同値。 -/
def dgKappaConeChoiceEquivalence :=
  (dgKappaConeCompactEquivalence R D I).trans (dgKappaConeCompactEquivalence R D J).symm

/-- 同じ実 cone の自己比較は恒等関手と同型。 -/
def dgKappaConeChoiceEquivalence_selfIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaConeChoiceEquivalence R D I I).hom (𝟙 _) :=
  (dgKappaConeCompactEquivalence R D I).homInvIso

/-- 選択比較の後の実導来包含は、元の実導来包含と全関手で同型。 -/
def dgKappaConeChoiceEquivalence_inclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaConeChoiceEquivalence R D I J).hom ≫
      dgKappaConeDerivedComparison R D J) (dgKappaConeDerivedComparison R D I) := by
  have e := ((dgKappaConeCompactEquivalence R D J).invHomIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D))).precomp
        (dgKappaConeCompactEquivalence R D I).hom
  simpa only [dgKappaConeChoiceEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm,
    Category.assoc, Category.id_comp, dgKappaConeCompactEquivalence_inclusion] using! e

/-- 三選択の比較は、同じ中間実 cone の逆二胞体で合成する。 -/
def dgKappaConeChoiceEquivalence_compIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaConeChoiceEquivalence R D I J).hom ≫
      (dgKappaConeChoiceEquivalence R D J K).hom)
      (dgKappaConeChoiceEquivalence R D I K).hom := by
  have e := ((dgKappaConeCompactEquivalence R D J).invHomIso.postcomp
    (dgKappaConeCompactEquivalence R D K).inv).precomp
      (dgKappaConeCompactEquivalence R D I).hom
  simpa only [dgKappaConeChoiceEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm,
    Category.assoc, Category.id_comp] using! e

/-- 任意の実 cone 入力族でも、元の同じ実導来包含比較を使う。 -/
def dgKappaConeChoiceParameterIso {T : SSet.{max (u + 1) v}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I)) :=
  (dgKappaConeChoiceEquivalence_inclusionIso R D I J).precomp a

/-- 比較自体の全高次パラメータへの再制限も厳密に元の合成と一致する。 -/
theorem dgKappaConeChoiceParameterIso_precomp {S T : SSet.{max (u + 1) v}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I)) (r : S ⟶ T) :
    (dgKappaConeChoiceParameterIso R D I J a).precomp r =
      dgKappaConeChoiceParameterIso R D I J (r ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ _ _

end SerrePositivity.KST.NonConnective
