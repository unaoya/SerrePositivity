module
public import SerrePositivity.KST.NonConnective.DGKInputCompactNativeComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：Ind I-2 e の同じ生成順射に対する逆射選択を全 native 入力で整合的に比較する。
方針：元の全関手族から公開逆射への比較を固定し、その比で任意二選択を比較する。
規約：全 native Hom と元の ν・compact Yoneda を保持する。非可算 cone 比較は別工程。
使われ方：K-7 d4 の選択比較の恒等・合成・任意族への再制限自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- 同じ compact Yoneda を順射とする生成同値の選択。存在は公開 I-2 e が供給する。 -/
abbrev DGKInputCompactGenerationChoice :=
  {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
    (dgKInputStableValue R A).obj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects Cardinal.aleph0 (dgKInputIndCompletion R A)) //
      e.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.compactIndYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj}

/-- 無条件 Ind 正本の同じ生成同値は、元の compact Yoneda を順射に持つ。 -/
def dgKInputStableCompactGenerationChoice : DGKInputCompactGenerationChoice R A :=
  ⟨(dgKInputStableCompactGeneration R A).equivalence, by
    rw [dgKInputStableCompactGeneration_equivalence, dgKInputCompactGenerationEquivalence_hom]⟩

/-- 任意の同じ生成逆射で表した、元の全 native 入力作用。 -/
def dgKInputCompactNativeChoiceFamilyMap (e : DGKInputCompactGenerationChoice R A) :=
  dgKInputCompactNativeLiftedFamilyMap R A B ≫ (pre e.val.inv).app _ ≫
    (ihom _).map (dgKInputCompactGenerationEquivalence R B).hom

/-- 同じ全族を公開生成逆射の全族へ比較する固定同型。 -/
def dgKInputCompactNativeChoiceToFixed (e : DGKInputCompactGenerationChoice R A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputCompactNativeChoiceFamilyMap R A B e)
      (dgKInputCompactNativeFamilyMap R A B) :=
  dgKInputCompactNativeFamilyMap_choiceIso R A B e.val e.property

/-- 元の全入力族上で、任意二つの生成逆射を比較する。 -/
def dgKInputCompactNativeChoiceIso (e e' : DGKInputCompactGenerationChoice R A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputCompactNativeChoiceFamilyMap R A B e)
      (dgKInputCompactNativeChoiceFamilyMap R A B e') :=
  dgKInputCompactNativeChoiceToFixed R A B e ≪≫ (dgKInputCompactNativeChoiceToFixed R A B e').symm

/-- 同じ選択を比較する全 native 同型は恒等。 -/
theorem dgKInputCompactNativeChoiceIso_refl (e : DGKInputCompactGenerationChoice R A) :
    dgKInputCompactNativeChoiceIso R A B e e = Iso.refl _ := by
  simp only [dgKInputCompactNativeChoiceIso, Iso.self_symm_id]

/-- 三つの逆射選択の比較は元の全 native Hom 族上で合成則を満たす。 -/
theorem dgKInputCompactNativeChoiceIso_trans (e e' e'' : DGKInputCompactGenerationChoice R A) :
    dgKInputCompactNativeChoiceIso R A B e e' ≪≫ dgKInputCompactNativeChoiceIso R A B e' e'' =
      dgKInputCompactNativeChoiceIso R A B e e'' := by
  simp only [dgKInputCompactNativeChoiceIso, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- 任意の同じ native 入力族にも、二選択の全作用比較を制限する。 -/
def dgKInputCompactNativeChoiceParameterIso (e e' : DGKInputCompactGenerationChoice R A)
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) :=
  (dgKInputCompactNativeChoiceIso R A B e e').precomp a

/-- 同じ比較自体は全高次パラメータの再制限と可換。 -/
theorem dgKInputCompactNativeChoiceParameterIso_precomp
    (e e' : DGKInputCompactGenerationChoice R A) {S T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) (r : S ⟶ T) :
    (dgKInputCompactNativeChoiceParameterIso R A B e e' a).precomp r =
      dgKInputCompactNativeChoiceParameterIso R A B e e' (r ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ _ _

/-- 任意族に制限した三選択比較も、同じ合成則を厳密に保持する。 -/
theorem dgKInputCompactNativeChoiceParameterIso_trans
    (e e' e'' : DGKInputCompactGenerationChoice R A) {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) :
    dgKInputCompactNativeChoiceParameterIso R A B e e' a ≪≫
        dgKInputCompactNativeChoiceParameterIso R A B e' e'' a =
      dgKInputCompactNativeChoiceParameterIso R A B e e'' a := by
  unfold dgKInputCompactNativeChoiceParameterIso
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, dgKInputCompactNativeChoiceIso_trans]

/-- 任意の生成逆射の全作用も、同じ元の ν 全族へ生成順射で比較できる。 -/
def dgKInputCompactNativeChoice_generationIso (e : DGKInputCompactGenerationChoice R A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKInputCompactNativeChoiceFamilyMap R A B e ≫
        (pre (dgKInputCompactGenerationEquivalence R A).hom).app _)
      (dgKInputCompactNativeLiftedFamilyMap R A B ≫
        (ihom _).map (dgKInputCompactGenerationEquivalence R B).hom) :=
  (dgKInputCompactNativeChoiceToFixed R A B e).postcomp
    ((pre (dgKInputCompactGenerationEquivalence R A).hom).app _) ≪≫
      dgKInputCompactNativeFamilyMap_generationIso R A B

/-- 選択比較を経ても、元の全 ν 作用への指定比較そのものを回収する。 -/
theorem dgKInputCompactNativeChoice_generationIso_naturality
    (e e' : DGKInputCompactGenerationChoice R A) :
    (dgKInputCompactNativeChoiceIso R A B e e').postcomp
        ((pre (dgKInputCompactGenerationEquivalence R A).hom).app _) ≪≫
        dgKInputCompactNativeChoice_generationIso R A B e' =
      dgKInputCompactNativeChoice_generationIso R A B e := by
  simp only [dgKInputCompactNativeChoiceIso, dgKInputCompactNativeChoice_generationIso,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- 同じ任意逆射の全 native 作用を、元の全 Yoneda への包含後にも比較する。 -/
def dgKInputCompactNativeChoice_yonedaIso (e : DGKInputCompactGenerationChoice R A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKInputCompactNativeChoiceFamilyMap R A B e ≫
        (pre (dgKInputCompactGenerationEquivalence R A).hom).app _ ≫
        (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{max (u + 1) v, max (u + 1) v + 1}
          Cardinal.aleph0 (dgKInputIndCompletion R B)))
      (dgKInputCompactNativeLiftedFamilyMap R A B ≫
        (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda.{max (u + 1) v}
          Cardinal.aleph0 (dgKInputStableValue R B).obj)) := by
  have e' := (dgKInputCompactNativeChoice_generationIso R A B e).postcomp
    ((ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{max (u + 1) v, max (u + 1) v + 1}
      Cardinal.aleph0 (dgKInputIndCompletion R B)))
  simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    dgKInputCompactGenerationEquivalence_inclusion] using! e'

end SerrePositivity.KST.NonConnective
