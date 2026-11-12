module
public import SerrePositivity.KST.NonConnective.DGKInputCompactNativeFamilyComposition

/-!
概要：元の全 native 入力作用と compact 生成元間の全作用を、同じ生成順射で比較する。
方針：始域の生成同値の単位を全関手空間へ送り、元の全パラメータへ制限する。
規約：元の全高次入力・生成同値を保持する。実 cone と構造辺 β の比較は別工程。
使われ方：K-7 d4 の固定 ν と compact 生成元間の作用の全入力自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- 概要：同じ生成順射は、元の全 native 入力作用と compact 生成元間の全作用を比較する。
方針：元の始域生成同値の単位を全前合成関手へ写し、同じ全族と標的順射で合成する。
規約：全 native Hom を一度に比較し、各 dg 射で同型を独立に選ばない。
使われ方：K-7 d4 の元の固定 ν 作用と生成元作用の照合。 -/
def dgKInputCompactNativeFamilyMap_generationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKInputCompactNativeFamilyMap R A B ≫
        (pre (dgKInputCompactGenerationEquivalence R A).hom).app _)
      (dgKInputCompactNativeLiftedFamilyMap R A B ≫
        (ihom _).map (dgKInputCompactGenerationEquivalence R B).hom) := by
  let X := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
    (dgKInputStableValue R A).obj
  let Y := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
    (dgKInputStableValue R B).obj
  have e := ((dgKInputCompactGenerationEquivalence R A).homInvIso.map_pre Y).precomp
    (dgKInputCompactNativeLiftedFamilyMap R A B)
  have e' := e.postcomp ((ihom X).map (dgKInputCompactGenerationEquivalence R B).hom)
  have hL : dgKInputCompactNativeFamilyMap R A B ≫
      (pre (dgKInputCompactGenerationEquivalence R A).hom).app _ =
      (dgKInputCompactNativeLiftedFamilyMap R A B ≫
        (pre ((dgKInputCompactGenerationEquivalence R A).hom ≫
          (dgKInputCompactGenerationEquivalence R A).inv)).app Y) ≫
        (ihom X).map (dgKInputCompactGenerationEquivalence R B).hom := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro p
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [hL]
  simpa only [pre_id, NatTrans.id_app, Category.comp_id] using! e'

/-- 概要：同じ全 native 作用比較を、元の Yoneda を通る全入力比較へ送る。
方針：同じ生成順射比較に compact 包含を後合成し、元の包含式を厳密に回収する。
規約：比較自体も同じ単位から作り、点別の Yoneda 比較を選び直さない。
使われ方：K-7 d4 の全 native Hom と元の全 Yoneda の照合。 -/
def dgKInputCompactNativeFamilyMap_yonedaIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKInputCompactNativeFamilyMap R A B ≫
        (pre (dgKInputCompactGenerationEquivalence R A).hom).app _ ≫
        (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{max (u + 1) v, max (u + 1) v + 1}
          Cardinal.aleph0 (dgKInputIndCompletion R B)))
      (dgKInputCompactNativeLiftedFamilyMap R A B ≫
        (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda.{max (u + 1) v}
          Cardinal.aleph0 (dgKInputStableValue R B).obj)) := by
  have e := (dgKInputCompactNativeFamilyMap_generationIso R A B).postcomp
    ((ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{max (u + 1) v, max (u + 1) v + 1}
      Cardinal.aleph0 (dgKInputIndCompletion R B)))
  simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    dgKInputCompactGenerationEquivalence_inclusion] using! e

/-- 概要：任意の native 入力族でも、同じ生成順射による全作用比較を保持する。
方針：構成済みの全族比較を元のパラメータ射で前合成する。
規約：同じ比較を制限し、各点で選び直さない。
使われ方：K-7 d4 の単体族・全高次入力への適用。 -/
def dgKInputCompactNativeFamilyMap_generationParameterIso
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgKInputCompactNativeFamilyMap_generationIso R A B) a

/-- 概要：同じ任意族の作用比較は、再制限しても元の再制限族の比較そのもの。
方針：正本の関手同型の前合成合成則を使う。
規約：同型の存在だけでなく、同じ比較自体の等式を保持する。
使われ方：K-7 d4 の全入力族での生成比較の自然性。 -/
theorem dgKInputCompactNativeFamilyMap_generationParameterIso_precomp
    {S T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) (r : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgKInputCompactNativeFamilyMap_generationParameterIso R A B a) r =
      dgKInputCompactNativeFamilyMap_generationParameterIso R A B (r ≫ a) := by
  unfold dgKInputCompactNativeFamilyMap_generationParameterIso
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ _ _

/-- 概要：同じ compact Yoneda を順射とする任意の生成逆射でも、元の全 native 作用と比較できる。
方針：Ind 正本の逆射選択比較を全前合成関手へ写し、同じ元の全族を前合成する。
規約：順射は元の compact Yoneda に厳密固定し、逆射の存在を追加入力にしない。
使われ方：K-7 d4 の生成逆射選択比較を、全 native 入力作用へ拡張する。 -/
def dgKInputCompactNativeFamilyMap_choiceIso
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgKInputStableValue R A).obj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects Cardinal.aleph0 (dgKInputIndCompletion R A)))
    (he : e.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.compactIndYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKInputCompactNativeLiftedFamilyMap R A B ≫ (pre e.inv).app _ ≫
        (ihom _).map (dgKInputCompactGenerationEquivalence R B).hom)
      (dgKInputCompactNativeFamilyMap R A B) := by
  letI : Fact (Cardinal.aleph0.{max (u + 1) v}).IsRegular :=
    Cardinal.fact_isRegular_aleph0
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationInverse_choiceIso Cardinal.aleph0
    (dgKInputStableValue_isIdempotentComplete R A) e he
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (hc.map_pre _) (dgKInputCompactNativeLiftedFamilyMap R A B)).postcomp
    ((ihom _).map (dgKInputCompactGenerationEquivalence R B).hom)

end SerrePositivity.KST.NonConnective
