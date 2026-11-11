module
public import SerrePositivity.KST.NonConnective.DGKInputIndNativeComposition

/-!
概要：同じ元の Indω 作用と compact 生成元間の作用を、全 native 入力で比較する。
方針：生成逆射と compact 包含の全比較に、元の全 Yoneda 制限比較を合成する。
規約：全高次 Hom を保持する。D-8 の非可算 κ-cone の作用は別工程。
使われ方：K-7 d4 の I-2 e・固定 ν・Indω 間の全入力自然性。
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

/-- 同じ全 native Ind 作用は、元の compact 包含と全関手同型で可換。 -/
def dgKInputIndNativeFamilyMap_compactIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKInputIndNativeFamilyMap R A B ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0
          (dgKInputIndCompletion R A))).app _)
      (dgKInputCompactNativeFamilyMap R A B ≫
        (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0
          (dgKInputIndCompletion R B))) := by
  let p := (dgKInputCompactGenerationEquivalence R A).inv
  let YA := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj
  have ej : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0 (dgKInputIndCompletion R A))
      (p ≫ YA) := by
    simpa only [Category.id_comp, p, YA] using!
      (dgKInputCompactGeneration_familyIso R A (𝟙 _)).symm
  have e₀ := (ej.map_pre (dgKInputIndCompletion R B)).precomp
    (dgKInputIndNativeFamilyMap R A B)
  have e₁ := (dgKInputIndNativeFamilyMap_restrictionIso R A B).postcomp ((pre p).app _)
  have hL : dgKInputIndNativeFamilyMap R A B ≫ (pre (p ≫ YA)).app _ =
      (dgKInputIndNativeFamilyMap R A B ≫ (pre YA).app _) ≫ (pre p).app _ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    rfl
  have hR : dgKInputIndNativeGeneratorFamily R A B ≫ (pre p).app _ =
      dgKInputCompactNativeFamilyMap R A B ≫
        (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0
          (dgKInputIndCompletion R B)) := by
    rw [dgKInputCompactNativeFamilyMap_inclusion]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    rfl
  rw [hL] at e₀
  exact e₀ ≪≫ (by simpa only [hR] using! e₁)

/-- 任意の全高次入力族でも、同じ compact 包含の自然性比較を使用する。 -/
def dgKInputIndNativeFamilyMap_compactParameterIso
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) :=
  (dgKInputIndNativeFamilyMap_compactIso R A B).precomp a

/-- 比較自体は元の任意入力族の再制限と厳密に可換。 -/
theorem dgKInputIndNativeFamilyMap_compactParameterIso_precomp
    {S T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) (r : S ⟶ T) :
    (dgKInputIndNativeFamilyMap_compactParameterIso R A B a).precomp r =
      dgKInputIndNativeFamilyMap_compactParameterIso R A B (r ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ _ _

end SerrePositivity.KST.NonConnective
