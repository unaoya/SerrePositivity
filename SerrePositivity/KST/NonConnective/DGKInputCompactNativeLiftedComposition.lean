module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps
public import SerrePositivity.KST.NonConnective.DGKInputCompactNativeComposition
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeFamilyCoherence

/-!
概要：元の全 native dg 入力の合成を、同じ固定 ν の宇宙移送全族で厳密に回収する。
方針：元の全単体的合成等式を各実内部 Hom の全評価で宇宙移送する。
規約：元の全高次入力と合成順を保持し、通常の dg 点へ離散化しない。
使われ方：K-7 d4 の compact 生成元間の全 native 合成比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A B C : PerfDGInput.{u, v} R)

/-- 概要：元の全 native 入力合成を、同じ大きい宇宙の積入力へ移す。
方針：元の積の宇宙交換同型の逆と元の合成の宇宙持ち上げを合成する。
規約：同じ元の入力合成を保持する。
使われ方：元の固定 ν の全族と compact 生成元間の全族の合成比較。 -/
def dgKInputCompactNativeParameterComp :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{max (u + 1) v, max (u + 1) v + 1}
    (presentedPerfectDGNativeParameter R A B) (presentedPerfectDGNativeParameter R B C)).inv ≫
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (presentedPerfectDGNativeParameterComp R A B C)

/-- 概要：同じ宇宙移送全族は、元の全 native 入力合成を実関手空間で厳密に保つ。
方針：K-S• 正本の元の全族合成等式を、元の各単体・各評価で宇宙移送する。
規約：同じ全高次入力を保持。compact 生成同値の中間往復は別途比較する。
使われ方：K-7 d4 の全 native 合成比較の元になる厳密等式。 -/
theorem dgKInputCompactNativeLiftedFamilyMap_comp :
    (dgKInputCompactNativeLiftedFamilyMap R A B ⊗ₘ dgKInputCompactNativeLiftedFamilyMap R B C) ≫
      MonoidalClosed.comp _ _ _ =
    dgKInputCompactNativeParameterComp R A B C ≫ dgKInputCompactNativeLiftedFamilyMap R A C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  have h := congrArg (fun f => (f.app n (p.1.down, p.2.down)).app d α a.down)
    (presentedPerfectDGNativeFamilyMap_comp R A B C)
  exact congrArg ULift.up h

end SerrePositivity.KST.NonConnective
