module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeRightComposition
public import SerrePositivity.KST.SConstruction.ClosedRightActionComposition

/-! # 元の全 native Perf 関手族の豊穣合成保存
概要：出力宇宙へ移した Kan 入力の合成を、実 Perf 関手空間への射が厳密に保つ。
方針：元の全単体的右作用の合成等号を、閉構造の curry によって豊穣合成へ移す。
規約：元の全高次入力と因子順を保持。使われ方：厳密豊穣 Perf 関手から K への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E T : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} T]

/-- 元の全 native Perf 関手族への実射は、同じ Kan 入力合成を厳密豊穣合成へ送る。 -/
lemma presentedPerfectDGNativeFamilyMap_comp :
    (presentedPerfectDGNativeFamilyMap A D E ⊗ₘ presentedPerfectDGNativeFamilyMap A E T) ≫
        MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A T)) =
      presentedPerfectDGNativeParameterComp A D E T ≫ presentedPerfectDGNativeFamilyMap A D T := by
  exact rightActionCurry_comp
    (presentedPerfectDGNativeCoreAction A D E) (presentedPerfectDGNativeCoreAction A E T)
    (presentedPerfectDGNativeCoreAction A D T) (presentedPerfectDGNativeParameterComp A D E T)
    (presentedPerfectDGNativeCoreAction_comp A D E T)

end SerrePositivity.KST.SConstruction
