module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionPointedFunctor
public import SerrePositivity.KST.SConstruction.ExInfinitySuspensionTransformation
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformationPrecompose

/-! # 元の一次方向商上の全 dg 入力に自然な Ex∞ suspension 比較
概要：同じ前向き比較を、厳密 dg 入力の元の全 Hom 上へ制限する。
方針：一次方向の同じ点つき厳密豊穣関手で前合成する。
規約：高次入力を離散化せず、厳密逆や単射性を仮定しない。使われ方：BF 構造射の右脚。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 一次方向の同じ商の suspension 比較を全厳密 dg 入力に束ねた豊穣自然変換。 -/
def presentedPerfectDGOneDirectionSuspensionComparison (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).comp SSet
        (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit))
      ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).comp SSet
        (suspensionThenCoaugmentedFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPrecompose
    (presentedPerfectDGOneDirectionPointedEnrichedFunctor A r) _ _
    exInfinitySuspensionTransformation

/-- 元の dg 入力上の比較成分は、同じ一次方向商の元の Ex∞ suspension 比較。 -/
lemma presentedPerfectDGOneDirectionSuspensionComparison_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionSuspensionComparison A r).app C =
      exInfinitySuspensionTransformation.app
        ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C) := rfl

end SerrePositivity.KST.SConstruction
