module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.PrecompositionNerveLocality
public import SerrePositivity.InfinityCategories.F1B.CocartesianScaffold.PullbackComparison

/-!
概要：通常の圏の nerve 上の cocartesian scaffold の全空間比較。
方針：底の全ての有限鎖上へ引き戻し、有限鎖での帰納と前合成同値の局所性を使う。
規約：一般の scaffold の始域に quasicategory 性を要求せず、前合成同値として結論を表す。
使われ方：Kerodon Theorem 5.3.5.7、cocartesian fibration の strict transport による復元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：通常の圏の nerve 上の cocartesian scaffold の比較射は前合成同値。
方針：各有限鎖への引き戻しでの同値を示し、底についての局所性で全体へ戻す。
規約：係数値は quasicategory、射影は cocartesian fibration。
使われ方：Kerodon Theorem 5.3.5.7、taut scaffold と universal scaffold の全空間比較。 -/
lemma CocartesianScaffold.isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    {p : E ⟶ nerve C} [CocartesianFibration p]
    {F : C ⥤ SSet.{u}} [∀ c, Quasicategory (F.obj c)]
    {l : simplicialReplacement F ⟶ E} (hs : SerrePositivity.InfinityCategories.CocartesianScaffold p F l) :
    IsPrecompositionEquivalence l := by
  let h := hs.projection
  exact isPrecompositionEquivalence_of_pullback_finiteNerve
    (Over.homMk (U := Over.mk (simplicialReplacementProjection F)) (V := Over.mk p) l h)
    (fun n H ↦ SerrePositivity.InfinityCategories.CocartesianScaffold.overPullback_finiteComparison p F l hs h n H)

/-- 概要：cocartesian fibration の universal scaffold は前合成同値。
方針：strict transport の各係数値での評価の同値を一般の scaffold 比較に適用する。
規約：底は通常の圏の nerve。
使われ方：Kerodon Theorems 5.3.5.7、5.3.5.6、strict transport から元の全空間の復元。 -/
lemma cocartesianUniversalScaffold_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] :
    IsPrecompositionEquivalence (SerrePositivity.InfinityCategories.cocartesianUniversalScaffold p) :=
  (SerrePositivity.InfinityCategories.cocartesianUniversalScaffold_isCocartesianScaffold p).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories
