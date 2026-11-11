module
public import SerrePositivity.KST.NonConnective.DGKInputCompactNativeComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndRestrictionEquivalence

/-!
概要：固定 ν の全 native Hom 作用を、同じ Indω 間の filtered 余極限保存関手へ延長する。
方針：元の全 Yoneda 制限の実同値の逆を、同じ宇宙移送全族に適用する。
規約：全入力族を一度に延長する。D-8 の κ-cone や懸垂構造辺への自然性は別工程。
使われ方：K-7 d4 の I-2 e と固定 ν の全入力作用の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

local instance indNativeRegular : Fact (Cardinal.aleph0.{w}).IsRegular :=
  Cardinal.fact_isRegular_aleph0
variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- 同じ元の Yoneda 制限を順射とする実 ∞ 圏同値。標的 Ind の余極限は正本が供給する。 -/
def dgKInputIndRestrictionEquivalence :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence Cardinal.aleph0 (dgKInputStableValue R A).obj
    (dgKInputIndCompletion R B)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits Cardinal.aleph0 (dgKInputStableValue R B).obj)

/-- 元の全 native ν 作用を、同じ標的の全 Yoneda に続けた全族。 -/
def dgKInputIndNativeGeneratorFamily :=
  dgKInputCompactNativeLiftedFamilyMap R A B ≫
    (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj)

/-- 元の全 native 入力族を、filtered 余極限保存関手の全部分 ∞ 圏へ延長する。 -/
def dgKInputIndNativeContinuousFamilyMap :=
  dgKInputIndNativeGeneratorFamily R A B ≫ (dgKInputIndRestrictionEquivalence R A B).inv

/-- 同じ延長の全関手空間への実包含。対象別の延長の独立選択は行わない。 -/
def dgKInputIndNativeFamilyMap :=
  dgKInputIndNativeContinuousFamilyMap R A B ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.kappaContinuousFunctorInclusion Cardinal.aleph0
      (dgKInputIndCompletion R A) (dgKInputIndCompletion R B)

/-- 概要：延長した全族の Yoneda 制限は、元の全 native ν・Yoneda 族と同型。
方針：同じ制限同値の余単位を元の全族へ前合成する。
規約：全 Hom 族上の関手同型であり、点ごとの比較に弱めない。
使われ方：d4 の Ind 作用と元の固定 ν 作用の照合。 -/
def dgKInputIndNativeFamilyMap_restrictionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputIndNativeFamilyMap R A B ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj)).app _)
      (dgKInputIndNativeGeneratorFamily R A B) := by
  have e := (dgKInputIndRestrictionEquivalence R A B).invHomIso.precomp
    (dgKInputIndNativeGeneratorFamily R A B)
  simpa only [dgKInputIndNativeFamilyMap, dgKInputIndNativeContinuousFamilyMap,
    dgKInputIndRestrictionEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction, Category.assoc, Category.comp_id] using! e

/-- 任意の同じ native 入力族への制限でも、元の全 Yoneda 比較を保持する。 -/
def dgKInputIndNativeFamilyMap_restrictionParameterIso
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) :=
  (dgKInputIndNativeFamilyMap_restrictionIso R A B).precomp a

/-- 比較自体も任意の全高次パラメータの再制限と可換する。 -/
theorem dgKInputIndNativeFamilyMap_restrictionParameterIso_precomp
    {S T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) (r : S ⟶ T) :
    (dgKInputIndNativeFamilyMap_restrictionParameterIso R A B a).precomp r =
      dgKInputIndNativeFamilyMap_restrictionParameterIso R A B (r ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ _ _

/-- 元の厳密 dg 射の同じ native 頂点における、実 Ind 関手。 -/
def dgKInputIndNativeMap (f : A ⟶ B) : dgKInputIndCompletion R A ⟶ dgKInputIndCompletion R B :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ((dgKInputIndNativeFamilyMap R A B).app (Opposite.op ⦋0⦌)
    (ULift.up (perfDGInputVertexEquiv R A B f)))

/-- 同じ実 dg 射の Ind 延長は、小さい filtered native 余極限を保存する。 -/
theorem dgKInputIndNativeMap_preservesFilteredColimits (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 (dgKInputIndNativeMap R A B f) := by
  let x := (dgKInputIndNativeContinuousFamilyMap R A B).app (Opposite.op ⦋0⦌)
    (ULift.up (perfDGInputVertexEquiv R A B f))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x

end SerrePositivity.KST.NonConnective
