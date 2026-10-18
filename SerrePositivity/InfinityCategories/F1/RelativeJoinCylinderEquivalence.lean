module

public import SerrePositivity.InfinityCategories.F1.RelativeJoinPullbackIso
public import SerrePositivity.InfinityCategories.F1.MappingCylinderPullbackIso
public import SerrePositivity.InfinityCategories.F1.RelativeJoinCylinderStandardTarget
public import SerrePositivity.InfinityCategories.F1.PrecompositionSimplexLocality

/-!
概要：任意の射の写像円柱から relative join への標準比較の同値条件。
方針：両模型の任意の底変換との交換と、各標準単体への pullback による局所判定を使う。
規約：始域・終域の有限性や quasicategory 性を要求しない。
使われ方：Kerodon Proposition 5.2.4.5、左 straightening の scaffold の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の円柱比較の pullback の同値条件は底変換した構造射の比較と同値。
方針：両模型から標準 pullback への同型と比較の可換性を二対三則に使う。
規約：底変換の射は任意。
使われ方：Kerodon Proposition 5.2.4.5、局所判定へ具体的な比較を渡す同定。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_pullback_iff
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPrecompositionEquivalence
      (overPullbackMap (relativeJoinCylinderComparisonOver f) (Over.mk h)) ↔
        IsPrecompositionEquivalence (relativeJoinCylinderComparison (pullback.snd f h)) := by
  have hM : IsPrecompositionEquivalence (mappingCylinderPullbackLift f h) :=
    isPrecompositionEquivalence_of_iso (asIso (mappingCylinderPullbackLift f h))
  have hR : IsPrecompositionEquivalence (relativeJoinPullbackLift f h) :=
    isPrecompositionEquivalence_of_iso (asIso (relativeJoinPullbackLift f h))
  constructor
  · intro hp
    have hc := hM.comp hp
    rw [← relativeJoinCylinderComparison_pullbackLift f h] at hc
    exact hR.cancel_right hc
  · intro hp
    have hc := hp.comp hR
    rw [relativeJoinCylinderComparison_pullbackLift f h] at hc
    exact hM.cancel_left hc

/-- 概要：任意の射の写像円柱から relative join への比較は前合成の同値条件を満たす。
方針：底の各標準単体へ引き戻し、既に証明した標準単体を終域とする場合へ還元する。
規約：任意の quasicategory を標的とする関手単体集合への前合成を試験する。
使われ方：Kerodon Proposition 5.2.4.5、写像円柱と relative join を使う scaffold の比較。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f) := by
  change IsPrecompositionEquivalence (relativeJoinCylinderComparisonOver f).left
  apply isPrecompositionEquivalence_of_pullback_stdSimplex (relativeJoinCylinderComparisonOver f)
  intro n h
  apply (isPrecompositionEquivalence_relativeJoinCylinderComparison_pullback_iff f h).mpr
  exact isPrecompositionEquivalence_relativeJoinCylinderComparison_standardTarget
    n (pullback.snd f h)

end SerrePositivity.InfinityCategories
