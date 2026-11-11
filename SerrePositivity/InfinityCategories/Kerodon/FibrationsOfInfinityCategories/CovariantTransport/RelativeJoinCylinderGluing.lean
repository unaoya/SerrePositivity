module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinLeftPushout
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverMono
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutGluing
public import Mathlib.CategoryTheory.Limits.Shapes.Connected

/-!
概要：写像円柱から relative join への比較の単射に沿う pushout による貼り合わせ。
方針：両関手の単射保存と pushout 保存、比較の自然性を一般の貼り合わせ判定に使う。
規約：比較の同値条件は任意の quasicategory への前合成による。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、始域の境界からセルへの帰納。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：単射を含む pushout の三頂点で写像円柱比較が同値条件を満たせば第四も満たす。
方針：写像円柱と relative join の二つの pushout の間に自然な比較の立方体を作る。
規約：Over S の pushout と左成分の単射を仮定する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルを追加する際の比較の帰納段階。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_pushout
    {S : SSet.{u}} {A B C D : Over S} {i : A ⟶ B} {g : A ⟶ C}
    {r : B ⟶ D} {s : C ⟶ D} [Mono i.left] (hp : IsPushout i g r s)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison A.hom))
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison B.hom))
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison C.hom)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison D.hom) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderOverFunctor S
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor (𝟙 S)
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparisonNat S
  have : Mono (F.map i) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderOverMap_mono i
  have : Mono (G.map i) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_mono (𝟙 S) i.left i.w
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_pushout_gluing (hp.map F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_left_isPushout (𝟙 S) (hp.map (Over.forget S)))
    (t.app A) (t.app B) (t.app C) (t.app D)
    (t.naturality i) (t.naturality g) (t.naturality r) (t.naturality s) hA hB hC

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
