module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinBaseCocartesianFibration
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinCoconeFiber
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomCartesianFibration

/-!
概要：相対 join の左包含は任意の底変換の後も cocartesian 辺を保存する。
方針：底変換と相対 join の同型で左包含を同定し、二つの表示を移る。
規約：底変換の単体集合と射は任意。
使われ方：相対指数の制限が可逆化する図式の条件を保つことの確認。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：底変換した左包含と相対 join の同型の合成は Over の pullback の左包含。
方針：両 pullback 射影で底変換の比較と左包含の自然性を照合する。
規約：pullback の順序交換を始域に含める。
使われ方：底変換後の cocartesian 辺の保存の厳密な移送。 -/
lemma kanRelativeJoinInl_overPullbackMap {K C A : SSet.{u}} (p : K ⟶ C) (b : A ⟶ C) :
    (pullbackSymmetry b p).hom ≫ relativeJoinInl (pullback.snd p b) (𝟙 A) ≫
        relativeJoinPullbackLift p b =
      overPullbackMap (kanRelativeJoinInlOver p) (Over.mk b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, relativeJoinPullbackLift_fst,
      kanRelativeJoinInl_baseProjection, pullbackSymmetry_hom_comp_snd]
    exact (overPullbackMap_fst (kanRelativeJoinInlOver p) (Over.mk b)).symm
  · rw [Category.assoc, Category.assoc, relativeJoinPullbackLift_snd,
      kanRelativeJoinInl_pullbackMap, ← Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact (overPullbackMap_snd (kanRelativeJoinInlOver p) (Over.mk b)).symm

/-- 概要：任意の底変換後の相対 join の左包含は cocartesian 辺を保存する。
方針：元の逆像を順序交換し、相対 join の左端の保存と底変換同型を順に適用する。
規約：元の射自体に fibration 性は要求しない。
使われ方：可逆化する図式を制限しても相対指数の特殊辺になることの確認。 -/
lemma kanRelativeJoinInl_overPullback_preservesCocartesian {K C A : SSet.{u}}
    (p : K ⟶ C) (b : A ⟶ C) (s : (pullback b p) _⦋1⦌)
    (hs : IsCocartesianEdge (pullback.fst b p) s) :
    IsCocartesianEdge (pullback.fst b (relativeJoinBaseProjection p (𝟙 C)))
      ((overPullbackMap (kanRelativeJoinInlOver p) (Over.mk b)).app (Opposite.op ⦋1⦌) s) := by
  have hq : IsCocartesianEdge ((pullbackSymmetry b p).hom ≫ pullback.snd p b) s := by
    rw [pullbackSymmetry_hom_comp_snd]
    exact hs
  have he := kanIsCocartesianEdge_map_iso (pullbackSymmetry b p) (pullback.snd p b) s hq
  have hl := kanRelativeJoinInl_base_isCocartesianEdge (pullback.snd p b) _ he
  have hc : IsCocartesianEdge
      (relativeJoinPullbackLift p b ≫ pullback.fst b (relativeJoinBaseProjection p (𝟙 C)))
      ((relativeJoinInl (pullback.snd p b) (𝟙 A)).app (Opposite.op ⦋1⦌)
        ((pullbackSymmetry b p).hom.app (Opposite.op ⦋1⦌) s)) := by
    rw [relativeJoinPullbackLift_fst]
    exact hl
  have h := kanIsCocartesianEdge_map_iso (asIso (relativeJoinPullbackLift p b)) _ _ hc
  change IsCocartesianEdge _
    (((pullbackSymmetry b p).hom ≫ relativeJoinInl (pullback.snd p b) (𝟙 A) ≫
      relativeJoinPullbackLift p b).app (Opposite.op ⦋1⦌) s) at h
  rw [kanRelativeJoinInl_overPullbackMap] at h
  exact h

end SerrePositivity.InfinityCategories.F1B
