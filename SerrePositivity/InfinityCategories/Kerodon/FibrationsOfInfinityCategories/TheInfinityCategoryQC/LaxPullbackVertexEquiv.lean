module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackVertexOfData

/-!
概要：lax pullback の頂点と指定三つ組の全単射。
方針：二射影の回収と矢印の一次単体の往復を比較する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：lax pullback の頂点と指定三つ組の全単射。
方針：二射影の回収と矢印の一次単体の往復を比較する。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
lemma laxPullbackVertexOfData_data {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData p q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexData p q x) = x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_fst]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.intervalFunctorVertexEdgeEquiv C).symm_apply_apply _
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_snd]
    rfl
/-- 概要：lax pullback の頂点と指定三つ組の全単射。
方針：二射影の回収と矢印の一次単体の往復を比較する。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
lemma laxPullbackVertexData_ofData {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackVertexData p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexData p q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData p q x) = x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackVertexData.ext
  · change ((pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData p q x)).1 = x.left
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_snd]
  · change ((pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData p q x)).2 = x.right
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_snd]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge
      ((pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData p q x)) = x.arrow
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_fst]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.intervalFunctorVertexEdgeEquiv C).apply_symm_apply _
/-- 概要：lax pullback の頂点と指定三つ組の全単射。
方針：二射影の回収と矢印の一次単体の往復を比較する。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
def laxPullbackVertexEquiv {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌ ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackVertexData p q :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexData p q, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData p q,
    laxPullbackVertexOfData_data p q, laxPullbackVertexData_ofData p q⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
