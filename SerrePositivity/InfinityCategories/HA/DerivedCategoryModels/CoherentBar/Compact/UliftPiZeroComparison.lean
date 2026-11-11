module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPointedFilling
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
/-!
概要：連結成分の宇宙比較を、指定した元と辺の上下操作で与える。
方針：実辺の同じ一次単体を上下し、π₀ の商の普遍性を使う。
規約：追加の宇宙は任意で、元の実射との自然性を保つ。
使われ方：native 評価の π₀ チャートを追加宇宙から戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X Y : SSet.{u}}

def dgBarCompactPiZeroUliftUp (X : SSet.{u}) :
    π₀ X → π₀ ((SSet.uliftFunctor.{v, u}).obj X) :=
  π₀.lift (fun x => π₀.mk (ULift.up x)) (fun _ _ e =>
    π₀.sound (SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{v, u}).obj X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} e)))

def dgBarCompactPiZeroUliftDown (X : SSet.{u}) :
    π₀ ((SSet.uliftFunctor.{v, u}).obj X) → π₀ X :=
  π₀.lift (fun x => π₀.mk x.down) (fun _ _ e =>
    π₀.sound (SSet.Edge.mk e.edge.down
      (congrArg ULift.down e.src_eq) (congrArg ULift.down e.tgt_eq)))

def dgBarCompactUliftPiZeroEquiv (X : SSet.{u}) :
    π₀ X ≃ π₀ ((SSet.uliftFunctor.{v, u}).obj X) where
  toFun := dgBarCompactPiZeroUliftUp X
  invFun := dgBarCompactPiZeroUliftDown X
  left_inv a := by obtain ⟨x, rfl⟩ := π₀.mk_surjective a; rfl
  right_inv a := by obtain ⟨x, rfl⟩ := π₀.mk_surjective a; rfl

lemma dgBarCompactUliftPiZeroEquiv_naturality (φ : X ⟶ Y) (a : π₀ X) :
    dgBarCompactUliftPiZeroEquiv.{u, v} Y (SSet.mapπ₀ φ a) =
      SSet.mapπ₀ ((SSet.uliftFunctor.{v, u}).map φ) (dgBarCompactUliftPiZeroEquiv.{u, v} X a) := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective a
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
