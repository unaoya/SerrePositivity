module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiZeroComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
/-!
概要：反転した空間の連結成分を元の成分へ自然に戻す。
方針：実辺の両端交換を π₀ の商へ渡す。
規約：元の頂点を保持し、Kan 性や代表の選択を要求しない。
使われ方：線形模型と native 評価の零次数コホモロジーチャート。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 元の頂点へ戻す π₀ の写像。 -/
def dgBarCompactPiZeroOppositeDown (X : SSet.{u}) : π₀ X.op → π₀ X :=
  π₀.lift (fun x => π₀.mk (SSet.opObjEquiv x)) (fun _ _ e =>
    (π₀.sound (Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop e))).symm)

/-- 同じ頂点を反転側へ送る π₀ の写像。 -/
def dgBarCompactPiZeroOppositeUp (X : SSet.{u}) : π₀ X → π₀ X.op :=
  π₀.lift (fun x => π₀.mk (SSet.opObjEquiv.symm x)) (fun _ _ e =>
    (π₀.sound (Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e))).symm)

/-- 反転は連結成分の型を変えない。 -/
def dgBarCompactOppositePiZeroEquiv (X : SSet.{u}) : π₀ X.op ≃ π₀ X where
  toFun := dgBarCompactPiZeroOppositeDown X
  invFun := dgBarCompactPiZeroOppositeUp X
  left_inv a := by obtain ⟨x, rfl⟩ := π₀.mk_surjective a; rfl
  right_inv a := by obtain ⟨x, rfl⟩ := π₀.mk_surjective a; rfl

lemma dgBarCompactOppositePiZeroEquiv_naturality {X Y : SSet.{u}}
    (f : X ⟶ Y) (a : π₀ X.op) :
    dgBarCompactOppositePiZeroEquiv Y (SSet.mapπ₀ (SSet.opFunctor.map f) a) =
      SSet.mapπ₀ f (dgBarCompactOppositePiZeroEquiv X a) := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective a
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
