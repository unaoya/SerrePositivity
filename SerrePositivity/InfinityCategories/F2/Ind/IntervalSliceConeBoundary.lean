module

public import SerrePositivity.InfinityCategories.F2.Ind.IntervalSliceConeLift
public import SerrePositivity.InfinityCategories.F2.Ind.JoinAssociatorRightPair

/-!
概要：区間の全錐の組み替えは同じ元の辺とパラメーターの制限を保つ。
方針：結合同型の右二因子の境界と自然性を、slice の curry に移す。
規約：全錐の射の厳密な等式。使われ方：元の円柱と始点余錐の境界合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 持ち上げた余錐の頂点側の全辺は、元の区間図式そのもの。 -/
lemma intervalSliceConeLift_tip {A X : SSet.{u}} (d : (Δ[1] : SSet.{u}) ⟶ X)
    (f : A ⟶ sliceOver d) :
    sliceOverUncurry (joinInr A (Δ[0] : SSet.{u}) ≫ intervalSliceConeLift d f) =
      (joinStdSimplexIso 0 0).hom ≫ d := by
  rw [sliceOverUncurry_precomp, intervalSliceConeLift_uncurry,
    intervalSliceConeReassociation, ← Category.assoc, joinAssociator_rightPair,
    ← Category.assoc (joinInr A _), joinInr_joinMap,
    Category.assoc, sliceOverUncurry_fixed]

/-- 組み替えの全形状比較は、元のパラメーター制限と厳密に可換。 -/
lemma intervalSliceConeReassociation_precomp {A₀ A X : SSet.{u}}
    (d : (Δ[1] : SSet.{u}) ⟶ X) (f : A ⟶ sliceOver d) (g : A₀ ⟶ A) :
    joinMap (joinMap g (𝟙 (Δ[0] : SSet.{u}))) (𝟙 Δ[0]) ≫
      intervalSliceConeReassociation d f = intervalSliceConeReassociation d (g ≫ f) := by
  have hj : joinMap g (𝟙 (join (Δ[0] : SSet.{u}) Δ[0])) ≫
      joinMap (𝟙 A) (joinStdSimplexIso 0 0).hom =
        joinMap (𝟙 A₀) (joinStdSimplexIso 0 0).hom ≫ joinMap g (𝟙 Δ[1]) := by
    rw [← joinMap_comp, ← joinMap_comp]
    simp only [Category.comp_id, Category.id_comp]
  have hs : joinMap (joinMap g (𝟙 (Δ[0] : SSet.{u}))) (𝟙 Δ[0]) ≫
      (stableJoinAssociator A Δ[0] Δ[0]).hom ≫ joinMap (𝟙 A) (joinStdSimplexIso 0 0).hom =
        (stableJoinAssociator A₀ Δ[0] Δ[0]).hom ≫
          joinMap (𝟙 A₀) (joinStdSimplexIso 0 0).hom ≫ joinMap g (𝟙 Δ[1]) := by
    rw [← Category.assoc, stableJoinAssociator_naturality, Category.assoc, joinMap_id, hj]
  simp only [intervalSliceConeReassociation, sliceOverUncurry_precomp]
  simpa only [Category.assoc] using congrArg (fun h => h ≫ sliceOverUncurry f) hs

/-- 終点 slice 内の全余錐も、元のパラメーター制限を厳密に保つ。 -/
lemma intervalSliceConeLift_precomp {A₀ A X : SSet.{u}}
    (d : (Δ[1] : SSet.{u}) ⟶ X) (f : A ⟶ sliceOver d) (g : A₀ ⟶ A) :
    joinMap g (𝟙 (Δ[0] : SSet.{u})) ≫ intervalSliceConeLift d f =
      intervalSliceConeLift d (g ≫ f) := by
  apply sliceOverUncurry_injective
  rw [sliceOverUncurry_precomp, intervalSliceConeLift_uncurry,
    intervalSliceConeLift_uncurry, intervalSliceConeReassociation_precomp]

end SerrePositivity.InfinityCategories.F2.Ind
