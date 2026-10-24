module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceComparison

/-!
概要：再構成した終点面の全余錐と底余錐を、元の旧族の同じ全余錐へ厳密に戻す。
方針：元の円柱全体を固定する等号を、同じ終点で制限する。
規約：元の旧族と下方余錐の入力を保持する。
使われ方：終点比較の旧族への制限が、拡張の選び方で変わらないことの確認。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
  (V : IndConeExtendedSliceData κ D q G)
/-- 概要：同じ再構成した終点面の旧族制限は、元の初期全円柱の同じ終点面。
方針：元の全円柱の固定条件。規約：全射の等号。使われ方：元の指定比較の旧族回収。 -/
lemma indConeEndpointSliceCone_old :
    joinMap (joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ≫ indConeEndpointSliceCone V =
    tensorRightPoint (join T (Δ[0] : SSet.{u + 1}))
      (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ V.initial.prism := by
  rw [indConeEndpointSliceCone, ← Category.assoc, tensorRightPoint_naturality,
    Category.assoc, V.old]
/-- 概要：同じ全底余錐の旧族制限は、元の初期全円柱の同じ底余錐。
方針：元の slice 射影で写す。規約：全射の等号。使われ方：指定比較の底の旧族回収。 -/
lemma indConeEndpointBaseCone_old :
    joinMap (joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ≫ indConeEndpointBaseCone V =
    tensorRightPoint (join T (Δ[0] : SSet.{u + 1}))
      (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ V.initial.prism ≫
        sliceOverProjection (indConeEndpointPoint κ D) := by
  rw [indConeEndpointBaseCone, ← Category.assoc, indConeEndpointSliceCone_old, Category.assoc]
end SerrePositivity.InfinityCategories.F2.Ind
