module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeSimplex

/-!
# 元の豊穣目標の単位・合成の各次数の自然性

概要：元の全単体作用素による二点の合成と単位の移送を回収する。
方針：元の単体写像の自然性を同じ点で評価する。
規約：元の Hom・単位・合成そのものを使う。
使われ方：自由積の普遍的な評価を全次数で束ねる。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [EnrichedCategory SSet.{u} D] {n m : SimplexCategoryᵒᵖ}

lemma comp_simplex (θ : n ⟶ m) {X Y Z : D} (p : (X ⟶[SSet.{u}] Y).obj n)
    (q : (Y ⟶[SSet.{u}] Z).obj n) :
    (X ⟶[SSet.{u}] Z).map θ ((eComp SSet.{u} X Y Z).app n (p, q)) =
      (eComp SSet.{u} X Y Z).app m ((X ⟶[SSet.{u}] Y).map θ p, (Y ⟶[SSet.{u}] Z).map θ q) :=
  (congrArg (fun f => f (p, q)) ((eComp SSet.{u} X Y Z).naturality θ)).symm

lemma unit_simplex (θ : n ⟶ m) (X : D) :
    (X ⟶[SSet.{u}] X).map θ ((eId SSet.{u} X).app n PUnit.unit) =
      (eId SSet.{u} X).app m PUnit.unit :=
  (congrArg (fun f => f PUnit.unit) ((eId SSet.{u} X).naturality θ)).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
