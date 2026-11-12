module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 任意の単体的豊穣圏の各次数の評価圏

概要：元の豊穣 Hom の各次数の点を射とする、同じ対象集合上の圏を構成する。
方針：元の単位・合成・全公理を同じ点で評価する。
規約：豊穣目標にモデル構造や fibrancy を要求しない。
使われ方：自由積の次数ごとの評価を任意の豊穣目標へ適用する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory
open CategoryTheory MonoidalCategory

abbrev Objects (D : Type uD) := D

variable {D : Type uD} [EnrichedCategory SSet.{u} D]

@[instance_reducible]
def category (n : SimplexCategoryᵒᵖ) : Category.{u} (Objects D) where
  Hom X Y := (X ⟶[SSet.{u}] Y).obj n
  id X := (eId SSet.{u} X).app n PUnit.unit
  comp {X Y Z} p q := (eComp SSet.{u} X Y Z).app n (p, q)
  id_comp {X Y} p := congrArg (fun k => k.app n p) (e_id_comp SSet.{u} X Y)
  comp_id {X Y} p := congrArg (fun k => k.app n p) (e_comp_id SSet.{u} X Y)
  assoc {X Y Z T} p q r :=
    (congrArg (fun k => k.app n ((p, q), r)) (e_assoc' SSet.{u} X Y Z T)).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory
