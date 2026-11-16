module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsRestriction

/-!
概要：元の指定切断射のホモトピー類を、同じ全錐の普遍辺の射影で表す。
方針：頂点の等式による辺の移送を、ホモトピー圏の等式の射との合成として書く。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存の制限の計算法則。
使われ方：S8 の元の射の像への分解を、指定された切断射の合成に戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight

/-- 辺の始点の型を等式で移す操作の、同じホモトピー類の式。 -/
private lemma homMk_edge_source_cast {X : SSet.{u}} {x x' y : X _⦋0⦌}
    (h : x = x') (e : SSet.Edge x y) :
    Truncated.HomotopyCategory.homMk
      (cast (congrArg (fun z => SSet.Edge (X := X) z y) h) e).toTruncated =
    eqToHom (congrArg HomotopyCategory.mk h.symm) ≫
      Truncated.HomotopyCategory.homMk e.toTruncated := by
  cases h
  simp only [cast_eq, eqToHom_refl, Category.id_comp]

/-- 元の切断射は、同じ制限錐の普遍辺の頂点射影と始点の等式の移送で表される。 -/
lemma sectionsMap_hom_eq_projection {I : Type u} [SmallCategory I]
    {P Q : I ⥤ Type u} {E : SSet.{u + 1}} [Quasicategory E]
    (φ : P ⟶ Q) (O : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (c : JoinCone (diagram P O)) (hc : IsLimitCone c)
    (q : JoinCone (diagram Q O)) (hq : IsLimitCone q) :
    Truncated.HomotopyCategory.homMk (sectionsMap φ O c hc q hq).toTruncated =
      eqToHom (congrArg HomotopyCategory.mk (restrictSectionsCone_vertex φ O q).symm) ≫
        (hoFunctor.map (sliceOverProjection (diagram P O))).toFunctor.map
          (Truncated.HomotopyCategory.homMk (sectionsConeMap φ O c hc q).toTruncated) := by
  let a : SSet.Edge (restrictSectionsCone φ O q).vertex c.vertex :=
    (sectionsConeMap φ O c hc q).map (sliceOverProjection (diagram P O))
  have h := homMk_edge_source_cast (y := c.vertex) (restrictSectionsCone_vertex φ O q) a
  exact h

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
