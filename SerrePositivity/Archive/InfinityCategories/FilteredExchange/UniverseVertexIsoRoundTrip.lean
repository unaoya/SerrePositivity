module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UniverseHomotopyFaithful
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerUnit

/-!
概要：指定頂点同型を宇宙下降して持ち上げ直すと、元の指定値を回収する。
方針：同じ実辺の像をホモトピー圏の関手として計算し、既存の往復則を使う。
規約：指定同型を保持。使われ方：模型三角形の縮小・再持ち上げの消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定頂点同型の持ち上げは、同じ射の類に対する持ち上げ関手の像。 -/
lemma uliftVertexIso_eq_mapIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : VertexIso x y) :
    uliftVertexIso.{u, v} e = (universeHomotopyUp.{u, v} X).mapIso e := by
  let a := Classical.choose (homotopyCategory_homMk_surjective x y e.hom)
  have ha := Classical.choose_spec (homotopyCategory_homMk_surjective x y e.hom)
  apply Iso.ext
  change Truncated.HomotopyCategory.homMk (uliftTruncatedEdge a) =
    (universeHomotopyUp X).map e.hom
  rw [← ha, universeHomotopyUp_map_homMk]

/-- 同じ指定頂点同型の下降と再持ち上げは、その元の値を厳密に回収する。 -/
lemma uliftVertexIso_downVertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌} (e : VertexIso x y) :
    uliftVertexIso.{u, v} (downVertexIso e) = e := by
  rw [uliftVertexIso_eq_mapIso, downVertexIso_eq_mapIso]
  apply eq_of_heq
  exact mapIso_heq_of_functor_eq (universeHomotopyDown_up.{u, v} X) e

end SerrePositivity.InfinityCategories.F2
