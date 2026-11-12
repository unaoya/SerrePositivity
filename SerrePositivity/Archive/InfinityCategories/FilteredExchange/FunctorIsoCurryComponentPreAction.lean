module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoDisplayCurryComponent
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedRestrictionNaturality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPrecompCompositionValue
/-!
概要：元の curry の指定成分に対する前作用を、元の全比較の係数制限へ戻す。
方針：両端の頂点表示を明示し、curry・評価・前合成の同じ像を合成する。
規約：元の指定成分と全係数を保持する。
使われ方：Ncomp の元の値比較を、巨大な式の型を展開せず係数制限へ渡す。
-/

@[expose] public section
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
noncomputable section
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- 概要：curry の同じ指定成分の前作用は、同じ元の全比較の二段制限。
方針：curry と評価の同じ Hom の像を合成する。
規約：元の成分を保持。使われ方：表示変更済み成分の前作用の回収。 -/
lemma functorIso_curry_app_map_pre_heq {A B D X : SSet.{u}}
    [Quasicategory B] [Quasicategory X] {f g : A ⊗ B ⟶ X}
    (e : FunctorIso f g) (v : B _⦋0⦌) (r : D ⟶ A) :
    HEq (VertexIso.map (e.curry.app v) ((pre r).app X))
      ((e.precomp (lift (𝟙 A) (SSet.const v))).precomp r) := by
  have happ := vertexIso_map_heq_of_heq (e.curry.app v)
    (VertexIso.map e.curry (evaluateFunctorAt v))
    (evaluateFunctorAt_functorVertex v (curry f)).symm
    (evaluateFunctorAt_functorVertex v (curry g)).symm
    (functorIso_app_heq_evaluate e.curry v) ((pre r).app X)
  rw [vertexIso_map_comp] at happ
  have hc := vertexIso_map_heq_of_heq e.curry
    (VertexIso.map e (functorSpaceCurryMap A B X))
    (functorSpaceCurryMap_vertex f).symm (functorSpaceCurryMap_vertex g).symm
    (functorIso_curry_heq_map e) (evaluateFunctorAt v ≫ (pre r).app X)
  refine happ.trans (hc.trans ?_)
  rw [vertexIso_map_comp]
  have hh : functorSpaceCurryMap A B X ≫ (evaluateFunctorAt v ≫ (pre r).app X) =
      (pre (lift (𝟙 A) (SSet.const v))).app X ≫ (pre r).app X := by
    rw [← Category.assoc, functorSpaceCurryMap_evaluate]
  refine (vertexIso_map_heq e hh).trans ?_
  simp only [functorIso_precomp_eq_mapIso]
  exact heq_of_eq (vertexIso_map_comp e ((pre (lift (𝟙 A) (SSet.const v))).app X)
    ((pre r).app X)).symm
/-- 概要：表示変更した指定成分の前作用は、同じ元の全比較の合成係数制限。
方針：表示等式を除き、同じ二段制限を結合する。
規約：元の全係数を保持。使われ方：元の固定射の値比較の制限。 -/
lemma functorIsoOfEq_curry_app_map_pre_heq {A B D X : SSet.{u}}
    [Quasicategory B] [Quasicategory X] {f g : A ⊗ B ⟶ X}
    {f' g' : B ⟶ (ihom A).obj X} (e : FunctorIso f g)
    (hf : curry f = f') (hg : curry g = g') (v : B _⦋0⦌) (r : D ⟶ A) :
    HEq (VertexIso.map ((functorIsoOfEq e.curry hf hg).app v) ((pre r).app X))
      (e.precomp (r ≫ lift (𝟙 A) (SSet.const v))) := by
  cases hf
  cases hg
  exact (functorIso_curry_app_map_pre_heq e v r).trans
    (functorIso_precomp_precomp_heq e (lift (𝟙 A) (SSet.const v)) r)
end SerrePositivity.InfinityCategories.F2
