module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoMapPostPresentation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：元の後合成同型を関手族上で制限した成分は、元の同型の係数制限。
方針：同じ点評価の自然性と後合成作用の厳密な評価式を使う。
規約：中間の係数全空間に quasicategory 性を要求しない。
使われ方：任意のパラメータ上の輸送比較の始点自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定後合成同型の実成分は、同じ実係数で制限した元の指定値。 -/
lemma functorIso_map_post_restricted_app_heq {K X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] {f g : X ⟶ Y} (e : FunctorIso f g)
    (L : Z ⟶ (ihom K).obj X) (z : Z _⦋0⦌) (q : K ⟶ X)
    (hz : L.app (Opposite.op ⦋0⦌) z = functorVertex q) :
    HEq (((e.map_post K).precomp L).app z) (e.precomp q) := by
  let β := e.map_post K
  have happ := functorIso_app_heq_evaluate (β.precomp L) z
  have hcalc : HEq (VertexIso.map (β.precomp L) (evaluateFunctorAt z))
      (VertexIso.map β (evaluateFunctorAt (functorVertex q))) := by
    have hm := vertexIso_map_heq_of_heq (β.precomp L)
      (VertexIso.map β ((pre L).app ((ihom K).obj Y))) rfl rfl
      (functorIso_precomp_vertexMap_heq β L) (evaluateFunctorAt z)
    refine hm.trans ?_
    rw [vertexIso_map_comp]
    exact vertexIso_map_heq β ((evaluateFunctorAt_pre L z).trans
      (congrArg (fun v => evaluateFunctorAt (Y := (ihom K).obj Y) v) hz))
  have hmap := vertexIso_map_heq_of_heq β
    (VertexIso.map e (functorPostcompositionMap K X Y))
    (functorPostcompositionMap_vertex (K := K) f).symm
    (functorPostcompositionMap_vertex (K := K) g).symm
    (functorIso_map_post_heq_map e) (evaluateFunctorAt (functorVertex q))
  exact happ.trans (hcalc.trans (hmap.trans
    ((heq_of_eq (vertexIso_map_comp e (functorPostcompositionMap K X Y)
      (evaluateFunctorAt (functorVertex q)))).trans
      ((vertexIso_map_heq e (functorPostcompositionMap_evaluate q)).trans
        (functorIso_precomp_vertexMap_heq e q).symm))))

end SerrePositivity.InfinityCategories.F2
