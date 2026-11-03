module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedronMaximalPath

/-!
概要：元の比較三単体の最大化は、元の最大化三角形の初点退化。
方針：全 Hom の nerve の各 path で元の最大 path の等式を使う。
規約：全豊穣関手の等式として指定図式を保持する。
使われ方：実 coslice 比較円柱の始点を標準の全族へ同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 最大化後の比較三単体は同じ最大化三角形の最初の退化。 -/
lemma coherentCompositionTetrahedron_maximalization
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    coherentSimplexMaximalization (coherentCompositionTetrahedron s) =
      (SimplicialNerve C).σ 0 (coherentSimplexMaximalization s) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply congrArg ((s.map _ _).app d)
  apply CategoryTheory.Functor.ext
    (fun z ↦ coherentCompositionTetrahedron_maximal_path (P.obj z))

end SerrePositivity.InfinityCategories.F2
