module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorCurryConstantFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元の相対 curry の指定比較の後合成を、元の同じ指定値の単一の像へ戻す。
方針：元の成分表示の補正を保持し、定値 fiber の全 curry の厳密な可換性を使う。
規約：元の指定同型と両端の実射を保持。使われ方：元の三角形比較と輸送比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の相対 curry の指定同型の後合成も、同じ元の指定同型の豊穣作用を保持する。 -/
lemma relativeFunctorCurryIso_postcomp_heq_map {A E B K Z : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (H H' : A ⊗ K ⟶ E)
    (hH : H ≫ p = fst A K ≫ a) (hH' : H' ≫ p = fst A K ≫ a)
    (e : VertexIso (relativeFunctorVertex p (fst A K ≫ a) H hH)
      (relativeFunctorVertex p (fst A K ≫ a) H' hH'))
    (q : relativeFunctorSpace p a ⟶ Z) :
    HEq ((relativeFunctorCurryIso p a H H' hH hH' e).postcomp q)
      (VertexIso.map e (relativeFunctorCurryHom p a K ≫ (ihom K).map q)) := by
  have he := relativeFunctorCurryIso_heq_map p a H H' hH hH' e
  have hs := (relativeFunctorCurryHom_vertex p a H hH).symm
  have ht := (relativeFunctorCurryHom_vertex p a H' hH').symm
  rw [functorIso_postcomp_eq_mapIso]
  exact (vertexIso_map_heq_of_heq _ _ hs ht he ((ihom K).map q)).trans
    (heq_of_eq (vertexIso_map_comp _ _ _))

/-- 定値標的の指定相対 curry 比較は、同じ fiber 値の通常の curry の指定像と一致。 -/
lemma relativeFunctorCurryIso_constant_fiber {A B K : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (H H' : A ⊗ K ⟶ leftUnstraightening (SSet.const z : B ⟶ SpaceInfinity))
    (hH : H ≫ leftUnstraighteningProjection (SSet.const z) = fst A K ≫ a)
    (hH' : H' ≫ leftUnstraighteningProjection (SSet.const z) = fst A K ≫ a)
    (e : VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z)) (fst A K ≫ a) H hH)
      (relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z)) (fst A K ≫ a) H' hH')) :
    HEq ((relativeFunctorCurryIso (leftUnstraighteningProjection (SSet.const z)) a H H'
      hH hH' e).postcomp (constantUnstraighteningRelativeIso a z).hom)
      (VertexIso.map (VertexIso.map e (constantUnstraighteningRelativeIso (fst A K ≫ a) z).hom)
        (functorSpaceCurryMap A K (vertexFiber pointedSpaceProjection z))) := by
  refine (relativeFunctorCurryIso_postcomp_heq_map _ a H H' hH hH' e
    (constantUnstraighteningRelativeIso a z).hom).trans ?_
  refine (vertexIso_map_heq e (relativeFunctorCurryHom_constant_fiber a z)).trans ?_
  exact (heq_of_eq (vertexIso_map_comp _ _ _)).symm

end SerrePositivity.InfinityCategories.F2
