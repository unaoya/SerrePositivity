module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexAppendMorphism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPostReindex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.AppendMorphismReindexIndex

/-!
概要：元の最終射を付け足す操作は、同じ二重の終点固定添字制限に自然。
方針：最後の退化の自然性と、元の指定後合成の全 Hom 自然性を貼る。
規約：指定した最終射を変更しない。使われ方：元の三射の実高次族を束ねる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ最終射の追加は、元の最後を固定する任意の添字制限に厳密に自然。 -/
lemma coherentSimplexAppendMorphism_reindex
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (s : (SimplicialNerve C) _⦋n + 1⦌) {Y : C}
    (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y) :
    (SimplicialNerve C).map (PinchedHom.extend (PinchedHom.extend α)).op
        (coherentSimplexAppendMorphism s g) =
      coherentSimplexAppendMorphism ((SimplicialNerve C).map (PinchedHom.extend α).op s)
        (eqToHom (coherentSimplexLastReindex_last α s) ≫ g) := by
  let S : (SimplicialNerve C) _⦋n + 2⦌ := (SimplicialNerve C).σ (Fin.last (n + 1)) s
  let T : (SimplicialNerve C) _⦋m + 1⦌ :=
    (SimplicialNerve C).map (PinchedHom.extend α).op s
  have hsrc := simplicialLastDegenerate_reindex α s
  have h := coherentSimplexLastPost_of_source_eq hsrc
    ((coherentSimplexLastReindex_last (PinchedHom.extend α) S).trans
      (coherentSimplexLastDegenerate_last s))
    ((coherentSimplexLastDegenerate_last T).trans (coherentSimplexLastReindex_last α s)) g
  calc
    _ = coherentSimplexLastPost
        ((SimplicialNerve C).map (PinchedHom.extend (PinchedHom.extend α)).op S)
        (eqToHom (coherentSimplexLastReindex_last (PinchedHom.extend α) S) ≫
          eqToHom (coherentSimplexLastDegenerate_last s) ≫ g) :=
      coherentSimplexLastPost_reindex (PinchedHom.extend α) S
        (eqToHom (coherentSimplexLastDegenerate_last s) ≫ g)
    _ = coherentSimplexLastPost ((SimplicialNerve C).σ (Fin.last (m + 1)) T)
        (eqToHom (coherentSimplexLastDegenerate_last T) ≫
          eqToHom (coherentSimplexLastReindex_last α s) ≫ g) := by
      simpa only [← Category.assoc, eqToHom_trans] using h
    _ = _ := rfl

end SerrePositivity.InfinityCategories.F2
