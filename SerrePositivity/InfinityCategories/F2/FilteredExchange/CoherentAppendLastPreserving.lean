module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentAppendMorphismReindex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.AppendLastPreservingIndex

/-!
概要：指定射の追加は、最後を保つ任意の全単体制限に厳密に自然。
方針：最後の複製の自然性を元の指定後合成の自然性へ貼る。
規約：零次元と全 Hom の作用を含む。使われ方：追加射を固定終辺として束ねる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 最後を保つ実添字制限は、元の同じ最終対象を持つ。 -/
lemma coherentSimplexLastPreserving_last
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (hα : α.toOrderHom (Fin.last m) = Fin.last n)
    (s : (SimplicialNerve C) _⦋n⦌) :
    ((SimplicialNerve C).map α.op s).obj ⟨ULift.up (Fin.last m)⟩ =
      s.obj ⟨ULift.up (Fin.last n)⟩ :=
  congrArg (fun i => s.obj ⟨ULift.up i⟩) hα

/-- 指定射の追加は、元の最後を保つ任意の実添字制限に厳密に自然。 -/
lemma coherentSimplexAppendMorphism_lastPreserving
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (hα : α.toOrderHom (Fin.last m) = Fin.last n)
    (s : (SimplicialNerve C) _⦋n⦌) {Y : C}
    (g : s.obj ⟨ULift.up (Fin.last n)⟩ ⟶ Y) :
    (SimplicialNerve C).map (PinchedHom.extend α).op (coherentSimplexAppendMorphism s g) =
      coherentSimplexAppendMorphism ((SimplicialNerve C).map α.op s)
        (eqToHom (coherentSimplexLastPreserving_last α hα s) ≫ g) := by
  let S : (SimplicialNerve C) _⦋n + 1⦌ := (SimplicialNerve C).σ (Fin.last n) s
  let T : (SimplicialNerve C) _⦋m⦌ := (SimplicialNerve C).map α.op s
  have hsrc := simplicialLastDegenerate_lastPreserving α hα s
  have h := coherentSimplexLastPost_of_source_eq hsrc
    ((coherentSimplexLastReindex_last α S).trans (coherentSimplexLastDegenerate_last s))
    ((coherentSimplexLastDegenerate_last T).trans
      (coherentSimplexLastPreserving_last α hα s)) g
  calc
    _ = coherentSimplexLastPost ((SimplicialNerve C).map (PinchedHom.extend α).op S)
        (eqToHom (coherentSimplexLastReindex_last α S) ≫
          eqToHom (coherentSimplexLastDegenerate_last s) ≫ g) :=
      coherentSimplexLastPost_reindex α S (eqToHom (coherentSimplexLastDegenerate_last s) ≫ g)
    _ = coherentSimplexLastPost ((SimplicialNerve C).σ (Fin.last m) T)
        (eqToHom (coherentSimplexLastDegenerate_last T) ≫
          eqToHom (coherentSimplexLastPreserving_last α hα s) ≫ g) := by
      simpa only [← Category.assoc, eqToHom_trans] using h
    _ = _ := rfl

end SerrePositivity.InfinityCategories.F2
