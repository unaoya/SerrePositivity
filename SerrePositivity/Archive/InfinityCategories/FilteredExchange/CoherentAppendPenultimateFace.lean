module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexAppendMorphism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPostReindex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan

/-!
概要：同じ最終射を追加した実単体の最終手前の面を、元の後合成へ同定する。
方針：最後を固定する面制限の自然性と、退化の同じ面の厳密回収を使う。
規約：全 Hom の作用を保持。使われ方：三射の元の実高次図式の面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 追加した実単体の最後の手前を除くと、元の同じ最終射の後合成を回収する。 -/
lemma coherentSimplexAppendMorphism_face_penultimate
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
    (s : (SimplicialNerve C) _⦋n + 1⦌) {Y : C}
    (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y) :
    (SimplicialNerve C).δ (Fin.last (n + 1)).castSucc
        (coherentSimplexAppendMorphism s g) = coherentSimplexLastPost s g := by
  let α : ⦋n⦌ ⟶ ⦋n + 1⦌ := SimplexCategory.δ (Fin.last (n + 1))
  let S : (SimplicialNerve C) _⦋n + 2⦌ := (SimplicialNerve C).σ (Fin.last (n + 1)) s
  have hsrc : (SimplicialNerve C).map (PinchedHom.extend α).op S = s := by
    rw [show PinchedHom.extend α =
      SimplexCategory.δ (Fin.last (n + 1)).castSucc from pinchedExtend_δ _]
    exact ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_σ_self (SimplicialNerve C) (i := Fin.last (n + 1))) s
  have h := coherentSimplexLastPost_of_source_eq
    (s := (SimplicialNerve C).map (PinchedHom.extend α).op S) (t := s) hsrc
    ((coherentSimplexLastReindex_last α S).trans (coherentSimplexLastDegenerate_last s)) rfl g
  let gS : S.obj ⟨ULift.up (Fin.last (n + 2))⟩ ⟶ Y :=
    eqToHom (coherentSimplexLastDegenerate_last s) ≫ g
  calc
    _ = (SimplicialNerve C).map (PinchedHom.extend α).op
        (coherentSimplexLastPost S gS) := by
      exact congrArg (fun a : ⦋n + 1⦌ ⟶ ⦋n + 2⦌ =>
        (SimplicialNerve C).map a.op (coherentSimplexLastPost S gS))
          (pinchedExtend_δ (Fin.last (n + 1))).symm
    _ = coherentSimplexLastPost ((SimplicialNerve C).map (PinchedHom.extend α).op S)
        (eqToHom (coherentSimplexLastReindex_last α S) ≫ gS) :=
      coherentSimplexLastPost_reindex α S gS
    _ = _ := by
      dsimp only [gS]
      rw [← Category.assoc, eqToHom_trans]
      simpa only [eqToHom_refl, Category.id_comp] using h

end SerrePositivity.InfinityCategories.F2
