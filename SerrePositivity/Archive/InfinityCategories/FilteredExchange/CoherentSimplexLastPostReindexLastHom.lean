module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPostReindexOldHom

/-!
概要：最後を固定する添字制限と指定後合成は、最後へ入る全 Hom で一致する。
方針：両豊穣関手の同じ添字移送を比較し、最後の後合成因子をそのまま続ける。
規約：元の全 Hom 写像と指定射を保持。使われ方：coherent slice の後合成の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {m n : ℕ}
  (α : ⦋m⦌ ⟶ ⦋n⦌) (s : (SimplicialNerve C) _⦋n + 1⦌) {Y : C}
  (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y)
local notation "F" => SimplicialThickening.functor
  (OrderHom.uliftMap (SimplexCategory.Hom.toOrderHom (PinchedHom.extend α)))
local notation "p" => EnrichedFunctor.comp SSet F s
local notation "gp" => eqToHom (coherentSimplexLastReindex_last α s) ≫ g
local notation "L" => EnrichedFunctor.comp SSet F (coherentSimplexLastPost s g)
local notation "R" => coherentSimplexLastPost p gp

/-- 最後へ入る元の全 Hom も、全添字制限の後で同じ指定後合成を保つ。 -/
lemma coherentSimplexLastPost_reindex_last_hom (i : Fin (m + 1)) :
    (L).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up (Fin.last (m + 1))⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentSimplexLastPost_reindex_obj α s g i.castSucc)
        (coherentSimplexLastPost_reindex_obj α s g (Fin.last (m + 1)))) =
      (R).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up (Fin.last (m + 1))⟩ := by
  apply simplicialHom_eq_of_normalized
    (coherentSimplexLastPost_reindex_obj α s g i.castSucc)
    (coherentSimplexLastPost_reindex_obj α s g (Fin.last (m + 1)))
    ((coherentSimplexLastPostObj_cast p (Y := Y) i).trans
      (congrArg s.obj (coherentLastReindex_cast α i)))
    (coherentSimplexLastPostObj_last p (Y := Y)) _ _
  change ((F).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up (Fin.last (m + 1))⟩ ≫
      (coherentSimplexLastPost s g).map ((F).obj ⟨ULift.up i.castSucc⟩)
        ((F).obj ⟨ULift.up (Fin.last (m + 1))⟩)) ≫ eqToHom _ =
    coherentSimplexLastPostHom p gp i.castSucc (Fin.last (m + 1)) ≫ eqToHom _
  have eL := enrichedFunctor_map_transport (coherentSimplexLastPost s g)
    (coherentLastReindex_cast α i) (coherentLastReindex_last α)
    (coherentSimplexLastPostObj_cast s (Y := Y) (α.toOrderHom i))
    (coherentSimplexLastPostObj_last s (Y := Y))
  erw [coherentSimplexLastPostHom_cast_last] at eL
  have eS := enrichedFunctor_map_transport s
    (coherentLastReindex_cast α i) (coherentLastReindex_last α) rfl rfl
  simp only [eqToHom_refl, Category.comp_id] at eS
  have eL' := congrArg (fun k =>
    (F).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up (Fin.last (m + 1))⟩ ≫ k) eL
  have eS' := congrArg (fun k =>
    (F).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up (Fin.last (m + 1))⟩ ≫ k) eS
  have eS'' := congrArg (fun k => k ≫
    eHomWhiskerLeft SSet (s.obj ⟨ULift.up (α.toOrderHom i).castSucc⟩) g) eS'
  have eR := coherentSimplexLastPostHom_cast_last_normalized p i
    (congrArg s.obj (coherentLastReindex_cast α i)) (coherentSimplexLastReindex_last α s) g
  simp only [Category.assoc] at eL' eS'' eR
  simpa only [Category.assoc] using (eL'.trans eS''.symm).trans eR.symm

end SerrePositivity.InfinityCategories.F2
