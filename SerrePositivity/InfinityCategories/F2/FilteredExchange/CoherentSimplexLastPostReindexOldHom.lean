module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPostReindexData
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPostNormalized

/-!
概要：最後を固定する全添字制限と指定後合成は、旧二対象間の全 Hom で一致する。
方針：同じ二頂点の添字等式で元の二つの豊穣関手の Hom を正規化する。
規約：添字制限の実 Hom 写像を保持。使われ方：coherent slice の後合成の自然性。
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

/-- 最後を固定する添字制限と指定後合成は、旧頂点間の実 Hom 作用まで一致する。 -/
lemma coherentSimplexLastPost_reindex_old_hom (i j : Fin (m + 1)) :
    (L).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentSimplexLastPost_reindex_obj α s g i.castSucc)
        (coherentSimplexLastPost_reindex_obj α s g j.castSucc)) =
      (R).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ := by
  apply simplicialHom_eq_of_normalized
    (coherentSimplexLastPost_reindex_obj α s g i.castSucc)
    (coherentSimplexLastPost_reindex_obj α s g j.castSucc)
    ((coherentSimplexLastPostObj_cast p (Y := Y) i).trans
      (congrArg s.obj (coherentLastReindex_cast α i)))
    ((coherentSimplexLastPostObj_cast p (Y := Y) j).trans
      (congrArg s.obj (coherentLastReindex_cast α j))) _ _
  change ((F).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫
      (coherentSimplexLastPost s g).map ((F).obj ⟨ULift.up i.castSucc⟩)
        ((F).obj ⟨ULift.up j.castSucc⟩)) ≫ eqToHom _ =
    coherentSimplexLastPostHom p gp i.castSucc j.castSucc ≫ eqToHom _
  have eL := enrichedFunctor_map_transport (coherentSimplexLastPost s g)
    (coherentLastReindex_cast α i) (coherentLastReindex_cast α j)
    (coherentSimplexLastPostObj_cast s (Y := Y) (α.toOrderHom i))
    (coherentSimplexLastPostObj_cast s (Y := Y) (α.toOrderHom j))
  erw [coherentSimplexLastPostHom_cast_cast] at eL
  have eS := enrichedFunctor_map_transport s
    (coherentLastReindex_cast α i) (coherentLastReindex_cast α j) rfl rfl
  simp only [eqToHom_refl, Category.comp_id] at eS
  have eL' := congrArg (fun k => (F).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫ k) eL
  have eS' := congrArg (fun k => (F).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫ k) eS
  have eR := coherentSimplexLastPostHom_cast_cast_normalized p gp i j
    (congrArg s.obj (coherentLastReindex_cast α i))
    (congrArg s.obj (coherentLastReindex_cast α j))
  simp only [Category.assoc] at eL' eS' eR
  simpa only [Category.assoc] using (eL'.trans eS'.symm).trans eR.symm

end SerrePositivity.InfinityCategories.F2
