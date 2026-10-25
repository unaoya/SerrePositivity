module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPostLaws

/-!
概要：coherent 単体の最後の対象を指定射で後合成し、旧面を厳密に保持する。
方針：元の全 Hom と最後へ入る後合成を、豊穣関手の二法則で束ねる。
規約：局所 Kan 性・新たな充填の選択は不要。
使われ方：Ncomp の合成 prism に固定射を追加する高次整合の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (s : (SimplicialNerve C) _⦋n + 1⦌) {Y : C}
  (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y)

/-- 最後へ入る全 Hom に指定射を後合成した、同じ次数の coherent 単体。 -/
def coherentSimplexLastPost : (SimplicialNerve C) _⦋n + 1⦌ where
  obj i := coherentSimplexLastPostObj s (Y := Y) i.as.down
  map i j := coherentSimplexLastPostHom s g i.as.down j.as.down
  map_id i := coherentSimplexLastPostHom_id s g i.as.down
  map_comp i j k := coherentSimplexLastPostHom_comp s g i.as.down j.as.down k.as.down

/-- 最後を含まない旧面の全対象・全 Hom は厳密に不変。 -/
lemma coherentSimplexLastPost_old_face :
    (SimplicialThickening.functor
      (Fin.castSuccOrderEmb.toOrderHom : Fin (n + 1) →o Fin (n + 2)).uliftMap).comp SSet
        (coherentSimplexLastPost s g) =
    (SimplicialThickening.functor
      (Fin.castSuccOrderEmb.toOrderHom : Fin (n + 1) →o Fin (n + 2)).uliftMap).comp SSet s := by
  apply EnrichedFunctor.ext SSet
    (fun i => coherentSimplexLastPostObj_cast s i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change (_ ≫ coherentSimplexLastPostHom s g i.castSucc j.castSucc) ≫ eqToHom _ = _
  rw [Category.assoc, coherentSimplexLastPostHom_cast_cast]
  rfl

/-- 新しい最後の頂点は指定射の終域そのもの。 -/
lemma coherentSimplexLastPost_last :
    (coherentSimplexLastPost s g).obj ⟨ULift.up (Fin.last (n + 1))⟩ = Y :=
  coherentSimplexLastPostObj_last s

/-- 同じ実単体の表示変更は、指定した同じ終域射の後合成を厳密に保持する。 -/
lemma coherentSimplexLastPost_of_source_eq {n : ℕ}
    {s t : (SimplicialNerve C) _⦋n + 1⦌} (e : s = t) {Z W : C}
    (hs : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ = Z)
    (ht : t.obj ⟨ULift.up (Fin.last (n + 1))⟩ = Z) (g : Z ⟶ W) :
    coherentSimplexLastPost s (eqToHom hs ≫ g) =
      coherentSimplexLastPost t (eqToHom ht ≫ g) := by
  cases e
  rfl

end SerrePositivity.InfinityCategories.F2
