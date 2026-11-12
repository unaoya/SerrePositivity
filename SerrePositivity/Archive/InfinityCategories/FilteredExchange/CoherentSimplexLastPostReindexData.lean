module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPost
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PinchedReindex

/-!
概要：最後を固定する添字制限と指定後合成の、同じ全対象の照合。
方針：延長添字の旧頂点・最後の頂点を厳密に同定する。
規約：元の全添字写像を保持。使われ方：coherent slice の指定終域後合成の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 最後を固定する添字延長は、旧頂点も元の添字写像で送る。 -/
lemma coherentLastReindex_cast {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (SimplicialThickening.functor (PinchedHom.extend α).toOrderHom.uliftMap).obj
      (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (m + 2)))) =
        ⟨ULift.up (α.toOrderHom i).castSucc⟩ :=
  congrArg (fun j => (⟨ULift.up j⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
    (PinchedHom.extendOrderHom_castSucc α.toOrderHom i)

/-- 最後を固定する添字延長は、同じ最後の頂点を保つ。 -/
lemma coherentLastReindex_last {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (SimplicialThickening.functor (PinchedHom.extend α).toOrderHom.uliftMap).obj
      (⟨ULift.up (Fin.last (m + 1))⟩ : SimplicialThickening (ULift.{u} (Fin (m + 2)))) =
        ⟨ULift.up (Fin.last (n + 1))⟩ :=
  congrArg (fun j => (⟨ULift.up j⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
    (PinchedHom.extendOrderHom_last α.toOrderHom)

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {m n : ℕ}
  (α : ⦋m⦌ ⟶ ⦋n⦌) (s : (SimplicialNerve C) _⦋n + 1⦌) {Y : C}
  (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y)
local notation "F" => SimplicialThickening.functor
  (OrderHom.uliftMap (SimplexCategory.Hom.toOrderHom (PinchedHom.extend α)))
local notation "p" => EnrichedFunctor.comp SSet F s

/-- 添字制限した全単体の最後の対象も、同じ元の最後の対象。 -/
lemma coherentSimplexLastReindex_last :
    (p).obj ⟨ULift.up (Fin.last (m + 1))⟩ = s.obj ⟨ULift.up (Fin.last (n + 1))⟩ :=
  congrArg s.obj (coherentLastReindex_last α)

/-- 最後を固定する全添字制限と指定後合成は、全対象で一致する。 -/
lemma coherentSimplexLastPost_reindex_obj (i : Fin (m + 2)) :
    ((F).comp SSet (coherentSimplexLastPost s g)).obj ⟨ULift.up i⟩ =
    (coherentSimplexLastPost p (eqToHom (coherentSimplexLastReindex_last α s) ≫ g)).obj
      ⟨ULift.up i⟩ := by
  change coherentSimplexLastPostObj s (Y := Y) (PinchedHom.extendOrderHom α.toOrderHom i) =
    coherentSimplexLastPostObj p (Y := Y) i
  induction i using Fin.lastCases with
  | last =>
    rw [PinchedHom.extendOrderHom_last]
    exact (coherentSimplexLastPostObj_last s).trans
      (coherentSimplexLastPostObj_last p).symm
  | cast i =>
    rw [PinchedHom.extendOrderHom_castSucc, coherentSimplexLastPostObj_cast,
      coherentSimplexLastPostObj_cast]
    exact (congrArg s.obj (coherentLastReindex_cast α i)).symm

end SerrePositivity.InfinityCategories.F2
