module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.AppendMorphismReindexIndex

/-!
概要：最後を保つ任意の添字制限は、最後の複製と可換。
方針：新しい最後と旧頂点に分け、元の最終頂点の条件を使う。
規約：零次元への制限を含む。使われ方：追加した射の固定終辺の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 最後を保つ任意の添字写像の延長は、元の最後の複製と可換。 -/
lemma pinchedExtend_lastPreserving_degeneracy {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (hα : α.toOrderHom (Fin.last m) = Fin.last n) :
    PinchedHom.extend α ≫ SimplexCategory.σ (Fin.last n) =
      SimplexCategory.σ (Fin.last m) ≫ α := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (Fin.last n).predAbove (PinchedHom.extendOrderHom α.toOrderHom i) =
    α.toOrderHom ((Fin.last m).predAbove i)
  induction i using Fin.lastCases with
  | last =>
    rw [PinchedHom.extendOrderHom_last, Fin.predAbove_right_last, Fin.predAbove_right_last]
    exact hα.symm
  | cast i =>
    rw [PinchedHom.extendOrderHom_castSucc,
      Fin.predAbove_castSucc_of_le _ _ (Fin.le_last _),
      Fin.predAbove_castSucc_of_le _ _ (Fin.le_last _)]

/-- 元の最後の退化は、最後を保つ任意の実添字制限に関して自然。 -/
lemma simplicialLastDegenerate_lastPreserving {X : SSet.{u}} {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (hα : α.toOrderHom (Fin.last m) = Fin.last n) (s : X _⦋n⦌) :
    X.map (PinchedHom.extend α).op (X.σ (Fin.last n) s) =
      X.σ (Fin.last m) (X.map α.op s) := by
  have h := congrArg (fun a => X.map a.op s) (pinchedExtend_lastPreserving_degeneracy α hα)
  simpa only [op_comp, CategoryTheory.Functor.map_comp_apply, SimplicialObject.σ] using h

end SerrePositivity.InfinityCategories.F2
