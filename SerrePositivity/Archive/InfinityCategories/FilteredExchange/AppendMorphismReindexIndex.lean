module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Index

/-!
概要：最後の頂点を複製する退化は、最後を二回固定した添字制限と可換。
方針：最後と旧頂点に分け、同じ順序写像を計算する。
規約：任意の面・退化を扱う。使われ方：指定射を追加する実全単体の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の最後の複製は、二重の最終点固定制限と可換。 -/
lemma pinchedExtend_lastDegeneracy {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    PinchedHom.extend (PinchedHom.extend α) ≫ SimplexCategory.σ (Fin.last (n + 1)) =
      SimplexCategory.σ (Fin.last (m + 1)) ≫ PinchedHom.extend α := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (Fin.last (n + 1)).predAbove
      (PinchedHom.extendOrderHom (PinchedHom.extend α).toOrderHom i) =
    (PinchedHom.extend α).toOrderHom ((Fin.last (m + 1)).predAbove i)
  induction i using Fin.lastCases with
  | last =>
    rw [PinchedHom.extendOrderHom_last, Fin.predAbove_right_last,
      Fin.predAbove_right_last]
    exact (PinchedHom.extendOrderHom_last α.toOrderHom).symm
  | cast i =>
    rw [PinchedHom.extendOrderHom_castSucc,
      Fin.predAbove_castSucc_of_le _ _ (Fin.le_last _),
      Fin.predAbove_castSucc_of_le _ _ (Fin.le_last _)]

/-- 同じ最後の退化単体の添字制限を、元の単体の制限後の退化で計算する。 -/
lemma simplicialLastDegenerate_reindex {X : SSet.{u}} {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (s : X _⦋n + 1⦌) :
    X.map (PinchedHom.extend (PinchedHom.extend α)).op (X.σ (Fin.last (n + 1)) s) =
      X.σ (Fin.last (m + 1)) (X.map (PinchedHom.extend α).op s) := by
  have h := congrArg (fun a => X.map a.op s) (pinchedExtend_lastDegeneracy α)
  simpa only [op_comp, CategoryTheory.Functor.map_comp_apply, SimplicialObject.σ] using h

end SerrePositivity.InfinityCategories.F2
