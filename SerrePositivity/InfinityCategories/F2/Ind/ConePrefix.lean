module

public import SerrePositivity.InfinityCategories.Core.JoinTensor

/-!
概要：右余錐の単体を元の切断まで制限すると左因子を回収する。
方針：先頭包含の切断の逆像と恒等左写像を計算する。
規約：空の先頭区間も含む。使われ方：補間余錐比較の単射性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- join の単体を切断まで制限すると、元の左因子の包含になる。 -/
lemma joinSimplex_prefix (A B : SSet.{u}) (n r : ℕ) (hr : r ≤ n + 1)
    (x : Join.augObj A r) (y : Join.augObj B (n + 1 - r)) :
    Join.augMap (join A B) (Join.prefixIncl (n + 1) r hr)
      (⟨⟨r, by omega⟩, x, y⟩ : Join.Simplex A B n) =
        Join.augHom (joinInl A B) r x := by
  cases r with
  | zero => rfl
  | succ r =>
    have hc : Join.pullCut (Join.prefixIncl (n + 1) (r + 1) hr) (r + 1) = r + 1 := by
      apply Join.cut_ext (Join.pullCut_le _ _) (le_refl _)
      intro i
      rw [Join.lt_pullCut_iff]
      rfl
    change Join.simplexMap A B (Join.prefixIncl (n + 1) (r + 1) hr)
      ⟨⟨r + 1, by omega⟩, x, y⟩ = Join.Simplex.inl x
    apply Join.Simplex.ext _ _ (Fin.ext hc)
    · exact (Join.augMap_congr A hc rfl
        (Join.leftMap (Join.prefixIncl (n + 1) (r + 1) hr) (r + 1))
        OrderHom.id (fun i j hij => hij) x x rfl).trans (Join.augMap_id A _ x)
    · exact @Subsingleton.elim (Join.augObj B (r + 1 - (r + 1)))
        (by simp only [Nat.sub_self, Join.augObj]; infer_instance) _ _

end SerrePositivity.InfinityCategories.F2.Ind
