module

public import SerrePositivity.KST.Spectra.NormalizedValueCochainExactness
public import SerrePositivity.KST.Spectra.GroupNerveCoordinates

/-!
概要：零単体が一つの源では零次微分は零で、H¹ 消滅なら一次 cocycle も零。
方針：二つの面の値を一致させ、正規化複体の完全性で cocycle を零次の像へ戻す。
規約：H¹ の仮定は通常の正規化 cohomology の消滅。
使われ方：Goerss–Jardine VIII §2。有理骨格の最初の fiber の計算。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NormalizedValueCochains

noncomputable section

/-- 零単体が一つなら、正規化零次微分は零。 -/
lemma differential_zero_of_subsingleton (K : SSet.{u}) [Subsingleton (K _⦋0⦌)]
    (M : AddCommGrpCat.{u}) (a : K.nonDegenerate 0 → M) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M 0 a = 0 := by
  funext s
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential_apply, Fin.sum_univ_two]
  have he : K.δ (0 : Fin 2) s.val = K.δ (1 : Fin 2) s.val := Subsingleton.elim _ _
  simp [he]

/-- H¹ が零で零次微分も零なら一次 cocycle は零。 -/
theorem first_cocycle_eq_zero (K : SSet.{u}) [Subsingleton (K _⦋0⦌)]
    (M : AddCommGrpCat.{u}) (hH : IsZero ((complex K M).homology 1))
    (z : K.nonDegenerate 1 → M) (hz : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M 1 z = 0) : z = 0 := by
  obtain ⟨a, ha⟩ := exists_primitive_of_isZero K M 0 hH z hz
  rw [← ha, differential_zero_of_subsingleton]

end
end SerrePositivity.KST.Spectra.NormalizedValueCochains

namespace SerrePositivity.KST.Spectra.GroupNerve

/-- 群の nerve の零単体は一つだけ。 -/
instance zeroSimplex_subsingleton (G : Type u) [Group G] :
    Subsingleton ((nerve (AsSmall.{u} (SingleObj G))) _⦋0⦌) :=
  (coordinatesEquiv G 0).injective.subsingleton

end SerrePositivity.KST.Spectra.GroupNerve
