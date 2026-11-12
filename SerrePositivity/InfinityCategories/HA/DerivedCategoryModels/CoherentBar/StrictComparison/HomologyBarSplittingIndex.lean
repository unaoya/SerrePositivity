module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarSimplicial
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting

/-!
概要：通常のホモロジー bar の単体を、非退化単体と全射の組へ分解する。
方針：元の nerve の canonical splitting の実余積性から添字同値を得る。
規約：全射は始点を保つため、始点のホモロジー係数も保たれる。
使われ方：非退化ホモロジー bar への通常の正規化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet
open scoped _root_.Simplicial
variable {J : Type u} [Category.{u} J]

abbrev dgHomologyBarSplittingLabel (Δ : SimplexCategoryᵒᵖ) :=
  Σ A : SimplicialObject.Splitting.IndexSet Δ, (nerve J).nonDegenerate A.1.unop.len

def dgHomologyBarSplittingIndexEquiv (Δ : SimplexCategoryᵒᵖ) :
    dgHomologyBarSplittingLabel (J := J) Δ ≃ (nerve J).obj Δ :=
  CofanTypes.equivOfIsColimit
    ((Cofan.isColimit_cofanTypes_iff ((nerve J).splitting.cofan Δ)).mpr
      ⟨(nerve J).splitting.isColimit Δ⟩)

lemma dgHomologyBarSplittingIndexEquiv_apply (Δ : SimplexCategoryᵒᵖ)
    (A : SimplicialObject.Splitting.IndexSet Δ)
    (s : (nerve J).nonDegenerate A.1.unop.len) :
    dgHomologyBarSplittingIndexEquiv (J := J) Δ ⟨A, s⟩ = (nerve J).map A.e.op s.val := rfl

lemma dgHomologyBarSplitting_epi_zero {Δ : SimplexCategoryᵒᵖ}
    (A : SimplicialObject.Splitting.IndexSet Δ) : A.e.toOrderHom 0 = 0 := by
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective (f := A.e)).mp inferInstance
    (0 : Fin (A.1.unop.len + 1))
  apply le_antisymm
  · rw [← hi]
    exact A.e.toOrderHom.monotone (Fin.zero_le i)
  · exact Fin.zero_le _

lemma dgHomologyBarSplittingIndexEquiv_first (Δ : SimplexCategoryᵒᵖ)
    (A : SimplicialObject.Splitting.IndexSet Δ)
    (s : (nerve J).nonDegenerate A.1.unop.len) :
    (dgHomologyBarSplittingIndexEquiv (J := J) Δ ⟨A, s⟩).obj 0 = s.val.obj 0 := by
  change s.val.obj (A.e.toOrderHom 0) = s.val.obj 0
  rw [dgHomologyBarSplitting_epi_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
