module
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.KST.SConstruction.FunctorZeroEvaluation
public import SerrePositivity.KST.SConstruction.FullSubcomplexUniversalVertices

/-! # 同じ零関手から恒等関手への、全自然変換を持つ元の実収縮辺 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 正本の零圏を経由する、同じ元の零自己完全関手。 -/
def stableZeroEndMap (A : StableCategory.{u}) : ExactMap A A :=
  show A ⟶ A from (show A ⟶ zeroCategory from toZeroCategory A) ≫
    (show zeroCategory ⟶ A from fromZeroCategory A)

/-- 元の零自己関手の実値は、同じ選ばれた零対象への定値関手。 -/
theorem stableZeroEndMap_hom (A : StableCategory.{u}) :
    (stableZeroEndMap A).hom = SSet.const (chosenZeroVertex A.obj).vertex :=
  throughZero_hom A A

/-- 元の零自己関手の頂点は、全自然変換を持つ完全関手圏の実始対象。 -/
theorem stableZeroEndVertex_isInitial (A : StableCategory.{u}) :
    IsInitialVertex (exactFunctorVertexEquiv A A (stableZeroEndMap A)) := by
  have hz : IsZeroVertex (functorVertex (stableZeroEndMap A).hom) := by
    rw [stableZeroEndMap_hom]
    exact functor_const_isZeroVertex _ (chosenZeroVertex A.obj).isZero
  exact isInitialVertex_fullSubcomplex_of_ambient (IsExactVertex A A) _ hz.1

/-- 同じ元の零自己関手から恒等関手への実自然変換を、一つだけ選ぶ。 -/
def stableZeroEndContractionEdge (A : StableCategory.{u}) :
    Truncated.Edge (X := (truncation 2).obj (exactFunctors A A : SSet.{u}))
      (exactFunctorVertexEquiv A A (stableZeroEndMap A))
      (exactFunctorVertexEquiv A A (show A ⟶ A from 𝟙 A)) :=
  Classical.choice ((stableZeroEndVertex_isInitial A).nonempty_edge _)

/-- 選んだ同じ実辺の全単体を、全 S_n に共通のパラメータ族として保持する。 -/
def stableZeroEndContractionFamily (A : StableCategory.{u}) :
    (Δ[1] : SSet.{u}) ⟶ (exactFunctors A A : SSet.{u}) :=
  SSet.yonedaEquiv.symm (stableZeroEndContractionEdge A).edge

/-- 元の共通族の始点は、同じ零自己関手の実頂点。 -/
theorem stableZeroEndContractionFamily_zero (A : StableCategory.{u}) :
    stdSimplex.δ (1 : Fin 2) ≫ stableZeroEndContractionFamily A =
      SSet.yonedaEquiv.symm (exactFunctorVertexEquiv A A (stableZeroEndMap A)) := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, stableZeroEndContractionFamily, Equiv.apply_symm_apply]
  exact (stableZeroEndContractionEdge A).src_eq

/-- 元の共通族の終点は、同じ恒等関手の実頂点。 -/
theorem stableZeroEndContractionFamily_one (A : StableCategory.{u}) :
    stdSimplex.δ (0 : Fin 2) ≫ stableZeroEndContractionFamily A =
      SSet.yonedaEquiv.symm (exactFunctorVertexEquiv A A (show A ⟶ A from 𝟙 A)) := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, stableZeroEndContractionFamily, Equiv.apply_symm_apply]
  exact (stableZeroEndContractionEdge A).tgt_eq

end SerrePositivity.KST.Fibration
