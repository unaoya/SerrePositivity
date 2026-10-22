module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveHornFaceAgreement
public import SerrePositivity.InfinityCategories.F1.WeightedNerveCoefficientRestriction
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：weighted nerve の相対境界の全ての面と最後の係数評価を、元の底上に揃える。
方針：全境界の同じ図式を Yoneda 表示し、最後の係数への評価を各面で計算する。
規約：係数の充填性は不要。使われ方：成分ごとの自明 Kan 性からの全空間の境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] (F : I ⥤ SSet.{u}) {n : ℕ}
  (σ : ComposableArrows I (n + 1))
  (a : (boundary (n + 1) : SSet.{u}) ⟶ weightedNerve F)
  (ha : a ≫ weightedNerveProjection F =
    (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)

include ha in
/-- 元の境界の各面は、同じ底の射列の面上にある。 -/
lemma weightedBoundaryFace_base (j : Fin (n + 2)) :
    (SSet.yonedaEquiv (boundary.ι j ≫ a)).1 =
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ := by
  change (weightedNerveProjection F).app (Opposite.op ⦋n⦌)
    (SSet.yonedaEquiv (boundary.ι j ≫ a)) =
      (nerve I).map (SimplexCategory.δ j).op σ
  rw [← SSet.yonedaEquiv_comp, Category.assoc, ha, ← Category.assoc, boundary.ι_ι]
  exact (SSet.yonedaEquiv_naturality (SimplexCategory.δ j)
    ((SSet.yonedaEquiv (X := nerve I)).symm σ)).symm.trans
      (congrArg ((nerve I).map (SimplexCategory.δ j).op)
        ((SSet.yonedaEquiv (X := nerve I) (n := ⦋n + 1⦌)).apply_symm_apply σ))

/-- 元の境界面の重み付き図式を、指定した同じ底の面上で読む。 -/
def weightedBoundaryFaceDiagram (j : Fin (n + 2)) :
    simplexPrefixWeight n ⟶
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ ⋙ F :=
  weightedNerveSimplexDiagram F _ (SSet.yonedaEquiv (boundary.ι j ≫ a))
    (weightedBoundaryFace_base F σ a ha j)

lemma weightedBoundaryFaceDiagram_eta (j : Fin (n + 2)) :
    (⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
      weightedBoundaryFaceDiagram F σ a ha j⟩ : weightedNerveSimplex F n) =
      SSet.yonedaEquiv (boundary.ι j ≫ a) :=
  weightedNerveSimplexDiagram_eta F _ _ _

/-- 元の境界面の最後の係数は、同じ終点への輸送で評価される。 -/
lemma weightedBoundaryCoefficient_face (j : Fin (n + 2)) :
    boundary.ι j ≫ weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha =
      (weightedBoundaryFaceDiagram F σ a ha j).app (Fin.last n) ≫
        F.map (σ.map (homOfLE
          (Fin.le_last ((SimplexCategory.δ j).toOrderHom (Fin.last n))))) := by
  apply weightedNerveSimplexCoefficient_restriction F σ a (boundary (n + 1)).ι ha
    (boundary.ι j) (SimplexCategory.δ j) (boundary.ι_ι j)
    (weightedBoundaryFaceDiagram F σ a ha j)
  exact (congrArg SSet.yonedaEquiv.symm (weightedBoundaryFaceDiagram_eta F σ a ha j)).trans
    (SSet.yonedaEquiv.symm_apply_apply _)

end SerrePositivity.InfinityCategories.F2.Ind
