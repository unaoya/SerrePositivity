module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantZigzagValue

/-!
# 保存済みの DK/Map^h π₀ 同値と元の全代数の局所化への値

概要：元の零次比較を元の包含の局所化 Hom 作用で評価する。
方針：元の同値の両逆則と同じ包含の因子化同型を使う。
規約：既存の比較同値を定義し直さない。
使われ方：高次比較からの誘導写像との全類での一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

lemma cofibrantAlgebraMappingSpacePiZeroEquiv_value
    (z : SSet.π₀ (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y)) :
    let := modelCategory A
    mappingSpacePiZeroEquiv A (weakEquivalences (operad A).Algebra).Q
        (op ((cofibrantAlgebraInclusion A).obj X)) ((cofibrantAlgebraInclusion A).obj Y) z =
      ((cofibrantAlgebraInclusionLocalizedIso A).app X).hom ≫
        (cofibrantAlgebraHoEquivalence A).functor.map
          (cofibrantAlgebraMappingSpacePiZeroEquiv A X Y z) ≫
        ((cofibrantAlgebraInclusionLocalizedIso A).app Y).inv := by
  let := modelCategory A
  let i := cofibrantAlgebraInclusionLocalizedIso A
  let E := cofibrantAlgebraHoEquivalence A
  let m := mappingSpacePiZeroEquiv A (weakEquivalences (operad A).Algebra).Q
    (op ((cofibrantAlgebraInclusion A).obj X)) ((cofibrantAlgebraInclusion A).obj Y)
  change m z = (i.app X).hom ≫ E.fullyFaithfulFunctor.homEquiv
    (E.fullyFaithfulFunctor.homEquiv.symm ((i.app X).inv ≫ m z ≫ (i.app Y).hom)) ≫ (i.app Y).inv
  rw [Equiv.apply_symm_apply]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

lemma cofibrantAlgebraDKPiZeroEquiv_value
    (z : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom (cofibrantAlgebraRelativeCategory A)
      (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y))) :
    let := modelCategory A
    mappingSpacePiZeroEquiv A (weakEquivalences (operad A).Algebra).Q
        (op ((cofibrantAlgebraInclusion A).obj X)) ((cofibrantAlgebraInclusion A).obj Y)
        (cofibrantAlgebraDKPiZeroEquiv A X Y z) =
      cofibrantAlgebraDKHoHomMap A X Y
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomPiZeroEquiv (cofibrantAlgebraRelativeCategory A)
          (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y) z) := by
  let := modelCategory A
  have h := cofibrantAlgebraMappingSpacePiZeroEquiv_value A X Y
    (cofibrantAlgebraDKPiZeroEquiv A X Y z)
  have he : cofibrantAlgebraMappingSpacePiZeroEquiv A X Y
      (cofibrantAlgebraDKPiZeroEquiv A X Y z) =
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv (cofibrantAlgebraWeakEquivalences A)
      (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomPiZeroEquiv (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y) z) :=
    Equiv.apply_symm_apply _ _
  rw [he] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles
