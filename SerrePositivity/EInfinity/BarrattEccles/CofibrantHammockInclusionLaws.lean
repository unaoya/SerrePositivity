module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantHammockInclusion

/-!
# 元の cofibrant hammock 包含と全語の正規化の一致

概要：元の各語の全射列を同じ包含で送った正規化を厳密に回収する。
方針：相対関手の元の正規化式と Hom の ULift 同型の全標準射の式を結ぶ。
規約：元の左比較射と元の全代数の reduced hammock を保持する。
使われ方：実 DK Hom と元の Map^h との同じ共通比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra
variable (A : Type u) [CommRing A]
  (X Y : (cofibrantAlgebraRelativeCategory A).category)
lemma cofibrantAlgebraHammockInclusionMap_normalization (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    let := modelCategory A
    Hammock.graphNormalization (cofibrantAlgebraRelativeCategory A).weakEquivalences X Y w ≫
        cofibrantAlgebraHammockInclusionMap A X Y =
      cofibrantAlgebraHammockGraphInclusionMap A X Y w ≫
        Hammock.graphNormalization (weakEquivalences (operad A).Algebra)
          ((cofibrantAlgebraDKInclusion A).obj X) ((cofibrantAlgebraDKInclusion A).obj Y) w := by
  let := modelCategory A
  change Hammock.graphNormalization (cofibrantAlgebraRelativeCategory A).weakEquivalences X Y w ≫
    (Hammock.Relative.reducedMap (cofibrantToAlgebraDKRelative A) X Y ≫
      (Hammock.HomLift.reducedIso (C := (operad A).Algebra)
        (weakEquivalences (operad A).Algebra) ((cofibrantAlgebraDKInclusion A).obj X)
          ((cofibrantAlgebraDKInclusion A).obj Y)).hom) = _
  rw [← Category.assoc, Hammock.Relative.graphNormalization_reducedMap, Category.assoc]
  let Z := (cofibrantAlgebraDKInclusion A).obj X
  let T := (cofibrantAlgebraDKInclusion A).obj Y
  let t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (cofibrantAlgebraRelativeCategory A).weakEquivalences w X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (Hammock.HomLift.liftedWeak (C := (operad A).Algebra)
        (weakEquivalences (operad A).Algebra)) w
        (ULiftHom.objUp.{u + 1, u + 1} Z) (ULiftHom.objUp.{u + 1, u + 1} T) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap (cofibrantToAlgebraDKRelative A) X Y).app w
  change t ≫ (Hammock.graphNormalization
      (Hammock.HomLift.liftedWeak (C := (operad A).Algebra)
        (weakEquivalences (operad A).Algebra)) _ _ w ≫
      (Hammock.HomLift.reducedIso (C := (operad A).Algebra)
        (weakEquivalences (operad A).Algebra) Z T).hom) =
    (t ≫ (Hammock.HomLift.graphIso (C := (operad A).Algebra)
      (weakEquivalences (operad A).Algebra) w Z T).hom) ≫
      Hammock.graphNormalization (weakEquivalences (operad A).Algebra) Z T w
  rw [Hammock.HomLift.reducedIso_graphNormalization (C := (operad A).Algebra), Category.assoc]
end SerrePositivity.EInfinity.BarrattEccles
