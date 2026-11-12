module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPathComposition
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativePinchedReference

/-!
# 実 comma 上の元の native roof の path Hom

概要：元の最大座標 prefix 写像を実 cofibrant comma の図式へ代入する。
方針：同じ評価・右脚・弱同値と元の Kan hammock Hom を使う。
規約：任意可換環・全時間単体・同じ native pinched 族を保持する。
使われ方：native roof の全三角形を与える混合 coherent prism。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SimplicialLocalization Hammock
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofProductCommaNativeFamilyMap :
    nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (cofibrantAlgebraRelativeCategory A).weakEquivalences
        (show (cofibrantAlgebraRelativeCategory A).category from
          cofibrantSourceRoofDegreeAlgebra A X Y b)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)) :=
  RoofPrefix.familyMap (cofibrantAlgebraRelativeCategory A)
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f)

lemma cofibrantSourceRoofProductCommaNativeFamilyMap_eq :
    cofibrantSourceRoofProductCommaNativeFamilyMap A X Y b =
    cofibrantSourceRoofProductCommaEvaluationRoofMap A X Y b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ := rfl

lemma cofibrantSourceRoofProductCommaNativeFamilyMap_pinched :
    cofibrantSourceRoofProductCommaNativeFamilyMap A X Y b ≫
      kanHammockHomPinchedMap (cofibrantAlgebraRelativeCategory A)
        (show (cofibrantAlgebraRelativeCategory A).category from
          cofibrantSourceRoofDegreeAlgebra A X Y b)
        (show (cofibrantAlgebraRelativeCategory A).category from Y) =
      cofibrantSourceRoofProductCommaNativePinchedMap A X Y b := rfl

def cofibrantSourceRoofProductCommaPrefixPathMap {n : ℕ}
    (Γ : Fin (n + 1) ⥤ cofibrantSourceRoofProductComma A X Y b)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.LastPath.{u + 1} n i) ⟶
      SimplicialCategory.sHom
        ((kanHammockSourceFunctor (cofibrantAlgebraRelativeCategory A)).obj
          ((cofibrantSourceRoofProductCommaDiagram A X Y b).obj (Γ.obj i)))
        ((kanHammockSourceFunctor (cofibrantAlgebraRelativeCategory A)).obj
          (show (cofibrantAlgebraRelativeCategory A).category from Y)) :=
  RoofPrefix.pathMap (cofibrantAlgebraRelativeCategory A)
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f) Γ t i

end SerrePositivity.EInfinity.BarrattEccles
