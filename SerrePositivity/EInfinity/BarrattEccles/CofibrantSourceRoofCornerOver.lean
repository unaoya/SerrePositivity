module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerBaseProjection
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductCornerProjection

/-!
# 実積単体 corner の底は元の comma 評価の Over 図式

概要：元の corner の正規化された底の全図式を同じ次数へ向かう comma 図式に戻す。
方針：次数輸送の逆と元の積単体・comma 同型の第二射影を消去する。
規約：任意可換環・指定次数・元の全作用素を保持する。
使われ方：実評価の左円柱と標準評価の全関手圏での同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofDegreeTransportIso_inv_over :
    (cofibrantSourceRoofDegreeTransportIso A X Y b).inv ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  rw [Iso.inv_comp_eq]
  exact (cofibrantSourceRoofDegreeTransportIso_over A X Y b).symm

lemma cofibrantSourceRoofProductCornerMap_normalizedOver :
    cofibrantSourceRoofProductCornerMap A X Y b ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizationMap (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) b ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizedProjection (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) b =
    cofibrantSourceRoofProductOverNerve A X Y b := by
  have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeCornerMap_normalizedOver (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    b (cofibrantSourceFrameRoofMap A X Y)
  simp only [cofibrantSourceRoofProductCornerMap, Category.assoc, h]
  exact (congrArg (fun g => (cofibrantSourceRoofProductIso A X Y b).hom ≫ g)
    (cofibrantSourceRoofDegreeTransportIso_inv_over A X Y b)).trans
      (cofibrantSourceRoofProductIso_over A X Y b)

lemma cofibrantSourceRoofProductCommaCornerMap_normalizedOver :
    cofibrantSourceRoofProductCommaCornerMap A X Y b ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizationMap (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) b ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizedProjection (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) b =
    nerveMap (CostructuredArrow.toOver (sourceFrameElementDegree A X Y)
      (cofibrantSourceRoofDegree A X Y b)) := by
  have h : (cofibrantSourceRoofProductCommaIso A X Y b).inv ≫
      cofibrantSourceRoofProductOverNerve A X Y b =
    nerveMap (CostructuredArrow.toOver (sourceFrameElementDegree A X Y)
      (cofibrantSourceRoofDegree A X Y b)) := by
    rw [Iso.inv_comp_eq]
    exact (cofibrantSourceRoofProductCommaIso_over A X Y b).symm
  rw [cofibrantSourceRoofProductCommaCornerMap, Category.assoc,
    cofibrantSourceRoofProductCornerMap_normalizedOver]
  exact h

end SerrePositivity.EInfinity.BarrattEccles
