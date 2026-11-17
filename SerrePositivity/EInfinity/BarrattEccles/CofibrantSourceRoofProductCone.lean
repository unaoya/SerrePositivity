module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofDegreeModel
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrameLimits

/-!
# 元の積単体の comma 表示上の指定次数と右脚の全自然変換

概要：元の D_m→D_n・D_m→Y と元の augmentation の三角形を全作用素で保持する。
方針：元の要素圏の次数から n へ向かう comma 圏を使い、同じ frame 射を評価する。
規約：任意可換環・元の代数射・全単体・Hom ULift・同じ指定次数を保持する。
使われ方：実 ProductHomMap と弱な基準射の全パラメータでの合成比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

abbrev cofibrantSourceRoofProductComma := CostructuredArrow (sourceFrameElementDegree A X Y)
  (cofibrantSourceRoofDegree A X Y b)

def cofibrantSourceRoofProductCommaIso : nerve (cofibrantSourceRoofProductElements A X Y b) ≅
    nerve (cofibrantSourceRoofProductComma A X Y b) := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexLiftedOver.nerveIso _ _

def cofibrantSourceRoofProductCommaFirstNerve : nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
    nerve (sourceFrameElementCategory A X Y) where
  app _ := ↾fun σ => σ ⋙ CostructuredArrow.proj _ _
  naturality _ _ _ := rfl

lemma cofibrantSourceRoofProductCommaIso_first :
    (cofibrantSourceRoofProductCommaIso A X Y b).hom ≫
      cofibrantSourceRoofProductCommaFirstNerve A X Y b =
        cofibrantSourceRoofProductFirstNerve A X Y b := rfl

lemma cofibrantSourceRoofProductCommaIso_over :
    (cofibrantSourceRoofProductCommaIso A X Y b).hom ≫
      nerveMap (CostructuredArrow.toOver (sourceFrameElementDegree A X Y)
        (cofibrantSourceRoofDegree A X Y b)) = cofibrantSourceRoofProductOverNerve A X Y b := rfl

abbrev cofibrantSourceRoofProductCommaDegree : cofibrantSourceRoofProductComma A X Y b ⥤
    AsSmall.{u + 1} SimplexCategory :=
  CostructuredArrow.proj _ _ ⋙ sourceFrameElementDegree A X Y

abbrev cofibrantSourceRoofProductCommaDiagram : cofibrantSourceRoofProductComma A X Y b ⥤
    (cofibrantAlgebraRelativeCategory A).category :=
  cofibrantSourceRoofProductCommaDegree A X Y b ⋙ cofibrantDKSourceFrame A X

def cofibrantSourceRoofProductCommaEvaluation : cofibrantSourceRoofProductCommaDiagram A X Y b ⟶
    (Functor.const (cofibrantSourceRoofProductComma A X Y b)).obj
      ((cofibrantDKSourceFrame A X).obj (cofibrantSourceRoofDegree A X Y b)) where
  app s := (cofibrantDKSourceFrame A X).map s.hom
  naturality {_s _t} f := by
    change (cofibrantDKSourceFrame A X).map ((sourceFrameElementDegree A X Y).map f.left) ≫
      (cofibrantDKSourceFrame A X).map _ = _ ≫ 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, CostructuredArrow.w, Category.comp_id]

def cofibrantSourceRoofProductCommaRightLeg : cofibrantSourceRoofProductCommaDiagram A X Y b ⟶
    (Functor.const (cofibrantSourceRoofProductComma A X Y b)).obj
      (show (cofibrantAlgebraRelativeCategory A).category from Y) where
  app s := ((sourceFrameElementsToDK A X Y).obj s.left).hom
  naturality {_s _t} f := by
    exact (CostructuredArrow.w ((sourceFrameElementsToDK A X Y).map f.left)).trans
      (Category.comp_id _).symm

def cofibrantSourceRoofProductCommaAugmentation :
    cofibrantSourceRoofProductCommaDiagram A X Y b ⟶
      (Functor.const (cofibrantSourceRoofProductComma A X Y b)).obj
        (show (cofibrantAlgebraRelativeCategory A).category from X) :=
  Functor.whiskerLeft (cofibrantSourceRoofProductCommaDegree A X Y b)
    (cofibrantDKSourceFrameAugmentation A X)

lemma cofibrantSourceRoofProductCommaAugmentation_triangle :
    cofibrantSourceRoofProductCommaEvaluation A X Y b ≫
      (Functor.const (cofibrantSourceRoofProductComma A X Y b)).map
        ((cofibrantDKSourceFrameAugmentation A X).app (cofibrantSourceRoofDegree A X Y b)) =
          cofibrantSourceRoofProductCommaAugmentation A X Y b := by
  apply NatTrans.ext
  funext s
  exact ((cofibrantDKSourceFrameAugmentation A X).naturality s.hom).trans (Category.comp_id _)

lemma cofibrantSourceRoofProductCommaEvaluation_weak (s : cofibrantSourceRoofProductComma A X Y b) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((cofibrantSourceRoofProductCommaEvaluation A X Y b).app s) :=
  cofibrantDKSourceFrame_map_weak A X s.hom

lemma cofibrantSourceRoofProductCommaAugmentation_weak
    (s : cofibrantSourceRoofProductComma A X Y b) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((cofibrantSourceRoofProductCommaAugmentation A X Y b).app s) :=
  cofibrantDKSourceFrameAugmentation_weak A X ((sourceFrameElementDegree A X Y).obj s.left)

end SerrePositivity.EInfinity.BarrattEccles
