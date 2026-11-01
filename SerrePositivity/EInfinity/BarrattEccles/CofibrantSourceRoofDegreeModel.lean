module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofSlices
public import SerrePositivity.InfinityCategories.HomotopyLimits.ProductSimplexLiftedOver
public import SerrePositivity.InfinityCategories.HomotopyLimits.MixedNerveCostructuredPullback

/-!
# 実屋根 slice の次数モデルと元の sourceFrameHom×Δ[n]

概要：指定した屋根の点の次数モデルを、元の積単体の反対要素圏と厳密に同定する。
方針：同じ標準単体の全射と Hom ULift の往復から、comma nerve の引き戻しへ送る。
規約：任意可換環・元の sourceFrameHom・指定点の次数・元の全作用素を保持する。
使われ方：実 Quillen A slice と同じ Kan Hom 比較の fiber の照合への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite
open SerrePositivity.EInfinity.FrameHom
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

abbrev cofibrantSourceRoofProductElements :=
  ProductSimplexLiftedOver.productElements (((sourceFrameHom A).obj (op X.obj)).obj Y.obj)
    (cofibrantSourceRoofDegree A X Y b)

def cofibrantSourceRoofProductFirst : cofibrantSourceRoofProductElements A X Y b ⥤
    sourceFrameElementCategory A X Y :=
  ProductSimplexLiftedOver.firstComponent _ _

def cofibrantSourceRoofProductFirstNerve :
    nerve (cofibrantSourceRoofProductElements A X Y b) ⟶
      nerve (sourceFrameElementCategory A X Y) where
  app _ := ↾fun σ => σ ⋙ cofibrantSourceRoofProductFirst A X Y b
  naturality _ _ _ := rfl

def cofibrantSourceRoofProductOver : cofibrantSourceRoofProductElements A X Y b ⥤
    Over (cofibrantSourceRoofDegree A X Y b) := ProductSimplexLiftedOver.over _ _

def cofibrantSourceRoofProductOverNerve : nerve (cofibrantSourceRoofProductElements A X Y b) ⟶
    nerve (Over (cofibrantSourceRoofDegree A X Y b)) where
  app _ := ↾fun σ => σ ⋙ cofibrantSourceRoofProductOver A X Y b
  naturality _ _ _ := rfl

def cofibrantSourceRoofProductIso : nerve (cofibrantSourceRoofProductElements A X Y b) ≅
    cofibrantSourceRoofDegreeModel A X Y b :=
  ProductSimplexLiftedOver.nerveIso _ _ ≪≫
    MixedNerveCostructuredPullback.pullbackIso (sourceFrameElementDegree A X Y)
      (cofibrantSourceRoofDegree A X Y b)

lemma cofibrantSourceRoofProductIso_source : (cofibrantSourceRoofProductIso A X Y b).hom ≫
    pullback.fst _ _ = cofibrantSourceRoofProductFirstNerve A X Y b := by
  have h := MixedNerveCostructuredPullback.pullbackIso_source
    (sourceFrameElementDegree A X Y) (cofibrantSourceRoofDegree A X Y b)
  exact (Category.assoc _ _ _).trans (congrArg
    (fun f => (ProductSimplexLiftedOver.nerveIso
      (((sourceFrameHom A).obj (op X.obj)).obj Y.obj)
      (cofibrantSourceRoofDegree A X Y b)).hom ≫ f) h)

lemma cofibrantSourceRoofProductIso_over : (cofibrantSourceRoofProductIso A X Y b).hom ≫
    pullback.snd _ _ = cofibrantSourceRoofProductOverNerve A X Y b := by
  have h := MixedNerveCostructuredPullback.pullbackIso_over
    (sourceFrameElementDegree A X Y) (cofibrantSourceRoofDegree A X Y b)
  exact (Category.assoc _ _ _).trans (congrArg
    (fun f => (ProductSimplexLiftedOver.nerveIso
      (((sourceFrameHom A).obj (op X.obj)).obj Y.obj)
      (cofibrantSourceRoofDegree A X Y b)).hom ≫ f) h)

end SerrePositivity.EInfinity.BarrattEccles
