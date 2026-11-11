module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerProjectionLaws
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductCone
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofSliceCriterion

/-!
# 実 corner 比較の全始域図式と元の comma 図式の一致

概要：元の積単体と comma 表示から実 corner への射の始域射影を同定する。
方針：次数輸送の逆射と元の引き戻し射影を順に消去する。
規約：任意可換環・同じ q・元の全単体を保持する。
使われ方：幾何的三角形と元の自然変換の全関手圏での比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofDegreeTransportIso_inv_source :
    (cofibrantSourceRoofDegreeTransportIso A X Y b).inv ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  rw [Iso.inv_comp_eq]
  exact (cofibrantSourceRoofDegreeTransportIso_source A X Y b).symm

lemma cofibrantSourceRoofProductCornerMap_source :
    cofibrantSourceRoofProductCornerMap A X Y b ≫ pullback.snd _ _ =
      cofibrantSourceRoofProductFirstNerve A X Y b ≫ cofibrantSourceFrameRoofMap A X Y := by
  have h := roofQuillenDegreeCornerMap_source (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    b (cofibrantSourceFrameRoofMap A X Y)
  simp only [cofibrantSourceRoofProductCornerMap, Category.assoc, h]
  have h₁ := cofibrantSourceRoofDegreeTransportIso_inv_source A X Y b
  have h₂ := cofibrantSourceRoofProductIso_source A X Y b
  exact (congrArg (fun g => (cofibrantSourceRoofProductIso A X Y b).hom ≫ g ≫
    cofibrantSourceFrameRoofMap A X Y) h₁).trans
      ((Category.assoc _ _ _).symm.trans (congrArg
        (fun g => g ≫ cofibrantSourceFrameRoofMap A X Y) h₂))

def cofibrantSourceRoofProductCommaCornerMap :
    nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (cofibrantSourceRoofProjection A X Y) :=
  (cofibrantSourceRoofProductCommaIso A X Y b).inv ≫
    cofibrantSourceRoofProductCornerMap A X Y b

lemma cofibrantSourceRoofProductCommaCornerMap_source :
    cofibrantSourceRoofProductCommaCornerMap A X Y b ≫ pullback.snd _ _ =
      cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫ cofibrantSourceFrameRoofMap A X Y := by
  have h : (cofibrantSourceRoofProductCommaIso A X Y b).inv ≫
      cofibrantSourceRoofProductFirstNerve A X Y b =
        cofibrantSourceRoofProductCommaFirstNerve A X Y b := by
    rw [Iso.inv_comp_eq]
    exact (cofibrantSourceRoofProductCommaIso_first A X Y b).symm
  rw [cofibrantSourceRoofProductCommaCornerMap, Category.assoc,
    cofibrantSourceRoofProductCornerMap_source, ← Category.assoc, h]

lemma cofibrantSourceRoofProductCommaCornerMap_diagram :
    (cofibrantSourceRoofProductCommaCornerMap A X Y b ≫
      roofCornerSourceSliceMap (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) b) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (cofibrantHammockVertex A Y)) =
        nerveMap (cofibrantSourceRoofProductCommaDiagram A X Y b) ≫
          SimplicialLocalization.hammockLocalizationNerveMap
            (cofibrantAlgebraRelativeCategory A) := by
  have h := roofCornerSourceSliceMap_projection (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b
  have h₁ := cofibrantSourceRoofProductCommaCornerMap_source A X Y b
  have h₂ := cofibrantSourceFrameRoofMap_degree A X Y
  dsimp only [cofibrantHammockVertex]
  calc
    _ = cofibrantSourceRoofProductCommaCornerMap A X Y b ≫
        (pullback.snd _ _ ≫ cofibrantSourceRoofProjection A X Y ≫
          (nerveMap (cofibrantDKSourceFrame A X) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (cofibrantAlgebraRelativeCategory A))) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun g => cofibrantSourceRoofProductCommaCornerMap A X Y b ≫ g) h)
    _ = (cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫
        cofibrantSourceFrameRoofMap A X Y) ≫ cofibrantSourceRoofProjection A X Y ≫
          (nerveMap (cofibrantDKSourceFrame A X) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (cofibrantAlgebraRelativeCategory A)) := by
      simpa only [Category.assoc] using congrArg
        (fun g => g ≫ cofibrantSourceRoofProjection A X Y ≫
          (nerveMap (cofibrantDKSourceFrame A X) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (cofibrantAlgebraRelativeCategory A))) h₁
    _ = cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫
        sourceFrameElementDegreeNerve A X Y ≫ nerveMap (cofibrantDKSourceFrame A X) ≫
          SimplicialLocalization.hammockLocalizationNerveMap
            (cofibrantAlgebraRelativeCategory A) := by
      simpa only [Category.assoc] using congrArg
        (fun g => cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫ g ≫
          (nerveMap (cofibrantDKSourceFrame A X) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (cofibrantAlgebraRelativeCategory A))) h₂
    _ = _ := by
      simp only [← Category.assoc]
      apply congrArg (fun g => g ≫ SimplicialLocalization.hammockLocalizationNerveMap
        (cofibrantAlgebraRelativeCategory A))
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro σ
      rfl

end SerrePositivity.EInfinity.BarrattEccles
