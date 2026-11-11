module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofDegreeModel
public import SerrePositivity.EInfinity.FrameHom.FrameRoofSliceFibration

/-!
# 元の cofibrant 屋根 slice から積単体モデルへの Kan fibration

概要：元の指定点の実 Quillen A slice の次数比較そのものを充填可能にする。
方針：同じ全単体の次数等式で正規化し、元の積単体同型で標的だけを戻す。
規約：任意可換環・元の q・元の全錐・指定点の次数を保持する。
使われ方：実 slice と同じ Kan Hom 比較のホモトピー fiber の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet HomotopicalAlgebra
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofDegreeTransportIso :
    pullback (cofibrantSourceFrameRoofMap A X Y ≫ cofibrantSourceRoofProjection A X Y)
      (nerveMap (Over.forget (cofibrantSourceRoofDegree A X Y b))) ≅
        cofibrantSourceRoofDegreeModel A X Y b :=
  pullback.congrHom (cofibrantSourceFrameRoofMap_degree A X Y) rfl

lemma cofibrantSourceRoofDegreeTransportIso_source :
    (cofibrantSourceRoofDegreeTransportIso A X Y b).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  simp only [cofibrantSourceRoofDegreeTransportIso, pullback.congrHom_hom,
    pullback.map, pullback.lift_fst, Category.comp_id]

lemma cofibrantSourceRoofDegreeTransportIso_over :
    (cofibrantSourceRoofDegreeTransportIso A X Y b).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  simp only [cofibrantSourceRoofDegreeTransportIso, pullback.congrHom_hom,
    pullback.map, pullback.lift_snd, Category.comp_id]

lemma cofibrantSourceRoofSliceDegreeMap_eq_generic : cofibrantSourceRoofSliceDegreeMap A X Y b =
    roofQuillenSliceDegreeMap (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      b (cofibrantSourceFrameRoofMap A X Y) ≫
        (cofibrantSourceRoofDegreeTransportIso A X Y b).hom := by
  apply pullback.hom_ext
  · rw [cofibrantSourceRoofSliceDegreeMap_source, Category.assoc,
      cofibrantSourceRoofDegreeTransportIso_source, roofQuillenSliceDegreeMap_source]
  · rw [Category.assoc, cofibrantSourceRoofDegreeTransportIso_over,
      roofQuillenSliceDegreeMap_over]
    exact pullback.lift_snd _ _ _

lemma cofibrantSourceRoofSliceDegreeMap_fibration :
    Fibration (cofibrantSourceRoofSliceDegreeMap A X Y b) := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  have := roofQuillenSliceDegreeMap_fibration (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    b (cofibrantSourceFrameRoofMap A X Y)
  rw [cofibrantSourceRoofSliceDegreeMap_eq_generic]
  infer_instance

def cofibrantSourceRoofSliceProductMap : cofibrantSourceRoofSlice A X Y b ⟶
    nerve (cofibrantSourceRoofProductElements A X Y b) :=
  cofibrantSourceRoofSliceDegreeMap A X Y b ≫ (cofibrantSourceRoofProductIso A X Y b).inv

lemma cofibrantSourceRoofSliceProductMap_degree : cofibrantSourceRoofSliceProductMap A X Y b ≫
    (cofibrantSourceRoofProductIso A X Y b).hom = cofibrantSourceRoofSliceDegreeMap A X Y b := by
  simp only [cofibrantSourceRoofSliceProductMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

lemma cofibrantSourceRoofSliceProductMap_fibration :
    Fibration (cofibrantSourceRoofSliceProductMap A X Y b) := by
  have := cofibrantSourceRoofSliceDegreeMap_fibration A X Y b
  dsimp only [cofibrantSourceRoofSliceProductMap]
  infer_instance

lemma cofibrantSourceRoofSliceProductMap_source : cofibrantSourceRoofSliceProductMap A X Y b ≫
    cofibrantSourceRoofProductFirstNerve A X Y b = pullback.fst _ _ := by
  calc
    _ = cofibrantSourceRoofSliceProductMap A X Y b ≫
        ((cofibrantSourceRoofProductIso A X Y b).hom ≫ pullback.fst _ _) :=
      congrArg (fun f => cofibrantSourceRoofSliceProductMap A X Y b ≫ f)
        (cofibrantSourceRoofProductIso_source A X Y b).symm
    _ = (cofibrantSourceRoofSliceProductMap A X Y b ≫
        (cofibrantSourceRoofProductIso A X Y b).hom) ≫ pullback.fst _ _ :=
      (Category.assoc _ _ _).symm
    _ = cofibrantSourceRoofSliceDegreeMap A X Y b ≫ pullback.fst _ _ :=
      congrArg (fun f => f ≫ pullback.fst _ _) (cofibrantSourceRoofSliceProductMap_degree A X Y b)
    _ = _ := cofibrantSourceRoofSliceDegreeMap_source A X Y b

lemma cofibrantSourceRoofSliceProductMap_over : cofibrantSourceRoofSliceProductMap A X Y b ≫
    cofibrantSourceRoofProductOverNerve A X Y b = cofibrantSourceRoofSliceOver A X Y b := by
  calc
    _ = cofibrantSourceRoofSliceProductMap A X Y b ≫
        ((cofibrantSourceRoofProductIso A X Y b).hom ≫ pullback.snd _ _) :=
      congrArg (fun f => cofibrantSourceRoofSliceProductMap A X Y b ≫ f)
        (cofibrantSourceRoofProductIso_over A X Y b).symm
    _ = (cofibrantSourceRoofSliceProductMap A X Y b ≫
        (cofibrantSourceRoofProductIso A X Y b).hom) ≫ pullback.snd _ _ :=
      (Category.assoc _ _ _).symm
    _ = cofibrantSourceRoofSliceDegreeMap A X Y b ≫ pullback.snd _ _ :=
      congrArg (fun f => f ≫ pullback.snd _ _) (cofibrantSourceRoofSliceProductMap_degree A X Y b)
    _ = _ := pullback.lift_snd _ _ _

lemma cofibrantSourceRoofSliceProductMap_rightFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (cofibrantSourceRoofSliceProductMap A X Y b) where
  mem := by
    intro K L i hi
    cases hi with
    | @intro n i _hi =>
      exact ((SSet.modelCategoryQuillen.fibration_iff _).1
        (cofibrantSourceRoofSliceProductMap_fibration A X Y b)) _
        (SSet.modelCategoryQuillen.horn_ι_mem_J _ i)

lemma cofibrantSourceRoofSliceProductMap_fiber_kanComplex
    (v : (nerve (cofibrantSourceRoofProductElements A X Y b)) _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (cofibrantSourceRoofSliceProductMap A X Y b) v) := by
  have := cofibrantSourceRoofSliceProductMap_rightFibration A X Y b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex _ v

end SerrePositivity.EInfinity.BarrattEccles
