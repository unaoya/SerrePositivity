module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofDegreeModel
public import SerrePositivity.EInfinity.FrameHom.FrameRoofSliceFibration

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Limits Opposite SSet HomotopicalAlgebra
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofDegreeTransportIso :
    pullback (modelBifibrantSourceFrameRoofMap X Y q ≫ modelBifibrantSourceRoofProjection X Y q)
      (nerveMap (Over.forget (modelBifibrantSourceRoofDegree X Y q b))) ≅
        modelBifibrantSourceRoofDegreeModel X Y q b :=
  pullback.congrHom (modelBifibrantSourceFrameRoofMap_degree X Y q) rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofDegreeTransportIso_source :
    (modelBifibrantSourceRoofDegreeTransportIso X Y q b).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  simp only [modelBifibrantSourceRoofDegreeTransportIso, pullback.congrHom_hom,
    pullback.map, pullback.lift_fst, Category.comp_id]

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofDegreeTransportIso_over :
    (modelBifibrantSourceRoofDegreeTransportIso X Y q b).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  simp only [modelBifibrantSourceRoofDegreeTransportIso, pullback.congrHom_hom,
    pullback.map, pullback.lift_snd, Category.comp_id]

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceDegreeMap_eq_generic :
  modelBifibrantSourceRoofSliceDegreeMap X Y q b =
    roofQuillenSliceDegreeMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      b (modelBifibrantSourceFrameRoofMap X Y q) ≫
        (modelBifibrantSourceRoofDegreeTransportIso X Y q b).hom := by
  apply pullback.hom_ext
  · rw [modelBifibrantSourceRoofSliceDegreeMap_source, Category.assoc,
      modelBifibrantSourceRoofDegreeTransportIso_source, roofQuillenSliceDegreeMap_source]
  · rw [Category.assoc, modelBifibrantSourceRoofDegreeTransportIso_over,
      roofQuillenSliceDegreeMap_over]
    exact pullback.lift_snd _ _ _

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceDegreeMap_fibration :
    Fibration (modelBifibrantSourceRoofSliceDegreeMap X Y q b) := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  have := roofQuillenSliceDegreeMap_fibration (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    b (modelBifibrantSourceFrameRoofMap X Y q)
  rw [modelBifibrantSourceRoofSliceDegreeMap_eq_generic]
  infer_instance

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofSliceProductMap : modelBifibrantSourceRoofSlice X Y q b ⟶
    nerve (modelBifibrantSourceRoofProductElements X Y q b) :=
  modelBifibrantSourceRoofSliceDegreeMap X Y q b ≫ (modelBifibrantSourceRoofProductIso X Y q b).inv

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceProductMap_degree :
  modelBifibrantSourceRoofSliceProductMap X Y q b ≫
    (modelBifibrantSourceRoofProductIso X Y q b).hom =
      modelBifibrantSourceRoofSliceDegreeMap X Y q b := by
  simp only [modelBifibrantSourceRoofSliceProductMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceProductMap_fibration :
    Fibration (modelBifibrantSourceRoofSliceProductMap X Y q b) := by
  have := modelBifibrantSourceRoofSliceDegreeMap_fibration X Y q b
  dsimp only [modelBifibrantSourceRoofSliceProductMap]
  infer_instance

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceProductMap_source :
  modelBifibrantSourceRoofSliceProductMap X Y q b ≫
    modelBifibrantSourceRoofProductFirstNerve X Y q b = pullback.fst _ _ := by
  calc
    _ = modelBifibrantSourceRoofSliceProductMap X Y q b ≫
        ((modelBifibrantSourceRoofProductIso X Y q b).hom ≫ pullback.fst _ _) :=
      congrArg (fun f => modelBifibrantSourceRoofSliceProductMap X Y q b ≫ f)
        (modelBifibrantSourceRoofProductIso_source X Y q b).symm
    _ = (modelBifibrantSourceRoofSliceProductMap X Y q b ≫
        (modelBifibrantSourceRoofProductIso X Y q b).hom) ≫ pullback.fst _ _ :=
      (Category.assoc _ _ _).symm
    _ = modelBifibrantSourceRoofSliceDegreeMap X Y q b ≫ pullback.fst _ _ :=
      congrArg (fun f => f ≫
        pullback.fst _ _) (modelBifibrantSourceRoofSliceProductMap_degree X Y q b)
    _ = _ := modelBifibrantSourceRoofSliceDegreeMap_source X Y q b

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceProductMap_over :
  modelBifibrantSourceRoofSliceProductMap X Y q b ≫
    modelBifibrantSourceRoofProductOverNerve X Y q b =
      modelBifibrantSourceRoofSliceOver X Y q b := by
  calc
    _ = modelBifibrantSourceRoofSliceProductMap X Y q b ≫
        ((modelBifibrantSourceRoofProductIso X Y q b).hom ≫ pullback.snd _ _) :=
      congrArg (fun f => modelBifibrantSourceRoofSliceProductMap X Y q b ≫ f)
        (modelBifibrantSourceRoofProductIso_over X Y q b).symm
    _ = (modelBifibrantSourceRoofSliceProductMap X Y q b ≫
        (modelBifibrantSourceRoofProductIso X Y q b).hom) ≫ pullback.snd _ _ :=
      (Category.assoc _ _ _).symm
    _ = modelBifibrantSourceRoofSliceDegreeMap X Y q b ≫ pullback.snd _ _ :=
      congrArg (fun f => f ≫
        pullback.snd _ _) (modelBifibrantSourceRoofSliceProductMap_degree X Y q b)
    _ = _ := pullback.lift_snd _ _ _

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceProductMap_rightFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (modelBifibrantSourceRoofSliceProductMap X Y q b) where
  mem := by
    intro K L i hi
    cases hi with
    | @intro n i _hi =>
      exact ((SSet.modelCategoryQuillen.fibration_iff _).1
        (modelBifibrantSourceRoofSliceProductMap_fibration X Y q b)) _
        (SSet.modelCategoryQuillen.horn_ι_mem_J _ i)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceProductMap_fiber_kanComplex
    (v : (nerve (modelBifibrantSourceRoofProductElements X Y q b)) _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (modelBifibrantSourceRoofSliceProductMap X Y q b) v) := by
  have := modelBifibrantSourceRoofSliceProductMap_rightFibration X Y q b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex _ v

end SerrePositivity.EInfinity.SimplicialLocalization
