module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantFramePinchedWeak

/-!
概要：元の bifibrant source frame の弱比較を同じ二列 graph の実射として露出する。
方針：元の全 Hom 同型、二列比較、AsSmall 全語同型を同じ順序で読む。
規約：元の全単体・両端点・元の余極限標準射を保持する。
使われ方：実 comma augmentation roof と同じ弱基準族の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra Hammock
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.FrameHom
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

/-- 概要：元の全 Hom 単体を同じ balanced 二列 graph に送る。
方針：元の Hom の包みと元の二列比較を同じ up の graph 同型で送る。
規約：元の全単体と元の左脚。使われ方：同じ comma roof の回収。 -/
def modelBifibrantSourceFrameGraphMap :
    nerve (modelBifibrantSourceFrameElementCategory X Y q) ⟶
      graph (modelBifibrantRelativeCategory C).weakEquivalences LeftRoof.word
        (modelBifibrantObject C X) (modelBifibrantObject C Y) :=
  (modelBifibrantSourceFrameIndexIso X Y q).hom ≫
    frameLeftRoofNerveMap modelRawBifibrantWeak (modelBifibrantFrame X q)
      (modelBifibrantFrameAugmentation X q) (fun n => q.augmentation_weakEquivalence n)
      (fun f => q.homotopicallyConstant f) ≫
        (AsSmallComparison.graphIso (modelRawBifibrantWeak (C := C)) X Y LeftRoof.word).hom

/-- 概要：同じ元の二列 graph の標準射は元の弱な全 hammock 比較を回収する。
方針：同じ AsSmall 全語同型と各語の標準射の自然性を使う。
規約：実射の厳密な因子分解。使われ方：元の augmentation roof の全族照合。 -/
lemma modelBifibrantSourceFrameGraphMap_colimit :
    modelBifibrantSourceFrameGraphMap X Y q ≫
      graphInclusion (modelBifibrantRelativeCategory C).weakEquivalences
        (modelBifibrantObject C X) (modelBifibrantObject C Y) LeftRoof.word =
          modelBifibrantSourceFrameColimitMap X Y q := by
  unfold modelBifibrantSourceFrameGraphMap modelBifibrantSourceFrameColimitMap
    modelBifibrantSourceFrameRawColimitMap modelBifibrantFrameLeftRoofColimitMap
    frameLeftRoofColimitMap
  simp only [Category.assoc]
  rw [AsSmallComparison.graphInclusion_colimitIso]
  rfl

end SerrePositivity.EInfinity.SimplicialLocalization
