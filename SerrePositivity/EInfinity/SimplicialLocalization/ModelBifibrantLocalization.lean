module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantFrameRightKanCofinality
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantRightKanReduction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

/-!
概要：一般モデル圏の bifibrant hammock 自身の局所化普遍性。
方針：元の native roof の余終性を三つの right Kan 判定入力へ代入する。
規約：第一の関手的分解と指定 right frame を使い、SSet モデルは仮定しない。
使われ方：cofibrant 部分圏・全圏への変形と指定局所化との coherent 比較。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：元の第一分解から同じ全対象の source frame を選ぶ。
方針：既存の関手的 Reedy 解像を使う。
規約：第一分解以外の存在入力なし。使われ方：実 right Kan 判定。 -/
def modelSourceFrameFamily : CofibrantResolutionFamily (C := C) simplex :=
  cosimplicialResolutionFamily (MorphismProperty.functorialFactorizationData _ _)

include r in
/-- 概要：実次数比較の余終性を入力条件なしで回収する。
方針：同じ native roof の全三角形を実比較へ代入する。
規約：指定 right frame と同じ source frame。使われ方：局所化普遍性。 -/
lemma modelBifibrantFrameRightKanMap_cofinal (X : BifibrantObject C) :
    IsLeftCofinal (modelBifibrantFrameRightKanMap X
      ((modelSourceFrameFamily (C := C)).atObject X.obj)) :=
  modelBifibrantFrameRightKanMap_isLeftCofinal X _ r

include r in
/-- 概要：同じ hammock 局所化の恒等延長は実 right Kan 延長。
方針：証明済みの全次数比較の余終性を標準錐へ代入する。
規約：未証明の余終性入力なし。使われ方：前合成の充満忠実性。 -/
lemma modelBifibrantSourceRightKanExtension_refl
    {E : SSet.{max u v}} [Quasicategory E]
    (G : kanHammockNerve (modelBifibrantRelativeCategory C) ⟶ E) :
    IsRightKanExtension (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G) G
      (functorHomotopyRefl
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G)) :=
  modelBifibrantSourceRightKanExtension_refl_of_frameCofinality
    (fun X => (modelSourceFrameFamily (C := C)).atObject X.obj)
    (fun X => modelBifibrantFrameRightKanMap_cofinal r X) G

include r in
/-- 概要：反転関手の同じ全 right Kan 図式は実極限を持つ。
方針：元の全 frame の極限を証明済みの余終な次数比較で移す。
規約：全頂点と全標的関手。使われ方：局所化の局所極限判定。 -/
lemma modelBifibrantSourceRightKanDiagram_hasLimit_all
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C)))
    (z : (kanHammockNerve (modelBifibrantRelativeCategory C)) _⦋0⦌) :
    HasLimit (rightKanDiagram (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      F z) :=
  modelBifibrantSourceRightKanDiagram_hasLimit_all_of_frameCofinality
    (fun X => (modelSourceFrameFamily (C := C)).atObject X.obj)
    (fun X => modelBifibrantFrameRightKanMap_cofinal r X) F hF z

include r in
/-- 概要：同じ実 right Kan 延長の単位の全成分は可逆。
方針：証明済みの余終性を元の錐脚と augmentation に適用する。
規約：指定単位の全成分。使われ方：同じ局所化の普遍性。 -/
lemma modelBifibrantSourceRightKanUnit_isInvertible
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C)))
    (G : kanHammockNerve (modelBifibrantRelativeCategory C) ⟶ E)
    (α : SSet.Homotopy
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G) F)
    (hα : IsRightKanExtension (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      F G α) (z : (nerve (modelBifibrantRelativeCategory C).category) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge α z).toTruncated :=
  modelBifibrantSourceRightKanUnit_isInvertible_of_frameCofinality
    (fun X => (modelSourceFrameFamily (C := C)).atObject X.obj)
    (fun X => modelBifibrantFrameRightKanMap_cofinal r X) F hF G α hα z

include r in
/-- 概要：一般モデルの bifibrant hammock は指定弱同値による ∞ 局所化。
方針：実余終性を証明した三つの right Kan 入力を一般判定へ代入する。
規約：第一分解と指定 right frame だけを追加する。
使われ方：指定局所化への全写像空間比較と全圏への変形。 -/
lemma modelBifibrantHammock_isLocalization :
    IsLocalization (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (weakNerveEdges (modelBifibrantRelativeCategory C)) :=
  modelBifibrantHammock_isLocalization_of_frameCofinality
    (fun X => (modelSourceFrameFamily (C := C)).atObject X.obj)
    (fun X => modelBifibrantFrameRightKanMap_cofinal r X)

end SerrePositivity.EInfinity.SimplicialLocalization
