module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFStages
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquareFrameEdges

/-!
概要：同じ未完備 D-9 実列に対する、元 BF 四辺の指定境界。
方針：同じ三つの native 安定圏と標準零圏の kSpectrumMap を使用する。
規約：四辺の構成を全二胞体の構成と取り違えない。
使われ方：一つの native 四角形の有限 BF 持ち上げに固定する境界。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open LocalizingInvariants Fibration NonConnective Spectra
open scoped Simplicial
local instance nativeBFBoundarySpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：元の未完備実列の四つの kSpectrumMap を持つ同じ BF 境界。
方針：包含・商・元左零射・元右零射を同じ coherent 辺にする。
規約：四頂点の整合性も含む境界。使われ方：有限 BF 四角形で固定する全四辺。 -/
def dgKappaNativeBFBoundary : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame Sp.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.squareFrameOfEdges
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kSpectrumMap
      (sInputExactMap (dgKappaNativeKernelInclusion.{u, v} R D I))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kSpectrumMap
      (sInputExactMap (fromZeroCategory (dgKappaNativeSuspensionCategory.{u, v} R D I)))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kSpectrumMap
      (sInputExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (dgKappaNativeKernelCategory.{u, v} R D I)))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kSpectrumMap
      (sInputExactMap (dgKappaNativeQuotient.{u, v} R D I))))

/-- 概要：指定境界の底辺は同じ元の未完備包含の BF 辺。
方針：境界の定義から回収する。
規約：全一単体を保持する。使われ方：要求された底辺等号の接続。 -/
lemma dgKappaNativeBFBoundary_bottom :
    (dgKappaNativeBFBoundary.{u, v} R D I).bottom = SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kSpectrumMap
        (sInputExactMap (dgKappaNativeVerdierDiagram.{u, v} R D I).inclusion))).edge := rfl

/-- 概要：指定境界の右辺は同じ元の未完備実商の BF 辺。
方針：境界の定義から回収する。
規約：全一単体を保持する。使われ方：要求された商辺等号の接続。 -/
lemma dgKappaNativeBFBoundary_right :
    (dgKappaNativeBFBoundary.{u, v} R D I).right = SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kSpectrumMap
        (sInputExactMap (dgKappaNativeVerdierDiagram.{u, v} R D I).projection))).edge := rfl

/-- 概要：指定境界の左辺は同じ元の未完備始域の零射の BF 辺。
方針：境界の定義から回収する。
規約：全一単体を保持する。使われ方：要求された左零射の等号の接続。 -/
lemma dgKappaNativeBFBoundary_left :
    (dgKappaNativeBFBoundary.{u, v} R D I).left = SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kSpectrumMap (sInputExactMap
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (dgKappaNativeVerdierDiagram.{u, v} R D I).left)))).edge := rfl

/-- 概要：指定境界の上辺は同じ元の未完備終域の零射の BF 辺。
方針：境界の定義から回収する。
規約：全一単体を保持する。使われ方：要求された右零射の等号の接続。 -/
lemma dgKappaNativeBFBoundary_top :
    (dgKappaNativeBFBoundary.{u, v} R D I).top = SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kSpectrumMap (sInputExactMap
        (fromZeroCategory (dgKappaNativeVerdierDiagram.{u, v} R D I).right)))).edge := rfl

end SerrePositivity.KST.SConstruction
