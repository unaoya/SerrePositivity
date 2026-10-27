module
public import SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof

/-!
概要：固定 ν の実長方形を、明示された右面・外周・全長方形の三認証で消費する。
方針：同じ実二面で貼合せを消去し、指定全比較の同じ成分で元始域を回収する。
規約：三認証の存在を主張しない。Perf 商辺は完備化付き列のまま保持する。
使われ方：Sp-3 の K-S• ③ 到着時の代入口。厳密像版は独立の特殊化。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Spectra.S3
variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}

/-- 三認証を明示引数として受ける主結論。全長方形の比較は上下二単体も保持する。 -/
theorem actualFaces_isPullback
    (G : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : PerfectVerdierDiagram.{u})
    (br : VerdierSquareBoundaryIso r.square (verdierRectangleFace 0 ≫ G ≫ ν))
    (bo : VerdierSquareBoundaryIso o.square (verdierRectangleFace 1 ≫ G ≫ ν))
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u}}
    (b : VerdierRectangleBoundaryIso (G ≫ ν) F)
    (er : VerdierSquareDiagramIso r.square (verdierRectangleFace 0 ≫ G ≫ ν) br)
    (eo : VerdierSquareDiagramIso o.square (verdierRectangleFace 1 ≫ G ≫ ν) bo)
    (e : VerdierRectangleDiagramIso (G ≫ ν) F b)
    {E : perfectStableInfinity.{u} ⟶ Sp.{u}} (hE : IsPerfectLocalizingInvariant E) :
    IsPullbackSquare (((β_ _ _).hom ≫ pastingSquare G 2) ≫ ν ≫ E) ∧
      IsPullbackSquare (((β_ _ _).hom ≫ pastingSquare F 2) ≫ E) :=
  ⟨RelativePerfectVerdierRectangle.comparison_isPullback_of_actualFaces
      G r o hE br er bo eo,
    RelativePerfectVerdierRectangle.comparison_isPullback_of_actualFaces_imageIso
      G r o hE br er bo eo b e⟩

/-- 始域は元入力への増大屋根で回収し、S 内の頂点等号を要求しない。 -/
def actualSourceValueIso
    {G : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u}}
    (b : VerdierRectangleBoundaryIso (G ≫ ν) F)
    (e : VerdierRectangleDiagramIso (G ≫ ν) F b)
    {original : S _⦋0⦌}
    (roof : RelativePerfectVerdierSourceRoof ν original
      (squareVertex ((β_ _ _).hom ≫ pastingSquare G 2) 0 0))
    (E : perfectStableInfinity.{u} ⟶ Sp.{u}) :
    VertexIso ((ν ≫ E).app _ original)
      (squareVertex (((β_ _ _).hom ≫ pastingSquare F 2) ≫ E) 0 0) :=
  RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso b e roof E

/-- 始域回収は全比較の同じ成分を使い、元の増大・核比較との可換式を保つ。 -/
theorem actualSourceValueIso_triangle
    {G : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u}}
    (b : VerdierRectangleBoundaryIso (G ≫ ν) F)
    (e : VerdierRectangleDiagramIso (G ≫ ν) F b)
    {original : S _⦋0⦌}
    (roof : RelativePerfectVerdierSourceRoof ν original
      (squareVertex ((β_ _ _).hom ≫ pastingSquare G 2) 0 0))
    (E : perfectStableInfinity.{u} ⟶ Sp.{u}) :
    (hoFunctor.map E).toFunctor.map ((hoFunctor.map ν).toFunctor.map
      (Truncated.HomotopyCategory.homMk roof.augmentation)) ≫
        (actualSourceValueIso b e roof E).hom =
    (hoFunctor.map E).toFunctor.map ((hoFunctor.map ν).toFunctor.map
      (Truncated.HomotopyCategory.homMk roof.comparison)) ≫
        (((e.comparison.precomp ((β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
          (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})))).postcomp E).toNatIso.app
            (HomotopyCategory.mk
              (squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u + 1})) 0 0))).hom :=
  RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso_triangle b e roof E

/-- 厳密な ν 像の二面認証を ofActualFaces に代入する特殊化。 -/
def rectangleOfSquare (G : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : PerfectVerdierSequence.{u})
    (hrb : squareBottomEdge ≫ (verdierRectangleFace 0 ≫ G) ≫ ν =
      SSet.yonedaEquiv.symm
        (perfectStableArrow r.verdier.inclusion r.left_complete r.middle_complete).edge)
    (hrr : squareRightEdge ≫ (verdierRectangleFace 0 ≫ G) ≫ ν =
      SSet.yonedaEquiv.symm
        (perfectStableArrow r.projection r.middle_complete r.right_complete).edge)
    (hrz : IsZeroCategory (perfectStableObject
      (squareVertex ((verdierRectangleFace 0 ≫ G) ≫ ν) 0 1)))
    (hob : squareBottomEdge ≫ (verdierRectangleFace 1 ≫ G) ≫ ν =
      SSet.yonedaEquiv.symm
        (perfectStableArrow o.verdier.inclusion o.left_complete o.middle_complete).edge)
    (hor : squareRightEdge ≫ (verdierRectangleFace 1 ≫ G) ≫ ν =
      SSet.yonedaEquiv.symm
        (perfectStableArrow o.projection o.middle_complete o.right_complete).edge)
    (hoz : IsZeroCategory (perfectStableObject
      (squareVertex ((verdierRectangleFace 1 ≫ G) ≫ ν) 0 1))) :
    RelativePerfectVerdierRectangle ν :=
  RelativePerfectVerdierRectangle.ofActualFaces G
    (RelativePerfectVerdierDiagram.ofSquare ν r _ hrb hrr hrz)
    (RelativePerfectVerdierDiagram.ofSquare ν o _ hob hor hoz) rfl rfl

/-- StableInfinity 側の辺の厳密照合からも、同じ S 長方形の証明書を得る。 -/
def rectangleOfStableSquare (G : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : PerfectVerdierSequence.{u})
    (hrb : squareBottomEdge ≫ (verdierRectangleFace 0 ≫ G) ≫ ν ≫
      perfectStableInfinityInclusion = SSet.yonedaEquiv.symm (stableArrow r.verdier.inclusion).edge)
    (hrr : squareRightEdge ≫ (verdierRectangleFace 0 ≫ G) ≫ ν ≫
      perfectStableInfinityInclusion = SSet.yonedaEquiv.symm (stableArrow r.projection).edge)
    (hrz : IsZeroCategory (perfectStableObject
      (squareVertex ((verdierRectangleFace 0 ≫ G) ≫ ν) 0 1)))
    (hob : squareBottomEdge ≫ (verdierRectangleFace 1 ≫ G) ≫ ν ≫
      perfectStableInfinityInclusion = SSet.yonedaEquiv.symm (stableArrow o.verdier.inclusion).edge)
    (hor : squareRightEdge ≫ (verdierRectangleFace 1 ≫ G) ≫ ν ≫
      perfectStableInfinityInclusion = SSet.yonedaEquiv.symm (stableArrow o.projection).edge)
    (hoz : IsZeroCategory (perfectStableObject
      (squareVertex ((verdierRectangleFace 1 ≫ G) ≫ ν) 0 1))) :
    RelativePerfectVerdierRectangle ν :=
  RelativePerfectVerdierRectangle.ofActualFaces G
    (RelativePerfectVerdierDiagram.ofStableSquare ν r _ hrb hrr hrz)
    (RelativePerfectVerdierDiagram.ofStableSquare ν o _ hob hor hoz) rfl rfl

end SerrePositivity.KST.Spectra.S3
