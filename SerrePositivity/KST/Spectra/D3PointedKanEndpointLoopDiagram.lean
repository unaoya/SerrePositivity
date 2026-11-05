module

public import SerrePositivity.KST.Spectra.D3StrictPullbackSquare

/-!
概要：同じ実端点パラメータ全四角形族を、点つき Kan の全 loop 図式族として認証する。
方針：二三角形を元の通常引き戻し錐の同じ合成射列と比較し、全四角形へ極限性を移す。
規約：構成済みの全 Hom 作用と全単体を変えず、実零角と実引き戻し性を加える。
使われ方：d3 の実段 loop 図式始点と通常点つき loop 関手の全自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3EndpointLoopSquareCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)

/-- 同じ通常端点パラメータ図式の実下三角形。 -/
lemma d3EndpointOrdinarySquare_triangle_left (Y : PointedKanObject.{u}) :
    squareTriangle 1 ≫
      (d3ParameterOrdinarySquare d3EndpointParameter Y ≫ nerveToCoherent PointedKanObject) =
        SSet.yonedaEquiv.symm ((nerveToCoherent PointedKanObject).app (Opposite.op ⦋2⦌)
          (ComposableArrows.mk₂ (d3PointedKanCofiberOrdinaryCone _root_.SerrePositivity.InfinityCategories.F1.Pointed.intervalEndpoint Y).fst
            (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.F1.Pointed.PointedMapping.prePointed _root_.SerrePositivity.InfinityCategories.F1.Pointed.intervalEndpoint Y.obj) :
              (d3PointedKanIhom _root_.SerrePositivity.InfinityCategories.F1.Pointed.pointedInterval).obj Y ⟶
                (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).obj Y))) := by
  apply SSet.yonedaEquiv.injective
  rw [← Category.assoc, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply congrArg ((nerveToCoherent PointedKanObject).app _)
  rw [squareTriangle, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 同じ通常端点パラメータ図式の実上三角形。 -/
lemma d3EndpointOrdinarySquare_triangle_right (Y : PointedKanObject.{u}) :
    squareTriangle 0 ≫
      (d3ParameterOrdinarySquare d3EndpointParameter Y ≫ nerveToCoherent PointedKanObject) =
        SSet.yonedaEquiv.symm ((nerveToCoherent PointedKanObject).app (Opposite.op ⦋2⦌)
          (ComposableArrows.mk₂ (d3PointedKanCofiberOrdinaryCone _root_.SerrePositivity.InfinityCategories.F1.Pointed.intervalEndpoint Y).snd
            (ObjectProperty.homMk
              (_root_.SerrePositivity.InfinityCategories.F1.Pointed.PointedMapping.prePointed (PointedObject.toPoint
                (𝟙_ PointedSimplicialSet.{u})) Y.obj) :
              (d3PointedKanIhom PointedObject.point).obj Y ⟶
                (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).obj Y))) := by
  apply SSet.yonedaEquiv.injective
  rw [← Category.assoc, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply congrArg ((nerveToCoherent PointedKanObject).app _)
  rw [squareTriangle, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 構成済み全族の各実四角形は、元の cofiber 錐の同じ coherent 四角形そのもの。 -/
lemma d3EndpointParameterSquare_eq_strict (Y : PointedKanObject.{u}) :
    squareDiagram (d3EndpointParameterSquare.app _ (coherentNerveVertex Y)) =
      D3StrictPullbackSquare.square (d3PointedKanCofiberOrdinaryCone _root_.SerrePositivity.InfinityCategories.F1.Pointed.intervalEndpoint Y) := by
  rw [d3EndpointParameterSquare, d3PointedKanParameterSquare_vertex]
  apply square_isPushout.hom_ext
  · rw [d3EndpointOrdinarySquare_triangle_right, D3StrictPullbackSquare.triangle_right]
  · rw [d3EndpointOrdinarySquare_triangle_left, D3StrictPullbackSquare.triangle_left]

/-- 同じ実端点パラメータ全族の四角形は、実際の ∞ 引き戻し。 -/
lemma d3EndpointParameterSquare_isPullback (Y : PointedKanObject.{u}) :
    IsPullbackSquare (squareDiagram
      (d3EndpointParameterSquare.app _ (coherentNerveVertex Y))) := by
  rw [d3EndpointParameterSquare_eq_strict]
  exact D3StrictPullbackSquare.isPullback _ (d3PointedKanEndpointCone_isLimit Y)

/-- 同じ構成済み全族に、実 loop 図式としての全頂点認証を与える。 -/
lemma d3EndpointParameterSquare_isLoop (v : PointedKanInfinity.{u} _⦋0⦌) :
    IsLoopDiagramVertex (d3EndpointParameterSquare.app _ v) := by
  obtain ⟨Y, rfl⟩ := (coherentNerveVertexEquiv PointedKanObject.{u}).surjective v
  exact ⟨d3EndpointParameterSquare_zero_corner Y,
    d3EndpointParameterSquare_other_zero Y, d3EndpointParameterSquare_isPullback Y⟩

/-- 元の全 Hom・全単体を保つ、実端点パラメータの全 loop 図式族。 -/
def d3PointedKanEndpointLoopDiagram : PointedKanInfinity.{u} ⟶ loopDiagrams PointedKanInfinity :=
  fullSubcomplexLift IsLoopDiagramVertex d3EndpointParameterSquare d3EndpointParameterSquare_isLoop


/-- 実 loop 図式族の四角の全関手は、元のパラメータ作用そのもの。 -/
lemma d3PointedKanEndpointLoopDiagram_corner (i j : Fin 2) :
    d3PointedKanEndpointLoopDiagram.{u} ≫ loopDiagramEvaluation PointedKanInfinity i j =
      coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj (i, j))) := by
  dsimp only [loopDiagramEvaluation, d3PointedKanEndpointLoopDiagram]
  rw [← Category.assoc, fullSubcomplexLift_ι]
  exact d3PointedKanParameterSquare_corner d3EndpointParameter i j

/-- 通常の点つき loop は、同じ実全図式族の始点作用に全関手同型。 -/
def d3PointedKanEndpointLoopDiagram_sourceIso :
    FunctorIso pointedKanLoopInfinity.{u}
      (d3PointedKanEndpointLoopDiagram ≫ loopDiagramEvaluation PointedKanInfinity 0 0) := by
  rw [d3PointedKanEndpointLoopDiagram_corner]
  exact d3PointedKanEndpointLoopIso

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
