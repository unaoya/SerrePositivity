module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFBoundary
public import SerrePositivity.KST.SConstruction.SpectrumPositiveComponentEquality

/-!
概要：同じ D-9 native 四角形の四辺で、元 BF 正段と Ex∞ 境界商を比較する。
方針：元の置換射影の自然性と、SOA・Ex∞ 比較の基点固定自然性を合成する。
規約：有限四辺に限定し、全 Sp 二胞体の構成とは区別する。
使われ方：元 BF 四辺に固定した各正段の全図式比較の境界データ。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open LocalizingInvariants Fibration NonConnective Spectra PointedMapping
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ未完備 native 実四角形の底・右・左・上の四完全射。
方針：同じ列の二射と同じ標準零射を保持する。
規約：新しい四辺を選ばない。使われ方：有限四辺の比較を同時に型付けする。 -/
def dgKappaNativeBFNativeArrow : Fin 4 → Arrow _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} :=
  ![Arrow.mk (dgKappaNativeVerdierDiagram.{u, v} R D I).inclusion,
    Arrow.mk (dgKappaNativeVerdierDiagram.{u, v} R D I).projection,
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (dgKappaNativeVerdierDiagram.{u, v} R D I).left),
    Arrow.mk (fromZeroCategory (dgKappaNativeVerdierDiagram.{u, v} R D I).right)]

/-- 概要：元の四辺の BF 正段と Ex∞ 境界商は同じ指定前向き比較で可換する。
方針：置換射影の保存された成分と、同じ SOA・Ex∞ 比較の自然性を合成する。
規約：各正段の基点固定の成分の等号。使われ方：同じ実比較ホモトピーの構成。 -/
lemma dgKappaNativeBFArrowProjection_component (e : Fin 4) (r : ℕ) :
    let N := dgKappaNativeBFNativeArrow.{u, v} R D I e
    let f := sInputExactMap N.hom
    let X := stableBoundaryPointedObject r N.left
    let Y := stableBoundaryPointedObject r N.right
    let b : X ⟶ Y := boundaryReducedRealizationMap r f
    componentOf ((kSpectrumMap f).app (r + 1) ≫
      (monicKKanSequenceProjection (sInputModel N.right)).app (r + 1) ≫
        pointedSOAExInfinityComparison Y) =
      componentOf ((monicKKanSequenceProjection (sInputModel N.left)).app (r + 1) ≫
        pointedSOAExInfinityComparison X ≫ (exInfinityPointedKanMap b).hom) := by
  let N := dgKappaNativeBFNativeArrow.{u, v} R D I e
  let f := sInputExactMap N.hom
  let X := stableBoundaryPointedObject r N.left
  let Y := stableBoundaryPointedObject r N.right
  let b : X ⟶ Y := boundaryReducedRealizationMap r f
  change componentOf ((monicKKanSequenceMap f).app (r + 1) ≫
    (monicKKanSequenceProjection (sInputModel N.right)).app (r + 1) ≫
      pointedSOAExInfinityComparison Y) =
    componentOf ((monicKKanSequenceProjection (sInputModel N.left)).app (r + 1) ≫
      pointedSOAExInfinityComparison X ≫ (exInfinityPointedKanMap b).hom)
  have h₁ := componentOf_comp_right
    (monicKKanSequenceMap_projection_component f (r + 1))
    (pointedSOAExInfinityComparison Y)
  have h₂ := componentOf_comp_left
    (pointedSOAExInfinityComparison_naturality_component b).symm
    ((monicKKanSequenceProjection (sInputModel N.left)).app (r + 1))
  have ha := congrArg componentOf (Category.assoc
    ((monicKKanSequenceMap f).app (r + 1))
    ((monicKKanSequenceProjection (sInputModel N.right)).app (r + 1))
    (pointedSOAExInfinityComparison Y))
  exact ha.symm.trans (h₁.trans h₂)

/-- 概要：同じ正段射影比較を持つ新 BF 辺は旧辺と全整数群で一致する。
方針：Ex∞ 比較と単射置換射影の弱同値で正段成分を反映する。
規約：辺の構成とは別の比較補題。与えられた辺の比較を回収する。
使われ方：同時構成した有限四辺を K-B と K-cof の旧整数群へ接続する。 -/
lemma dgKappaNativeBFArrow_homotopyMap_eq (e : Fin 4)
    (g : kOmegaSpectrum (sInputModel
        (dgKappaNativeBFNativeArrow.{u, v} R D I e).left) ⟶
      kOmegaSpectrum (sInputModel (dgKappaNativeBFNativeArrow.{u, v} R D I e).right))
    (h : ∀ r : ℕ,
      let N := dgKappaNativeBFNativeArrow.{u, v} R D I e
      let X := stableBoundaryPointedObject r N.left
      let Y := stableBoundaryPointedObject r N.right
      let b : X ⟶ Y := boundaryReducedRealizationMap r (sInputExactMap N.hom)
      componentOf (g.app (r + 1) ≫
        (monicKKanSequenceProjection (sInputModel N.right)).app (r + 1) ≫
          pointedSOAExInfinityComparison Y) =
        componentOf ((monicKKanSequenceProjection (sInputModel N.left)).app (r + 1) ≫
          pointedSOAExInfinityComparison X ≫ (exInfinityPointedKanMap b).hom)) (j : ℤ) :
    OmegaSpectrum.homotopyMap g j = OmegaSpectrum.homotopyMap
      (kSpectrumMap (sInputExactMap (dgKappaNativeBFNativeArrow.{u, v} R D I e).hom)) j := by
  apply spectrumHomotopyMap_eq_of_positive_component
  intro r
  let N := dgKappaNativeBFNativeArrow.{u, v} R D I e
  apply pointedComponent_cancel_right_of_piIsomorphism
    ((monicKKanSequenceProjection (sInputModel N.right)).app (r + 1))
    (monicKKanSequenceProjection_piIsomorphism (sInputModel N.right) (r + 1))
  apply pointedComponent_cancel_right_of_piIsomorphism
    (pointedSOAExInfinityComparison (stableBoundaryPointedObject r N.right))
    (pointedSOAExInfinityComparison_piIsomorphism (stableBoundaryPointedObject r N.right))
  let p := (monicKKanSequenceProjection (sInputModel N.right)).app (r + 1)
  let c := pointedSOAExInfinityComparison (stableBoundaryPointedObject r N.right)
  let f := kSpectrumMap (sInputExactMap N.hom)
  have ha := congrArg componentOf (Category.assoc (g.app (r + 1)) p c)
  have hb := congrArg componentOf (Category.assoc (f.app (r + 1)) p c)
  exact ha.trans (((h r).trans
    (dgKappaNativeBFArrowProjection_component.{u, v} R D I e r).symm).trans hb.symm)

end SerrePositivity.KST.SConstruction
