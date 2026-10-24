module
public import SerrePositivity.KST.Fibration.QuotientSKernelFullSquare
public import SerrePositivity.KST.Fibration.StrictConeTransformation

/-!
概要：同じ元の商核四角形と、全 S• 零角へ読み替えた全四角形を実関手同型で結ぶ。
方針：元の零角同型を cospan の通常同型と全錐の変換にし、同じ全 coherent 錐へ送る。
規約：四辺だけでなく元の全二胞体を運ぶ。指定 Verdier 側の比較は別工程として残す。
使われ方：K-6 c4 の商核側の全四角形輸送。元の核円柱の全 S• 座標を保つ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Comparison
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q)

/-- 元の零角同型と同じ cospan の二脚による、実 cospan 図式の通常同型。 -/
def quotientSKernelFullCospanIso :
    kanPullbackDiagram
        (exInfinityKanMap (simplicialDiagonalFunctor.map (coreSExactMap q)))
        (exInfinityKanMap (simplicialDiagonalFunctor.map
          (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q))) ≅
      kanPullbackDiagram
        (exInfinityKanMap (simplicialDiagonalFunctor.map (coreSExactMap q)))
        (exInfinityKanMap (simplicialDiagonalFunctor.map (zeroFunctorFullSMap
          (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
          (verdierSequenceComposite_zero h)))) :=
  CategoryTheory.Functor.isoWhiskerLeft AsSmall.down
    (cospanExt (Iso.refl _) (quotientSKernelCornerFullSKanIso h) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by
        simpa only [Iso.refl_hom, Category.comp_id] using quotientSKernelCornerFullSKanIso_top h))

set_option maxHeartbeats 800000 in
-- 同じ実 core S・全 S•・Ex∞ の対象座標を同時に照合する。
/-- 元の商核四角形の全二胞体を、同じ全 S• 零角の四角形へ運ぶ実関手同型。 -/
def quotientSKernelFullSquareIso :
    FunctorIso (quotientSKernelInfinitySquare i q) (quotientSKernelFullInfinitySquare h) := by
  let c := kanCommSqCone
    (P := stableCoreSingleKanObject (show StableQCat from A))
    (X := exInfinityClosedKanEnrichedFunctor.obj ⟨simplicialDiagonalFunctor.obj
      (relativeSimplicialSConstruction (i.hom ≫ q.hom))⟩)
    (Y := stableCoreSingleKanObject (show StableQCat from B))
    (Z := stableCoreSingleKanObject (show StableQCat from C))
    (exInfinity.map_commSq (quotientSKernelRealizationSquare i q))
  let d := kanCommSqCone
    (P := stableCoreSingleKanObject (show StableQCat from A))
    (X := fullSRealizationKanObject A)
    (Y := stableCoreSingleKanObject (show StableQCat from B))
    (Z := stableCoreSingleKanObject (show StableQCat from C))
    (exInfinity.map_commSq (quotientSKernelFullRealizationSquare h))
  let α := (quotientSKernelFullCospanIso h).hom
  have hf : ∀ j, (𝟙 c.pt) ≫ d.π.app j = c.π.app j ≫ α.app j := by
    intro j
    rcases j with ⟨_ | (_ | _)⟩
    · simp only [Category.id_comp, Category.comp_id]
      rfl
    · simp only [Category.id_comp, Category.comp_id]
      rfl
    · change (𝟙 _) ≫ exInfinity.map (coreSFullRealizationInclusion (show StableQCat from A)) =
        exInfinityKanMap (simplicialDiagonalFunctor.map
          (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom))) ≫
          (quotientSKernelCornerFullSKanIso h).hom
      rw [Category.id_comp]
      exact (quotientSKernelCornerFullSKanIso_left h).symm
  have hα : ∀ j, IsInvertibleEdge (coherentNerveEdge (α.app j)) := by
    intro j
    rcases j with ⟨_ | (_ | _)⟩
    · exact kanIdentityEdge_isInvertible _
    · exact kanIdentityEdge_isInvertible _
    · change IsInvertibleEdge (coherentNerveEdge (quotientSKernelCornerFullSKanIso h).hom)
      apply coherentKanEdge_isInvertible_of_isQCatEquivalence
      exact (qCatEquivalenceOfIso (exInfinity.mapIso
        (simplicialDiagonalFunctor.mapIso (relativeSKernelSimplicialIso h)))).isQCatEquivalence
  have he := strictCoherentConeTransformationIso α c d (𝟙 c.pt) hf hα
    (kanIdentityEdge_isInvertible _)
  exact he.precomp (cospanConeSquareIso.inv ≫
    joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv)

/-- 同じ元の商核四角形の引き戻し性は、全 S• 零角への全図式輸送で両方向に保たれる。 -/
theorem quotientSKernelFullInfinitySquare_isPullback_iff :
    IsPullbackSquare (quotientSKernelInfinitySquare i q) ↔
      IsPullbackSquare (quotientSKernelFullInfinitySquare h) :=
  ⟨fun hk => hk.of_functorIso (quotientSKernelFullSquareIso h),
    fun hk => hk.of_functorIso (quotientSKernelFullSquareIso h).symm⟩

end SerrePositivity.KST.Fibration
