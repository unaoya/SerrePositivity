module
public import SerrePositivity.KST.Fibration.KanClosedEvaluation
public import SerrePositivity.KST.Fibration.StableBoundaryQuotientTransformation
public import SerrePositivity.KST.Fibration.DGNuSBoundaryInfinity
public import SerrePositivity.KST.Fibration.CoreEnrichedPrecompose
public import SerrePositivity.KST.SConstruction.ReducedMultiRealization
public import SerrePositivity.KST.Comparison.ExInfinityLocalization
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.F1.KanEnrichedComparisonIso

/-! # 元の反復実現と境界商の Ex∞ 比較を、同じ全 coherent 図式へ適用する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の正反復実現を、全 Hom を保って同じ Ex∞ Kan 値へ送る。 -/
def stableMultiKanEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} StableQCat.{u} KanObject.{u} :=
  (stableMultiRealizationEnrichedFunctor (r + 1)).comp SSet exInfinityClosedKanEnrichedFunctor

/-- 元の境界商の基点を忘れ、同じ Ex∞ Kan 値と全 Hom を保持する。 -/
def stableBoundaryClosedKanEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} StableQCat.{u} KanObject.{u} :=
  (stableBoundaryClosedEnrichedFunctor r).comp SSet exInfinityClosedKanEnrichedFunctor

/-- 元の全境界商の自然変換を、同じ Ex∞ の全 Hom 作用で写す。 -/
def stableBoundaryQuotientKanTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (stableMultiKanEnrichedFunctor r) (stableBoundaryClosedKanEnrichedFunctor r) :=
  strictSimplicialTransformationPostcompose _ _ exInfinityClosedKanEnrichedFunctor
    (stableBoundaryQuotientTransformation r)

/-- Ex∞ 後の比較成分は、元の同じ境界商射の Ex∞ 像である。 -/
theorem stableBoundaryQuotientKanTransformation_app (r : ℕ) (C : StableQCat.{u}) :
    (stableBoundaryQuotientKanTransformation r).app C =
      eHomEquiv SSet (show (stableMultiKanEnrichedFunctor r).obj C ⟶
        (stableBoundaryClosedKanEnrichedFunctor r).obj C from
          exInfinity.map (boundaryReductionQuotient r (stableCategoryModel C))) :=
  exInfinityClosedKanEnrichedFunctor_hom
    (boundaryReductionQuotient r (stableCategoryModel C))

/-- 元の全比較の同じ区間族。対象ごとの比較だけから自然性を推論しない。 -/
def stableBoundaryQuotientKanHomotopy (r : ℕ) :
    SSet.Homotopy (coherentNerveMap (stableMultiKanEnrichedFunctor r))
      (coherentNerveMap (stableBoundaryClosedKanEnrichedFunctor r)) :=
  Spectra.StrictEnrichedTransformation.homotopy _ _ (stableBoundaryQuotientKanTransformation r)

/-- 元の全比較を各頂点で評価すると、同じ Ex∞ 商射の辺になる。 -/
theorem stableBoundaryQuotientKanHomotopy_component (r : ℕ) (C : StableQCat.{u}) :
    (simplicialHomotopyVertexEdge (stableBoundaryQuotientKanHomotopy r)
      (coherentNerveVertex C)).edge =
      (coherentNerveEdge (show (stableMultiKanEnrichedFunctor r).obj C ⟶
        (stableBoundaryClosedKanEnrichedFunctor r).obj C from
          exInfinity.map (boundaryReductionQuotient r (stableCategoryModel C)))).edge := by
  rw [stableBoundaryQuotientKanHomotopy, Spectra.StrictEnrichedTransformation.homotopy_component]
  rw [strictSimplicialTransformation_componentHom _ _ _ C _
    (stableBoundaryQuotientKanTransformation_app r C)]

/-- 同じ元の Ex∞ 境界商射は Kan 複体間の実ホモトピー同値である。 -/
theorem stableBoundaryQuotientKan_isHomotopyEquivalence (r : ℕ) (C : StableQCat.{u}) :
    IsSimplicialHomotopyEquivalence
      (exInfinity.map (boundaryReductionQuotient r (stableCategoryModel C))) := by
  have hq := boundaryReductionQuotient_image_isIso AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) r (stableCategoryModel C)
  have hp := kanPiIsomorphism_of_localized_isIso
    (exInfinity.map (boundaryReductionQuotient r (stableCategoryModel C)))
    ((exInfinity_map_localized_isIso_iff _).mpr hq)
  let x : (multiDiagonalCoreSConstruction (r + 1) (stableCategoryModel C)) _⦋0⦌ :=
    Classical.choice
      (multiDiagonalDiagram_zero_isContractibleKan r (stableCategoryModel C)).nonempty
  exact homotopyEquivalence_of_kanPiIsomorphism_of_vertex _ hp
    ((exInfinityUnit.app _).app (Opposite.op ⦋0⦌) x)

/-- 同じ元の商射を全成分に持つ、関手 ∞ 圏内の自然同型。 -/
def stableBoundaryQuotientKanIso (r : ℕ) :
    FunctorIso (coherentNerveMap (stableMultiKanEnrichedFunctor r))
      (coherentNerveMap (stableBoundaryClosedKanEnrichedFunctor r)) :=
  functorIsoOfPointwiseInvertibleHomotopy (stableBoundaryQuotientKanHomotopy r) (by
    intro c
    obtain ⟨C, rfl⟩ := (coherentNerveVertexEquiv StableQCat.{u}).surjective c
    apply (isInvertibleEdge_congr (stableBoundaryQuotientKanHomotopy_component r C)).mpr
    exact coherentKanEdge_isInvertible_of_isQCatEquivalence
      (stableBoundaryQuotientKan_isHomotopyEquivalence r C).isQCatEquivalence)

/-- 基点忘却後の境界商 Kan 関手は、同じ元の全閉 Hom 関手と厳密に一致する。 -/
theorem stableSBoundaryKan_forget (r : ℕ) :
    (stableSBoundaryKanEnrichedFunctor r).comp SSet pointedKanForgetEnriched =
      stableBoundaryClosedKanEnrichedFunctor r := by
  rw [stableSBoundaryKanEnrichedFunctor, enrichedFunctor_comp_assoc,
    exInfinityPointedKan_forget, ← enrichedFunctor_comp_assoc]
  rfl

/-- 同じ元の S• 境界商を忘却した ∞ 関手と、元の全正反復実現の比較。 -/
def stableMultiBoundaryForgetIso (r : ℕ) :
    FunctorIso (coherentNerveMap (stableMultiKanEnrichedFunctor r))
      (stableSBoundaryKanInfinityFunctor r ≫ coherentNerveMap pointedKanForgetEnriched) := by
  have he : stableSBoundaryKanInfinityFunctor r ≫ coherentNerveMap pointedKanForgetEnriched =
      coherentNerveMap (stableBoundaryClosedKanEnrichedFunctor r) := by
    rw [stableSBoundaryKanInfinityFunctor, ← coherentNerveMap_comp, stableSBoundaryKan_forget]
  rw [he]
  exact stableBoundaryQuotientKanIso r

/-- 元の Verdier 四角形全体を保つ、反復実現と境界商の基点忘却の比較。 -/
def verdierMultiBoundaryForgetSquareIso (r : ℕ) (d : VerdierDiagram.{u}) :
    FunctorIso (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor r))
      (d.square ≫ stableSBoundaryKanInfinityFunctor r ≫
        coherentNerveMap pointedKanForgetEnriched) :=
  (stableMultiBoundaryForgetIso r).precomp d.square

/-- 元の全反復実現四角形と、同じ境界商を基点忘却した四角形の引き戻し性は同値。 -/
theorem verdierMultiBoundaryForget_isPullback_iff (r : ℕ) (d : VerdierDiagram.{u}) :
    IsPullbackSquare (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor r)) ↔
      IsPullbackSquare (d.square ≫ stableSBoundaryKanInfinityFunctor r ≫
        coherentNerveMap pointedKanForgetEnriched) :=
  ⟨fun h => h.of_functorIso (verdierMultiBoundaryForgetSquareIso r d),
    fun h => h.of_functorIso (verdierMultiBoundaryForgetSquareIso r d).symm⟩

end SerrePositivity.KST.Fibration
