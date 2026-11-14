module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientFlatKernel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientZeroingExtension
public import SerrePositivity.KST.LocalizingInvariants.DGKappaRelativeRoofTransport

/-!
概要：D-9 の同じ実小核を、Sp-6 の固定零化四角形から懸垂屋根へ接続する。
方針：native Verdier 列の零化から D 正本で指定収縮を選び、元の商包含を保持する。
規約：固定 ν の Verdier 証拠と零角の Perf 零性に条件付き。Perf・P 照合の存在は主張しない。
使われ方：K-7 c5 の kernel・diagram・quotient の具体化と、残る Perf 比較の切り分け。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ分解 cone 内の D-9 の実小核を、固定 dg 入力として保持する。 -/
def dgKappaResolvedKernelKInput : PerfDGInput.{u, max (u + 1) v} R :=
  perfDGInputOf R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel R (DGKappaCone R D I)
    (dgKappaConePerfectObjects R D I))

/-- 核の包含は、D-9 の同じ実包含そのもの。 -/
def dgKappaResolvedKernelInputMap :
    dgKappaResolvedKernelKInput R D I ⟶ dgKappaResolvedConeKInput R D I :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernelInclusion R (DGKappaCone R D I)
    (dgKappaConePerfectObjects R D I))

/-- D-9 の局所 Hom K-平坦性は、同じ包装された実核にも成り立つ。 -/
theorem dgKappaResolvedKernel_homKFlat : localHomKFlat R (dgKappaResolvedKernelKInput R D I) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_homKFlat R (DGKappaCone R D I)
    (dgKappaConePerfectObjects R D I)

/-- 同じ実核の全頂点は、元の分解 cone の商包含との合成で零化される。 -/
theorem dgKappaResolvedKernel_quotient_kills
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgKappaResolvedKernelKInput R D I)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgKappaResolvedKernelInputMap R D I).down.comp
      (dgKappaResolvedSuspensionInputMap R D I).down)).app (Opposite.op ⦋0⦌) z) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_isStable R (DGKappaCone R D I)
    (dgKappaConePerfectObjects R D I)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D I)
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R
    (DGCategoryCellResolution.Source R (DGKappaCone R D I))
  let := dgKappaSuspensionInfinity_isStable R D I
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_isStableVerdierSequence R
    (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)).kills z
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using! h

/-- 指定収縮は D 正本の零化判定から得る。新しい収縮・商 API は追加しない。 -/
theorem dgKappaResolvedKernel_exists_contracted :
    ∃ C : DGQuotient.ContractedFunctor R (dgKappaResolvedKernelKInput R D I) Set.univ
      (dgKappaSuspensionKInput R D I),
      C.toDGFunctor = (dgKappaResolvedKernelInputMap R D I).down.comp
        (dgKappaResolvedSuspensionInputMap R D I).down := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_exists_contracted_of_zeroing
  intro b
  have h := dgKappaResolvedKernel_quotient_kills R D I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex b.val)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] using h

/-- 固定 ν の Verdier 証拠と零角の Perf 零性に条件付きで、同じ核・商辺の実屋根を得る。 -/
theorem exists_dgKappaResolvedRelativeRoof
    (hV : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgKInputNuMap R (dgKappaResolvedKernelInputMap R D I))
      (dgKInputNuMap R (dgKappaResolvedSuspensionInputMap R D I)))
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R
      (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I)))) :
    ∃ t : DGKappaSuspensionRelativeRoofInput R D I,
      t.kernel = dgKappaResolvedKernelKInput R D I ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.diagram.square =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaResolvedKernelInputMap R D I)).edge := by
  obtain ⟨C, hC⟩ := dgKappaResolvedKernel_exists_contracted R D I
  exact exists_dgKappaRelativeRoof_of_fixedNull R D I
    (dgKappaResolvedKernelKInput R D I) (dgKappaResolvedKernelInputMap R D I) C hC hV hz

variable
  (hV : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgKInputNuMap R (dgKappaResolvedKernelInputMap R D I))
    (dgKInputNuMap R (dgKappaResolvedSuspensionInputMap R D I)))
  (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R
    (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I))))

/-- 固定 ν の Verdier 証拠・零角の Perf 零性に条件付きで選ぶ、元の実核の相対屋根。 -/
def dgKappaResolvedRelativeRoof : DGKappaSuspensionRelativeRoofInput R D I :=
  (exists_dgKappaResolvedRelativeRoof R D I hV hz).choose

/-- 条件付き屋根の核は、新たな模型ではなく D-9 の同じ実小核。 -/
theorem dgKappaResolvedRelativeRoof_kernel :
    (dgKappaResolvedRelativeRoof R D I hV hz).kernel = dgKappaResolvedKernelKInput R D I :=
  (exists_dgKappaResolvedRelativeRoof R D I hV hz).choose_spec.1

/-- 条件付き屋根の包含は、同じ実核の元の包含の全一単体。 -/
theorem dgKappaResolvedRelativeRoof_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (dgKappaResolvedRelativeRoof R D I hV hz).diagram.square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaResolvedKernelInputMap R D I)).edge :=
  (exists_dgKappaResolvedRelativeRoof R D I hV hz).choose_spec.2

/-- 条件付き屋根の商辺は、元の平坦懸垂の同じ商包含の全一単体。 -/
theorem dgKappaResolvedRelativeRoof_quotient :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgKappaResolvedRelativeRoof R D I hV hz).diagram.square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaResolvedSuspensionInputMap R D I)).edge :=
  (dgKappaResolvedRelativeRoof R D I hV hz).quotient

end SerrePositivity.KST.NonConnective
