module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroArrowComparisons

/-!
概要：元零角二辺の指定端点付き比較を元実／絶対四角形の全辺へ戻す。
方針：元四辺の回収と同じ全関手同型を使い、完備包含で反映する。
規約：元左辺・元上辺・同じ零角成分を保持。使われ方：元全比較 prism の二境界面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元実左辺の固定 ν 完全射の辺は元実四角形の同じ左辺。
方針：元四辺の回収と元 ν の全一単体回収を使う。
規約：元全辺の等号。使われ方：元実左境界の厳密保持。 -/
lemma dgOdotMilnorNuZeroLeftMap_diagram :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualLeft R d)).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R := by
  symm
  rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).2.2.1]
  change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))).edge) = _
  exact congrArg SSet.yonedaEquiv.symm
    (dgKInputNu_edge R (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d)))

/-- 概要：元実上辺の固定 ν 完全射の辺は元実四角形の同じ上辺。
方針：元の四辺と元 ν の全一単体を回収する。
規約：元全辺の等号。使われ方：元実上境界の厳密保持。 -/
lemma dgOdotMilnorNuZeroTopMap_diagram :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualTop R d)).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R := by
  symm
  rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).2.2.2]
  change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).edge) = _
  exact congrArg SSet.yonedaEquiv.symm
    (dgKInputNu_edge R (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d)))

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元標準零角への辺は同じ絶対四角形の元左辺。
方針：同じ選択絶対提示の元四辺回収を使う。
規約：元全辺の等号。使われ方：元絶対左境界の厳密保持。 -/
lemma dgOdotMilnorNuZeroAbsoluteLeftMap_diagram :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K))).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) :=
  (perfectVerdierRawSquare_edges (dgOdotMilnorNuPerfectSequence R d h)).2.2.1.symm

/-- 概要：元標準零角からの辺は同じ絶対四角形の元上辺。
方針：同じ元絶対四角形の上辺回収を使う。
規約：元全辺の等号。使われ方：元絶対上境界の厳密保持。 -/
lemma dgOdotMilnorNuZeroAbsoluteTopMap_diagram :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory (B))).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) :=
  (perfectVerdierRawSquare_edges (dgOdotMilnorNuPerfectSequence R d h)).2.1.symm

/-- 概要：元実／絶対四角形の元左辺を同じ指定零角成分で全比較する。
方針：元全辺の等号で同じ端点成分固定比較を戻す。
規約：元四角形と元二辺。使われ方：上比較 prism の元左境界。 -/
def dgOdotMilnorNuZeroLeftDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  Eq.mp (congrArg₂ (fun f g : (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (dgOdotMilnorNuZeroLeftMap_diagram R d) (dgOdotMilnorNuZeroAbsoluteLeftMap_diagram R d h))
      (dgOdotMilnorNuZeroLeftArrowComparison R d)

/-- 概要：元実／絶対四角形の元上辺を同じ指定零角成分で全比較する。
方針：元全辺回収で同じ端点成分固定比較を戻す。
規約：元四角形と元二辺。使われ方：上比較 prism の元上境界。 -/
def dgOdotMilnorNuZeroTopDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  Eq.mp (congrArg₂ (fun f g : (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (dgOdotMilnorNuZeroTopMap_diagram R d) (dgOdotMilnorNuZeroAbsoluteTopMap_diagram R d h))
      (dgOdotMilnorNuZeroTopArrowComparison R d)

/-- 概要：元実／絶対 Cat^perf 四角形の元左辺の同じ全比較。
方針：同じ完備包含で元 StableInfinity 比較を反映する。
規約：元の全左辺を保持。使われ方：全四角形比較の零角左境界。 -/
def dgOdotMilnorNuZeroPerfectLeftDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square) := by
  apply perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫
      dgKInputPerfectNu R ≫ perfectStableInfinityInclusion)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ perfectVerdierSquare (dgOdotMilnorNuPerfectSequence R d h) ≫
      perfectStableInfinityInclusion)
  rw [dgKInputPerfectNu_inclusion, perfectVerdierSquare_inclusion]
  exact dgOdotMilnorNuZeroLeftDiagramComparison R d h

/-- 概要：元実／絶対 Cat^perf 四角形の元上辺の同じ全比較。
方針：同じ完備包含の充満忠実性を使う。
規約：元の全上辺を保持。使われ方：全四角形比較の零角上境界。 -/
def dgOdotMilnorNuZeroPerfectTopDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square) := by
  apply perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫
      dgKInputPerfectNu R ≫ perfectStableInfinityInclusion)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ perfectVerdierSquare (dgOdotMilnorNuPerfectSequence R d h) ≫
      perfectStableInfinityInclusion)
  rw [dgKInputPerfectNu_inclusion, perfectVerdierSquare_inclusion]
  exact dgOdotMilnorNuZeroTopDiagramComparison R d h

end SerrePositivity.KST.SConstruction
