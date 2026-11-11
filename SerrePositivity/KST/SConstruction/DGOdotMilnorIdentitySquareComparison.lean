module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityTriangleComparisons
public import SerrePositivity.KST.SConstruction.StableZeroSquareComparison
public import SerrePositivity.KST.SConstruction.SquareFrameHomotopyPostcomp

/-!
概要：元恒等右面の全四角形を、元絶対恒等提示全体へ比較する。
方針：同じ四境界の StableInfinity 像を零対角上で接合し、充満忠実な包含で戻す。
規約：D2 の全比較は明示入力。指定三境界との同じ比較の一致は別工程。
使われ方：実右面の VerdierSquareDiagramIso の全四角形同型成分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)
namespace DGOdotMilnorIdentityLaxComparisonInput
variable (v : DGOdotMilnorIdentityLaxComparisonInput R d)

/-- 概要：元 Cat^perf 四境界比較を同じ StableInfinity 内へ写す。
方針：同じ包含で四ホモトピーと共有四頂点経路を同時に写す。
規約：元比較を保持。使われ方：共有零対角の一意性への接続。 -/
def rawSquareFrameComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare ((dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R) ≫
      perfectStableInfinityInclusion))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare ((perfectIdentityLaxSequence (Q) (hQ)).presentation.square ≫
      perfectStableInfinityInclusion)) :=
  squareFrameHomotopyPostcomp (squareFrameComparison R d v) perfectStableInfinityInclusion

/-- 概要：元恒等右面の StableInfinity 全図式は絶対恒等提示全体と同型。
方針：元四境界と元零角に対する共有零対角の接合を使う。
規約：元二胞体を保持。使われ方：元 Cat^perf 全右面比較の逆像。 -/
def rawSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R) ≫ perfectStableInfinityInclusion)
    ((perfectIdentityLaxSequence (Q) (hQ)).presentation.square ≫ perfectStableInfinityInclusion) :=
  stableZeroSquareComparison (rawSquareFrameComparison R d v) (by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex
      ((dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R) ≫ perfectStableInfinityInclusion) 0 1))
    rw [Category.assoc, dgKInputPerfectNu_inclusion]
    exact dgOdotMilnorIdentityNullSquare_zero R d)

/-- 概要：元恒等実右面の Cat^perf 全四角形は元絶対恒等提示全体と同型。
方針：同じ元 StableInfinity 比較を充満忠実な包含で戻す。
規約：D2 入力を保持し、指定三境界の一致はまだ主張しない。
使われ方：実右面全図式認証の比較成分。 -/
def perfectSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (perfectIdentityLaxSequence (Q) (hQ)).presentation.square :=
  perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso (rawSquareComparison R d v)
end DGOdotMilnorIdentityLaxComparisonInput
end SerrePositivity.KST.SConstruction
