module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPerfectSquareDiagramIso
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceRoofPullback
public import SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierImageTransport
/-!
概要：元実核零化面と元始域比較長方形の外面を、全 Cat^perf 局所化不変量で認証する。
方針：元指定三境界付き全比較を Sp 正本へ渡し、既存の始域比較面と貼る。
規約：実核面の認証を追加入力にしない。LT 全長方形の三比較とは区別する。
使われ方：増大屋根を保持した元始域側の実零化面の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
variable {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
/-- 概要：元実 ν 核零化四角形は全 Cat^perf 局所化不変量で pullback。
方針：元絶対核提示から同じ実面への指定三境界付き全比較を Sp 正本へ渡す。
規約：元上下二胞体を保持し、実面の認証を仮定しない。
使われ方：元始域比較長方形の右面の実認証。 -/
theorem dgOdotMilnorPerfectNullSquare_value_isPullback
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R ≫ E) :=
  RelativePerfectVerdierDiagram.isPullback_of_perfectImageIso
    (dgOdotMilnorNuPerfectSequence R d h).presentation hE
    (dgOdotMilnorNuAbsolutePerfectSquareBoundary R d h)
    (dgOdotMilnorNuAbsolutePerfectSquareDiagramIso R d h)
/-- 概要：元始域比較長方形の同じ外面は Milnor 条件だけで不変量値の pullback。
方針：元実核面の認証を既存の同じ始域比較長方形の貼り合わせへ供給する。
規約：元 cell 始域と増大屋根を保持。使われ方：元始域への実零化面の回収。 -/
theorem dgOdotMilnorSourceNullRectangle_value_outer_isPullback_of_milnor
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare
      ((dgOdotMilnorSourceNullRectangle R d).diagram ≫ dgKInputPerfectNu R ≫ E) 1) :=
  dgOdotMilnorSourceNullRectangle_value_outer_isPullback R d h hE
    (dgOdotMilnorPerfectNullSquare_value_isPullback R d h hE)
end SerrePositivity.KST.SConstruction
