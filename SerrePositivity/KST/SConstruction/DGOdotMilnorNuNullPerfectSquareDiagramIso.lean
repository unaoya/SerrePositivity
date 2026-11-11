module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPerfectBoundaryComponent
/-!
概要：元実 ν 核面と絶対完備化付き核列を、Cat^perf の指定三境界付き全図式で比較する。
方針：元 ν の同じ指定三比較を完備包含の逆像に取り、元全比較の制限と照合する。
規約：同じ元両二胞体と指定全同型を保持し、LT の実右面・外周とは区別する。
使われ方：固定 ν 長方形の核面の完備化付き接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
/-- 概要：元実 ν 核面の同じ指定三比較を Cat^perf の元三境界に保持する。
方針：元包含・商・零角の指定全比較を同じ完備包含の逆像に取る。
規約：包含後は元指定値を回収。使われ方：Sp 正本の全核面比較の三境界。 -/
def dgOdotMilnorNuNullPerfectSquareBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
    (dgOdotMilnorNuPerfectSequence R d h).presentation.square where
  inclusion := dgOdotMilnorNuNullPerfectBoundaryComponent R d h _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge
    (dgOdotMilnorNuInclusionDiagramComparison R d h)
  quotient := dgOdotMilnorNuNullPerfectBoundaryComponent R d h _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge
    (dgOdotMilnorNuProjectionDiagramComparison R d h)
  zero := dgOdotMilnorNuNullPerfectBoundaryComponent R d h _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierZeroCorner
    (dgOdotMilnorNuNullRawSquareZeroBoundary R d h)
/-- 概要：元実核面と元絶対核提示の Cat^perf 全比較は同じ元指定三境界を保持する。
方針：元全比較の完備包含からの回収と元三境界の厳密制限を接続する。
規約：元上下二胞体と同じ指定比較。使われ方：Sp の完備化付き実核面接続。 -/
def dgOdotMilnorNuNullPerfectSquareDiagramIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
    (dgOdotMilnorNuPerfectSequence R d h).presentation.square
    (dgOdotMilnorNuNullPerfectSquareBoundary R d h) where
  comparison := dgOdotMilnorNuNullPerfectSquareComparison R d h
  inclusion_eq := dgOdotMilnorNuNullPerfectBoundaryComponent_eq_precomp R d h _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge
    (dgOdotMilnorNuInclusionDiagramComparison R d h)
    (dgOdotMilnorNuNullSquareComparison_inclusion R d h)
  quotient_eq := dgOdotMilnorNuNullPerfectBoundaryComponent_eq_precomp R d h _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge
    (dgOdotMilnorNuProjectionDiagramComparison R d h)
    (dgOdotMilnorNuNullSquareComparison_projection R d h)
  zero_eq := dgOdotMilnorNuNullPerfectBoundaryComponent_eq_precomp R d h _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierZeroCorner
    (dgOdotMilnorNuNullRawSquareZeroBoundary R d h)
    (dgOdotMilnorNuNullSquareComparison_zero R d h)
/-- 概要：絶対完備化付き核提示から元実 ν 核面へ向かう同じ Cat^perf 三境界。
方針：元の指定三比較をそれぞれ反転して保持する。
規約：同じ全境界比較。使われ方：Sp の絶対提示から実面へ向かう接続。 -/
def dgOdotMilnorNuAbsolutePerfectSquareBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso
    (dgOdotMilnorNuPerfectSequence R d h).presentation.square
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) where
  inclusion := (dgOdotMilnorNuNullPerfectSquareBoundary R d h).inclusion.symm
  quotient := (dgOdotMilnorNuNullPerfectSquareBoundary R d h).quotient.symm
  zero := (dgOdotMilnorNuNullPerfectSquareBoundary R d h).zero.symm
/-- 概要：絶対完備化付き核提示から元実 ν 核面への同じ指定三境界付き全 Cat^perf 比較。
方針：元両二胞体を保つ全比較と三境界回収を同時に反転する。
規約：Sp 正本の型・向きと元指定比較。使われ方：元実長方形への核面接続。 -/
def dgOdotMilnorNuAbsolutePerfectSquareDiagramIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso
    (dgOdotMilnorNuPerfectSequence R d h).presentation.square
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
    (dgOdotMilnorNuAbsolutePerfectSquareBoundary R d h) where
  comparison := (dgOdotMilnorNuNullPerfectSquareComparison R d h).symm
  inclusion_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm _ _).trans
    (congrArg Iso.symm (dgOdotMilnorNuNullPerfectSquareDiagramIso R d h).inclusion_eq)
  quotient_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm _ _).trans
    (congrArg Iso.symm (dgOdotMilnorNuNullPerfectSquareDiagramIso R d h).quotient_eq)
  zero_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm _ _).trans
    (congrArg Iso.symm (dgOdotMilnorNuNullPerfectSquareDiagramIso R d h).zero_eq)
end SerrePositivity.KST.SConstruction
