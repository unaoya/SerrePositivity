module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullSquareShortComparisons

/-!
概要：元実 ν 核零化四角形の全比較を、Sp 所有の指定三境界付き全四角形比較へ接続する。
方針：既存の包含・商比較と既存零角左辺からの零角比較を指定し、元全比較の制限を回収する。
規約：LT の実右面・外周・全長方形の三つの存在証明とは区別する。
使われ方：同じ元実核面の全比較を長方形の貼り合わせへ渡す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元実 ν 核面の既存の指定包含・商・零角比較。
方針：元の指定全辺比較とその零角端点比較を束ねる。
規約：全四角形比較から境界を選ばない。使われ方：Sp 正本の全比較の三境界。 -/
def dgOdotMilnorNuNullRawSquareBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) where
  inclusion := dgOdotMilnorNuInclusionDiagramComparison R d h
  quotient := dgOdotMilnorNuProjectionDiagramComparison R d h
  zero := dgOdotMilnorNuNullRawSquareZeroBoundary R d h

/-- 概要：元実 ν 核面全体の同型は元の指定三境界を同時に保持する。
方針：元上下二胞体の比較を貼った同じ全同型と、三つの厳密回収を束ねる。
規約：元両二胞体を保持する Sp 正本の型。使われ方：LT の実長方形への核面接続。 -/
def dgOdotMilnorNuNullRawSquareDiagramIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))
    (dgOdotMilnorNuNullRawSquareBoundary R d h) where
  comparison := dgOdotMilnorNuNullSquareComparison R d h
  inclusion_eq := dgOdotMilnorNuNullSquareComparison_inclusion R d h
  quotient_eq := dgOdotMilnorNuNullSquareComparison_projection R d h
  zero_eq := dgOdotMilnorNuNullSquareComparison_zero R d h

/-- 概要：元絶対核提示から元実 ν 核面へ向かう同じ指定三境界。
方針：元の指定包含・商・零角比較をそれぞれ逆向きに保持する。
規約：境界を選び直さない。使われ方：Sp の絶対提示から実面への接続。 -/
def dgOdotMilnorNuAbsoluteRawSquareBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso
    (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R) where
  inclusion := (dgOdotMilnorNuInclusionDiagramComparison R d h).symm
  quotient := (dgOdotMilnorNuProjectionDiagramComparison R d h).symm
  zero := (dgOdotMilnorNuNullRawSquareZeroBoundary R d h).symm

/-- 概要：元絶対核提示から実 ν 核面への同じ指定三境界付き全比較。
方針：元両二胞体を保つ全比較を反転し、三制限の逆向き回収を使う。
規約：Sp 正本の型と向き。使われ方：同じ固定 ν の実長方形への核面接続。 -/
def dgOdotMilnorNuAbsoluteRawSquareDiagramIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso
    (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (dgOdotMilnorNuAbsoluteRawSquareBoundary R d h) where
  comparison := (dgOdotMilnorNuNullSquareComparison R d h).symm
  inclusion_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm _ _).trans
    (congrArg Iso.symm (dgOdotMilnorNuNullSquareComparison_inclusion R d h))
  quotient_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm _ _).trans
    (congrArg Iso.symm (dgOdotMilnorNuNullSquareComparison_projection R d h))
  zero_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm _ _).trans
    (congrArg Iso.symm (dgOdotMilnorNuNullSquareComparison_zero R d h))

end SerrePositivity.KST.SConstruction
