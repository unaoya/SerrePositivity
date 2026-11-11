module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceOuterComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterSquareDiagramIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：LT 絶対外周を厚平坦核を始点とする元実核面へ指定三境界付きで比較する。
方針：元 cell 外周認証と元始域比較長方形の全同型を合成する。
規約：元増大屋根・resolved 商・実完備化を保持。使われ方：共通 LT 実長方形の外周認証。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：厚核実面へ向かう包含・商・零角の指定比較を同じ元屋根比較で移す。
方針：元 cell 外面の三指定比較に元屋根全比較の三制限を合成する。
規約：各境界を全比較の存在から選択しない。使われ方：厚核版外周の境界引数。 -/
def dgOdotMilnorKernelOuterSquareBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso
    (dgOdotMilnorActualOuterDiagram R d h).square
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) where
  inclusion := (dgOdotMilnorOuterSquareBoundary R d h).inclusion ≪≫
    (dgOdotMilnorSourceOuterToKernelPerfectComparison R d h).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge
  quotient := (dgOdotMilnorOuterSquareBoundary R d h).quotient ≪≫
    (dgOdotMilnorSourceOuterToKernelPerfectComparison R d h).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge
  zero := (dgOdotMilnorOuterSquareBoundary R d h).zero ≪≫
    (dgOdotMilnorSourceOuterToKernelPerfectComparison R d h).precomp _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierZeroCorner

/-- 概要：元 LT 絶対外周から元厚核実零化面への指定三境界付き全比較。
方針：同じ元屋根長方形全比較を外周の全認証へ合成し、元三制限を回収する。
規約：共通 LT 実長方形の存在は別工程。使われ方：Sp 正本への厚核版外周認証。 -/
def dgOdotMilnorKernelOuterSquareDiagramIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso
    (dgOdotMilnorActualOuterDiagram R d h).square
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
    (dgOdotMilnorKernelOuterSquareBoundary R d h) where
  comparison := (dgOdotMilnorOuterSquareDiagramIso R d h).comparison ≪≫
    dgOdotMilnorSourceOuterToKernelPerfectComparison R d h
  inclusion_eq := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, (dgOdotMilnorOuterSquareDiagramIso R d h).inclusion_eq]
    rfl
  quotient_eq := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, (dgOdotMilnorOuterSquareDiagramIso R d h).quotient_eq]
    rfl
  zero_eq := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, (dgOdotMilnorOuterSquareDiagramIso R d h).zero_eq]
    rfl
end SerrePositivity.KST.SConstruction
