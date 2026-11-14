module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterSquareSideRecovery
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterZeroBoundary
public import SerrePositivity.KST.SConstruction.StableZeroTargetHom
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：元 LT 絶対外周から実始域零化外面への指定三境界付き全図式比較を構成する。
方針：元実四角形比較の逆を使い、包含・商・零角の指定全比較を厳密回収する。
規約：Milnor 条件のみ。共通 LT 実長方形の存在は別工程として保持する。
使われ方：Sp 正本の外周 VerdierSquareDiagramIso と後続の共通長方形接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元絶対外周から実外面への包含・商・零角の指定全比較。
方針：同じ側面証人から得た全比較の逆と、同じ全対象商の指定零角を束ねる。
規約：元始域屋根と元 resolved 商を保持。使われ方：外周認証の指定三境界。 -/
def dgOdotMilnorOuterSquareBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso
    (dgOdotMilnorActualOuterDiagram R d h).square
    (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R) where
  inclusion := (dgOdotMilnorOuterBottomComparison R d h).symm
  quotient := (dgOdotMilnorOuterRightComparison R d h).symm
  zero := dgOdotMilnorOuterZeroBoundary R d h

/-- 概要：元 LT 絶対外周の実始域外面への全比較は指定三境界を厳密に保持する。
方針：元全比較の逆と包含・商の回収、零終点の一意性で指定零角を照合する。
規約：同じ元両二胞体を保持。共通 LT 実長方形の完成とは数えない。
使われ方：Sp の完備化付き接続口の外周全図式認証。 -/
def dgOdotMilnorOuterSquareDiagramIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso
    (dgOdotMilnorActualOuterDiagram R d h).square
    (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (dgOdotMilnorOuterSquareBoundary R d h) where
  comparison := (dgOdotMilnorOuterPerfectSquareComparison R d h).symm
  inclusion_eq := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm
      (dgOdotMilnorOuterPerfectSquareComparison R d h) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).trans
      (congrArg Iso.symm (dgOdotMilnorOuterPerfectSquareComparison_bottom R d h))
  quotient_eq := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm
      (dgOdotMilnorOuterPerfectSquareComparison R d h) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).trans
      (congrArg Iso.symm (dgOdotMilnorOuterPerfectSquareComparison_right R d h))
  zero_eq := by
    apply perfectZeroPointFunctorIso_ext
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex
      (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R) 0 1))
    exact dgOdotMilnorSourceNullOuterSquare_perfect_zero R d
end SerrePositivity.KST.SConstruction
