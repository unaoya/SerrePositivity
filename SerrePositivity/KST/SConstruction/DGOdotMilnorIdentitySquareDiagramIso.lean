module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentitySquareSideRecovery
public import SerrePositivity.KST.SConstruction.StableZeroTargetHom
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元恒等実右面への指定三境界付き Cat^perf 全図式比較を構成する。
方針：元全四角形比較の包含・商制限を回収し、既存指定零角比較を零終点の一意性で照合する。
規約：D2 の全比較は明示入力。元全四角形・元指定三比較を保持する。
使われ方：Sp の完備化付き接続口が要求する実右面の VerdierSquareDiagramIso。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
namespace DGOdotMilnorIdentityLaxComparisonInput
variable (v : DGOdotMilnorIdentityLaxComparisonInput R d)

/-- 概要：絶対恒等提示から元実右面への全比較は同じ指定三境界を厳密に保持する。
方針：元全比較の逆と元包含・商制限の厳密回収、零点図式比較の一意性を使う。
規約：元両二胞体と既存指定零角比較を保持。D2 入力の存在は別工程。
使われ方：Sp 正本の完備化付き実右面認証。 -/
def rightSquareDiagramIso (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso
    (dgOdotMilnorActualRightDiagram R d h).square
    (dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (squareBoundary R d v h) where
  comparison := (perfectSquareComparison R d v).symm
  inclusion_eq := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm (perfectSquareComparison R d v) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).trans
      (congrArg Iso.symm (perfectSquareComparison_bottom R d v))
  quotient_eq := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm (perfectSquareComparison R d v) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).trans
      (congrArg Iso.symm (perfectSquareComparison_right R d v))
  zero_eq := by
    apply perfectZeroPointFunctorIso_ext
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex
      (dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R) 0 1))
    exact dgOdotMilnorIdentityNullSquare_perfect_zero R d
end DGOdotMilnorIdentityLaxComparisonInput
end SerrePositivity.KST.SConstruction
