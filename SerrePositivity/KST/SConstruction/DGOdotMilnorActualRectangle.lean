module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRelativeRoofRectangle

/-!
概要：Sp の絶対二面から実 ν 長方形への接続口を、同じ Milnor 図式へ特殊化する。
方針：実長方形と指定三境界付き二面比較・上下二単体付き全比較を明示する。
規約：各比較の存在は未証明であり、この入力型や条件付き結論を d④ 完了と数えない。
使われ方：S 内の別の厳密 Verdier 代表を要求せず、供給すべき三つの全比較を固定する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
  Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "L" => dgOdotMilnorCompletedLaxQuotient R d h
/-- 概要：同じ完備化先の恒等 lax 差の絶対右面。
方針：構成済みの実提示を使用する。規約：同じ完備化先を保持する。
使われ方：実右面への全比較の始域。 -/
def dgOdotMilnorActualRightDiagram : PerfectVerdierDiagram.{u + 1} :=
  (perfectIdentityLaxSequence (dgOdotMilnorCompletedLaxQuotient R d h).sequence.right
    (dgOdotMilnorCompletedLaxQuotient R d h).sequence.right_complete).presentation

/-- 概要：同じ実商と完備化を保持する LT 長方形の絶対外周。
方針：元の全長方形の外面を使用する。規約：別の提示を選び直さない。
使われ方：実外周への全比較の始域。 -/
def dgOdotMilnorActualOuterDiagram : PerfectVerdierDiagram.{u + 1} :=
  (dgOdotMilnorCompletedLaxQuotient R d h).outerDiagram

local notation "r" => dgOdotMilnorActualRightDiagram R d h
local notation "o" => dgOdotMilnorActualOuterDiagram R d h

/-- 概要：同じ実 S 長方形と Sp 正本の三つの全比較の残入力。
方針：絶対二面から実 ν 面への比較を直接保持する。
規約：二面の S 内の別代表は仮定しない。使われ方：d④ の実構成の供給境界。 -/
structure DGOdotMilnorActualRectangleInput where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R
  rightBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (r).square
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ diagram ≫ dgKInputPerfectNu R)
  rightComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (r).square
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ diagram ≫ dgKInputPerfectNu R) rightBoundary
  outerBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (o).square
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ diagram ≫ dgKInputPerfectNu R)
  outerComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (o).square
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ diagram ≫ dgKInputPerfectNu R) outerBoundary
  boundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (diagram ≫ dgKInputPerfectNu R) (L).rectangleDiagram
  comparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (diagram ≫ dgKInputPerfectNu R)
    (L).rectangleDiagram boundary
  kernel_vertex : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 2) 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d)

namespace DGOdotMilnorActualRectangleInput
variable {R d h} (v : DGOdotMilnorActualRectangleInput R d h)

/-- 概要：同じ実 S 長方形の第三面の値は二つの絶対提示から引き戻しとなる。
方針：Sp の実二面直接認証をそのまま適用する。
規約：全比較は明示入力。使われ方：三比較の実構成後の主接続。 -/
theorem comparison_isPullback {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare v.diagram 2) ≫
      dgKInputPerfectNu R ≫ E) :=
  RelativePerfectVerdierRectangle.comparison_isPullback_of_actualFaces
    v.diagram (r) (o) hE v.rightBoundary v.rightComparison v.outerBoundary v.outerComparison

include v in
/-- 概要：上下二単体を含む同じ全比較で元の LT 長方形の比較面へ値を運ぶ。
方針：Sp の実二面認証と全長方形輸送を一度に使用する。
規約：商辺の関手同型だけで代用しない。使われ方：元 LT 図式との全接続。 -/
theorem completedComparison_isPullback {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (L).rectangleDiagram 2) ≫ E) :=
  RelativePerfectVerdierRectangle.comparison_isPullback_of_actualFaces_imageIso
    v.diagram (r) (o) hE v.rightBoundary v.rightComparison v.outerBoundary v.outerComparison
      v.boundary v.comparison

/-- 概要：元対角始域への増大屋根は同じ実長方形の始域に接続する。
方針：構成済みの実屋根を同じ厚核頂点へ照合する。
規約：元始域の S 頂点等号は要求しない。使われ方：同じ全比較の始域成分。 -/
def sourceRoof : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof (dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare v.diagram 2) 0 0) := by
  rw [v.kernel_vertex]
  exact dgOdotMilnorRelativeSourceRoof R d h

/-- 概要：元入力値から元 LT 比較面の始域値へ、同じ全比較の成分で移す。
方針：Sp の直接屋根接続を使用する。規約：始域同型を別に選び直さない。
使われ方：native Verdier 列と LT 錐の元始域を保った値の回収。 -/
def sourceValueIso (E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((dgKInputPerfectNu R ≫ E).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d)))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (L).rectangleDiagram 2) ≫ E) 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso
    v.boundary v.comparison v.sourceRoof E

end DGOdotMilnorActualRectangleInput
end SerrePositivity.KST.SConstruction
