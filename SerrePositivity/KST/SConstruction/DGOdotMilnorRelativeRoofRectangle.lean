module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRelativeSourceRoof
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRelativeRectangle

/-!
概要：同じ平坦核を始域とする実長方形に、構成済みの元入力への増大屋根を接続する。
方針：指定全境界比較は保持し、始域の回収は実二辺と指定 ν 同値で行う。
規約：実 S 長方形と全比較は明示入力のまま、始域屋根の存在は入力しない。
使われ方：17:53 採用の d④ の主接続と元始域の不変量値の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
  Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：同じ実平坦核を始域とする完備化付き相対長方形の残入力。
方針：二面・指定三境界・上下二単体を保つ全比較を保持する。
規約：元入力への屋根は構成済みであり追加入力にしない。
使われ方：Sp-6 の未供給の実長方形と主経路の接続。 -/
structure DGOdotMilnorRelativeRoofRectangleInput where
  rectangle : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle (dgKInputPerfectNu.{u, u + 1} R)
  boundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (rectangle.diagram ≫ dgKInputPerfectNu R)
    (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram
  image : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (rectangle.diagram ≫ dgKInputPerfectNu R)
    (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram boundary
  kernel_vertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare rectangle.diagram 2) 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d)

namespace DGOdotMilnorRelativeRoofRectangleInput
variable {R d h} (v : DGOdotMilnorRelativeRoofRectangleInput R d h)

/-- 概要：実長方形の始域から元入力を回収する同じ実屋根。
方針：既構成の二辺を元の平坦核頂点の等号で照合する。
規約：S 内の元始域頂点等号を要求しない。使われ方：元入力の値の回収。 -/
def sourceRoof : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof (dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare v.rectangle.diagram 2) 0 0) := by
  rw [v.kernel_vertex]
  exact dgOdotMilnorRelativeSourceRoof R d h

/-- 概要：同じ実相対長方形の比較面の値は引き戻し。
方針：完備化付きの二面の実相殺を使用する。規約：元の図式全体を保持する。
使われ方：屋根版の d④ から Cat^perf 不変量への結論。 -/
theorem comparison_isPullback {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare v.rectangle.diagram 2) ≫
      dgKInputPerfectNu R ≫ E) := v.rectangle.comparisonSquare_isPullback hE

/-- 概要：同じ実比較面の始域値は元の入力値と指定同型で結ばれる。
方針：Sp 正本の同じ始域屋根の値を適用する。規約：全境界比較と独立に選び直さない。
使われ方：元対角始域を保つ LT の値の接続。 -/
def sourceValueIso (E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((dgKInputPerfectNu R ≫ E).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d)))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare v.rectangle.diagram 2) ≫
        dgKInputPerfectNu R ≫ E) 0 0) :=
  v.rectangle.sourceValueIso v.sourceRoof E

end DGOdotMilnorRelativeRoofRectangleInput
end SerrePositivity.KST.SConstruction
