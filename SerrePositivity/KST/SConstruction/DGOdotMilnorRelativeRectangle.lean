module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCompletedLandTamme
public import SerrePositivity.KST.SConstruction.DGKInputPerfectNu
public import SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierImageTransport

/-!
概要：resolved 商の実完備化を持つ Milnor 列を、固定 S の完備化付き相対長方形へ接続する。
方針：Sp 正本の実二面と指定境界付き全 ν 比較を、そのまま同じ Cat^perf 値へ写す。
規約：未供給の S 内全長方形を明示し、ν 像から S の代表の存在を推論しない。
使われ方：d④ の残入力を固定し、届いた実図式から同じ LT 引き戻しを得る。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
  Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元始域を保つ実 S 長方形と、同じ実 lax 長方形への全指定境界比較。
方針：包含・完備化後の商・零角と上下二単体の比較を全図式同型に固定する。
規約：各欄の実構成は別工程であり、この型の定義を完成に数えない。
使われ方：Sp の新しい完備化付き相対接続に渡す残入力。 -/
structure DGOdotMilnorRelativeRectangleInput where
  rectangle : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle (dgKInputPerfectNu.{u, u + 1} R)
  boundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (rectangle.diagram ≫ dgKInputPerfectNu R)
    (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram
  image : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (rectangle.diagram ≫ dgKInputPerfectNu R)
    (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram boundary
  source_vertex : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (((β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom) ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare rectangle.diagram 2) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d)

namespace DGOdotMilnorRelativeRectangleInput
variable {R d h} (v : DGOdotMilnorRelativeRectangleInput R d h)

/-- 概要：元の S 内比較四角形。
方針：同じ実長方形の第三面を回収する。規約：ν 像だけの図式に置換しない。
使われ方：同じ固定 ν の不変量値の引き戻し。 -/
def comparisonSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare v.rectangle.diagram 2

/-- 概要：同じ元始域を持つ比較四角形の値は引き戻し。
方針：Sp 正本の実二面の相殺を使用する。規約：商辺に strict 局所化は要求しない。
使われ方：d④ から Cat^perf 不変量の実結論。 -/
theorem comparison_isPullback {F : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
    (hF : IsPerfectLocalizingInvariant F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (v.comparisonSquare ≫ dgKInputPerfectNu R ≫ F) :=
  v.rectangle.comparisonSquare_isPullback hF

/-- 概要：全比較の二つの面は指定包含・商・零角の同じ比較を保持する。
方針：全長方形の既存の比較制限を回収する。規約：面ごとに同型を選び直さない。
使われ方：元の商境界の実比較との照合。 -/
lemma comparison_faces (j : Fin 2) :
    v.image.comparison.precomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace j) = (v.image.faces j).comparison :=
  v.image.faces_eq j

/-- 概要：上下の合成三角形の比較も指定された同じもの。
方針：全比較の二単体への制限を使用する。規約：四辺だけの比較に弱めない。
使われ方：元 resolved 射影と完備化の合成の回収。 -/
lemma comparison_triangles :
    v.image.comparison.precomp (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle (𝟙 _)) = v.boundary.bottom ∧
      v.image.comparison.precomp (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle (𝟙 _)) = v.boundary.top :=
  ⟨v.image.bottom_eq, v.image.top_eq⟩

/-- 概要：比較四角形の始域は元の同じ固定 dg 入力。
方針：入力の実頂点等号を保持する。規約：同値な別始域で代用しない。
使われ方：K-B 向け S• 界面の元始域回収。 -/
lemma comparison_source : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex v.comparisonSquare 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d) := v.source_vertex

end DGOdotMilnorRelativeRectangleInput
end SerrePositivity.KST.SConstruction
