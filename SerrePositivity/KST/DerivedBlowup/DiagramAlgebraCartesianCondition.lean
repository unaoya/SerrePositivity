module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraLocallyPerfect

/-!
概要：KST §3.1 の一対象正規表示での cartesian・局所 perfect 条件。
方針：canonical な導来係数拡大比較の可逆性を全包含で要求する。
規約：任意同型の存在を cartesian 条件の代用にしない。
使われ方：有限重なりの dg 図式の Perf 候補の対象条件。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：正規表示での指定導来係数拡大比較が全包含で可逆である条件。
方針：構成済み canonical な射の IsIso を用いる。
規約：KST §3.1。使われ方：coherent な局所図式の cartesian 対象条件。 -/
def diagramAlgebraCartesian : ObjectProperty (DerivedAllDiagramModules F) :=
  fun X => ∀ (i j : J) (h : i ≤ j), IsIso (diagramAlgebraDerivedExtensionComparison F h X)

/-- 概要：正規表示で cartesian かつ各頂点で perfect な導来図式加群。
方針：指定比較の可逆性と局所 perfect 条件を組み合わせる。
規約：KST §3.1。使われ方：既存の Koszul 模型の Perf 候補との比較。 -/
def diagramAlgebraCartesianPerfect : ObjectProperty (DerivedAllDiagramModules F) :=
  fun X => diagramAlgebraCartesian F X ∧ diagramAlgebraLocallyPerfect F X

end SerrePositivity.KST.DerivedBlowup
