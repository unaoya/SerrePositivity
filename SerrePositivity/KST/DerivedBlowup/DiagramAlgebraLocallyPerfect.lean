module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedEvaluation
public import SerrePositivity.DifferentialGraded.Perfect.Basic

/-!
概要：KST §3.1 の一対象正規表示での局所 perfect 条件。
方針：各局所導来評価に既存の有限 cell の retract による perfect 性を課す。
規約：全図式の主導来圏上の性質であり、cartesian 条件とは独立に定める。
使われ方：同じ全 diagram-module 模型の正規表示による局所条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：正規表示の全局所 dg 代数で perfect となる導来図式加群の性質。
方針：構成済み導来評価を通して既存 modulePerfect を要求する。
規約：KST §3.1。使われ方：正規表示での大域 Perf 候補の局所条件。 -/
def diagramAlgebraLocallyPerfect : ObjectProperty (DerivedAllDiagramModules F) :=
  fun X => ∀ i : J, modulePerfect R (AlgebraVertex (F.obj i))ᵒᵖ
    ((diagramAlgebraDerivedEvaluation F i).obj X)

/-- 概要：正規表示による局所 perfect 条件は導来図式加群の同型で不変。
方針：各導来評価で同型を送り、perfect 性の同型不変性を使う。
規約：KST §3.1。使われ方：射影的代表への条件の移送。 -/
instance diagramAlgebraLocallyPerfectClosedUnderIso :
    (diagramAlgebraLocallyPerfect F).IsClosedUnderIsomorphisms where
  of_iso e hX i := (modulePerfect R (AlgebraVertex (F.obj i))ᵒᵖ).prop_of_iso
    ((diagramAlgebraDerivedEvaluation F i).mapIso e) (hX i)

end SerrePositivity.KST.DerivedBlowup
