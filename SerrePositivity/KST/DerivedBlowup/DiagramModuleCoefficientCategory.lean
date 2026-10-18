module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleAssociativity
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGAlgebraDiagram
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
概要：KST §3.1 の全 diagram-module を表す係数 dg 圏とその加群圏。
方針：証明済みの Hom・単位・合成・圏法則を既存 DGCategory へ渡し、その opposite の右加群を取る。
規約：対象は全 diagram-module。cartesian・perfect 条件は別に課す。
使われ方：objectwise acyclic による導来化と導来 blowup の coherent な加群模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]

/-- 概要：代数図式を保持する diagram-module 係数圏の対象型。
方針：元の添字を構造体で包み、異なる代数図式の dg 構造を型で区別する。
規約：KST §3.1。使われ方：dg 圏の型クラスの対象型。 -/
structure DiagramModuleCoefficientObject (F : J ⥤ Mon (Complex R)) where
  index : J

/-- 概要：全 diagram-module を表す実際の係数 dg 圏。
方針：証明済みの単位・結合律を既存の Hom からの constructor に渡す。
規約：KST §3.1、Hom(i,j) は包含があれば目標代数、なければ零。
使われ方：全 diagram-module を既存の dg 加群として扱う。 -/
instance diagramModuleCoefficientDGCategory (F : J ⥤ Mon (Complex R)) :
    DGCategory R (DiagramModuleCoefficientObject F) :=
  ofHomObjects R (DiagramModuleCoefficientObject F)
    (fun x y => diagramModuleHom F x.index y.index)
    (fun x => diagramModuleId F x.index)
    (fun x y z => diagramModuleComp F x.index y.index z.index)
    (fun x y => diagramModule_left_unit F x.index y.index)
    (fun x y => diagramModule_right_unit F x.index y.index)
    (fun x y z w => diagramModule_assoc F x.index y.index z.index w.index)

/-- 概要：全 diagram-module の dg 加群圏。
方針：共変の図式加群を係数 dg 圏の opposite 上の右 dg 加群として読む。
規約：KST §3.1、Hom も既存の全次数自然変換の複体を使う。
使われ方：図式全体の objectwise acyclic による導来化。 -/
abbrev AllDiagramModules (F : J ⥤ Mon (Complex R))
    [Small.{u} (DiagramModuleCoefficientObject F)] :=
  ModuleCategory R (DiagramModuleCoefficientObject F)ᵒᵖ

/-- 概要：全 diagram-module の objectwise 擬同型による導来圏。
方針：既存の moduleQuasiIso の局所化を使う。
規約：KST §3.1、cartesian・perfect 条件をまだ課さない通常の導来圏。
使われ方：coherent な降下模型を組み立てる基礎の局所化。 -/
abbrev DerivedAllDiagramModules (F : J ⥤ Mon (Complex R))
    [Small.{u} (DiagramModuleCoefficientObject F)] :=
  DerivedModuleCategory R (DiagramModuleCoefficientObject F)ᵒᵖ

variable (R) {I : Type} [DecidableEq I]

/-- 概要：導来 blowup の全有限重なりの diagram-module 係数 dg 圏の対象型。
方針：実際の全有限重なり dg 代数関手を一般の係数 dg 圏に渡す。
規約：KST Def3.1・Lemma3.6。使われ方：導来 blowup の大域加群模型。 -/
abbrev BlowupDiagramCoefficientObject (a : I → R) :=
  DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a)

end SerrePositivity.KST.DerivedBlowup
