module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraBottomInclusion
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Functor.Closed

/-!
概要：KST §3.1 の構造加群を全係数図式上の実際の dg 加群として構成する。
方針：補助始点の共変 representable を元の係数圏へ制限する。
規約：全次数の作用と自然性を既存の dg representable から保持する。
使われ方：大域構造加群・捻り加群とその局所比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：各頂点にその局所 dg 代数を持つ実際の全図式加群。
方針：補助始点からの Hom を与える共変 representable を制限する。
規約：KST §3.1、dg 加群の全 Hom 作用を備える。
使われ方：構造加群の導来像と cartesian perfect 条件の入力。 -/
def diagramStructureRawModule : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ :=
  restrictModule R (DiagramModuleCoefficientObject F)ᵒᵖ
    (DiagramModuleCoefficientObject (diagramAlgebraWithBottom F))ᵒᵖ
    (diagramAlgebraBottomInclusion F).op.op
    (representable R (op (⟨⊥⟩ : DiagramModuleCoefficientObject (diagramAlgebraWithBottom F))))

/-- 概要：構造図式加群の各頂点での複体はその局所代数の複体。
方針：補助始点から各頂点への Hom の包含条件を簡約する。
規約：KST §3.1。使われ方：局所比較と構造加群の値の計算。 -/
theorem diagramStructureRawModule_obj (i : J) :
    (diagramStructureRawModule F).obj (op (op ⟨i⟩)) = (F.obj i).X := by
  change diagramModuleHom (diagramAlgebraWithBottom F) ⊥ (i : WithBot J) = _
  simp only [diagramModuleHom, bot_le, ite_true]
  rfl

/-- 概要：構造図式加群を全 diagram-module の通常圏の対象にする。
方針：構成済み raw dg 加群を既存の閉零圏へ包む。
規約：KST §3.1。使われ方：主導来局所化への構造加群の像。 -/
def diagramStructureModule [Small.{u} (DiagramModuleCoefficientObject F)] : AllDiagramModules F :=
  ForgetEnrichment.of (Complex R) (diagramStructureRawModule F)

/-- 概要：通常加群圏の構造図式加群も各頂点で局所代数の複体を与える。
方針：raw dg 加群の構成済み評価公式を使う。
規約：KST §3.1。使われ方：局所加群評価の具体的な値。 -/
theorem diagramStructureModule_value [Small.{u} (DiagramModuleCoefficientObject F)] (i : J) :
    (moduleEvaluation R (DiagramModuleCoefficientObject F)ᵒᵖ (op ⟨i⟩)).obj
      (diagramStructureModule F) = (F.obj i).X :=
  diagramStructureRawModule_obj F i

/-- 概要：構造図式加群の主導来局所化での対象。
方針：実際に構成した全図式加群を指定局所化で送る。
規約：KST §3.1、cartesian・perfect 性は別に証明する。
使われ方：構造加群と捻り加群の導来 Hom の計算。 -/
def derivedDiagramStructureModule [Small.{u} (DiagramModuleCoefficientObject F)] :
    DerivedAllDiagramModules F :=
  (moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj (diagramStructureModule F)

end SerrePositivity.KST.DerivedBlowup
