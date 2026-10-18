module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeStructureDerivedTransition
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraCartesianCondition

/-!
概要：KST §3.1 の gauge で捻った実際の構造加群の cartesian perfect 性。
方針：指定係数拡大比較を代表延長同型と局所 regular 同型を介して比較する。
規約：canonical な比較射そのものの可逆性を証明する。
使われ方：O(m) の大域 Perf 候補での実現。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)
variable [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：gauge 構造加群の指定導来係数拡大比較は全包含で同型。
方針：局所 regular 同型を係数拡大した後、代表延長同型と重み付き同型を比較する。
規約：KST §3.1。使われ方：指定 cartesian 条件。 -/
theorem diagramGaugeStructureDerivedExtensionComparison_isIso {i j : J} (h : i ≤ j) :
    IsIso (diagramAlgebraDerivedExtensionComparison F h
      (derivedDiagramGaugeStructureModule F s)) := by
  have hc : IsIso ((diagramAlgebraDerivedExtension F h).map
      (diagramGaugeStructureRegularDerivedIso F s i).hom ≫
      diagramAlgebraDerivedExtensionComparison F h (derivedDiagramGaugeStructureModule F s)) := by
    rw [diagramGaugeStructureRegularDerivedIso_extension]
    infer_instance
  let := hc
  exact IsIso.of_isIso_comp_left
    ((diagramAlgebraDerivedExtension F h).map (diagramGaugeStructureRegularDerivedIso F s i).hom) _

/-- 概要：gauge で捻った実際の構造加群は canonical な比較に関して cartesian。
方針：指定係数拡大比較の可逆性を全称化する。
規約：KST §3.1。使われ方：O(m) の大域 Perf 条件の一部。 -/
theorem diagramGaugeStructureModule_cartesian :
    diagramAlgebraCartesian F (derivedDiagramGaugeStructureModule F s) :=
  fun _ _ h => diagramGaugeStructureDerivedExtensionComparison_isIso F s h

/-- 概要：gauge 構造加群は全頂点で局所 perfect。
方針：直接 regular 導来同型に沿って代表生成元の perfect 性を移す。
規約：KST §3.1。使われ方：大域 Perf 条件の局所条件。 -/
theorem diagramGaugeStructureModule_locallyPerfect :
    diagramAlgebraLocallyPerfect F (derivedDiagramGaugeStructureModule F s) := by
  intro i
  exact (modulePerfect R (AlgebraVertex (F.obj i))ᵒᵖ).prop_of_iso
    (diagramGaugeStructureRegularDerivedIso F s i)
    (modulePerfectOver_representable R (AlgebraVertex (F.obj i))ᵒᵖ
      (op .point) (Set.mem_univ _))

/-- 概要：gauge で捻った実際の構造加群は cartesian perfect。
方針：指定比較の可逆性と直接 regular 性を合わせる。
規約：KST §3.1、層レベルの比較は別工程。
使われ方：整数捻りを既存の大域 Perf 候補へ入れる。 -/
theorem diagramGaugeStructureModule_cartesianPerfect :
    diagramAlgebraCartesianPerfect F (derivedDiagramGaugeStructureModule F s) :=
  ⟨diagramGaugeStructureModule_cartesian F s, diagramGaugeStructureModule_locallyPerfect F s⟩

end SerrePositivity.KST.DerivedBlowup
