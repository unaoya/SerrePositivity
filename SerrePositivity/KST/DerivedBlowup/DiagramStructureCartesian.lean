module

public import SerrePositivity.KST.DerivedBlowup.DiagramStructureDerivedRegularTransition
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraCartesianCondition

/-!
概要：KST §3.1 の実際の構造図式加群の cartesian perfect 性。
方針：指定係数拡大比較を局所 regular 同型と代表延長同型を介して比較する。
規約：canonical な比較射自体の可逆性を証明する。
使われ方：導来 blowup の構造加群を大域 Perf 候補へ入れる。
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

/-- 概要：構造加群の指定導来係数拡大比較は全包含で同型。
方針：局所 regular 同型を係数拡大してから比較し、代表延長比較の可逆性を使う。
規約：KST §3.1。使われ方：構造加群の canonical な cartesian 条件。 -/
theorem diagramStructureDerivedExtensionComparison_isIso {i j : J} (h : i ≤ j) :
    IsIso (diagramAlgebraDerivedExtensionComparison F h (derivedDiagramStructureModule F)) := by
  have hc : IsIso ((diagramAlgebraDerivedExtension F h).map
      (diagramStructureRegularDerivedIso F i).hom ≫
      diagramAlgebraDerivedExtensionComparison F h (derivedDiagramStructureModule F)) := by
    rw [diagramStructureRegularDerivedIso_extension]
    infer_instance
  let := hc
  exact IsIso.of_isIso_comp_left
    ((diagramAlgebraDerivedExtension F h).map (diagramStructureRegularDerivedIso F i).hom) _

/-- 概要：実際に構成した構造図式加群は canonical な比較に関して cartesian。
方針：各包含の指定係数拡大比較の可逆性を全称化する。
規約：KST §3.1。使われ方：構造加群の大域 Perf 候補への所属。 -/
theorem diagramStructureModule_cartesian :
    diagramAlgebraCartesian F (derivedDiagramStructureModule F) :=
  fun _ _ h => diagramStructureDerivedExtensionComparison_isIso F h

/-- 概要：実際の構造図式加群は cartesian かつ全頂点で perfect。
方針：指定比較の可逆性と証明済み局所 regular 性を組み合わせる。
規約：KST §3.1、層レベルの比較は別工程。
使われ方：導来 blowup の構造加群と生成系の実現。 -/
theorem diagramStructureModule_cartesianPerfect :
    diagramAlgebraCartesianPerfect F (derivedDiagramStructureModule F) :=
  ⟨diagramStructureModule_cartesian F, diagramStructureModule_locallyPerfect F⟩

end SerrePositivity.KST.DerivedBlowup
