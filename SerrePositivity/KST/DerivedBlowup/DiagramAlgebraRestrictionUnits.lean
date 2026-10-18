module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraRestrictionAssociativity

/-!
概要：KST §3.1 の正規表示の標準局所加群制限同型の単位整合性。
方針：標準点での恒等成分に帰着し、左右の単位経路を照合する。
規約：標準合成同型と標準単位同型の指定経路を等式として比較する。
使われ方：局所導来制限の擬関手の単位条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：始点の恒等包含との標準制限合成同型は始点の単位同型に一致する。
方針：標準点で評価し、双方の恒等成分を使う。
規約：KST §3.1。使われ方：標準制限比較の左単位条件。 -/
theorem diagramAlgebraRestrictionCompIso_left_unit {i j : J} (h : i ≤ j)
    (M : ModuleCategory R (AlgebraVertex (F.obj j))ᵒᵖ) :
    (diagramAlgebraRestrictionCompIso F (le_refl i) h).hom.app M =
      (diagramAlgebraRestrictionIdIso F i).hom.app
        ((diagramAlgebraModuleRestriction F h).obj M) := by
  apply moduleMorphism_ext
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  rw [diagramAlgebraRestrictionCompIso_hom_eval, diagramAlgebraRestrictionIdIso_hom_eval]
  rfl

/-- 概要：終点の恒等包含との標準制限合成同型は終点の単位同型の制限に一致する。
方針：制限写像を標準点で評価し、標準合成・単位同型の恒等成分を使う。
規約：KST §3.1。使われ方：標準制限比較の右単位条件。 -/
theorem diagramAlgebraRestrictionCompIso_right_unit {i j : J} (h : i ≤ j)
    (M : ModuleCategory R (AlgebraVertex (F.obj j))ᵒᵖ) :
    (diagramAlgebraRestrictionCompIso F h (le_refl j)).hom.app M =
      (diagramAlgebraModuleRestriction F h).map
        ((diagramAlgebraRestrictionIdIso F j).hom.app M) := by
  apply moduleMorphism_ext
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  rw [diagramAlgebraRestrictionCompIso_hom_eval, moduleRestriction_map_eval]
  change 𝟙 _ = (moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
    ((diagramAlgebraRestrictionIdIso F j).hom.app M)
  rw [diagramAlgebraRestrictionIdIso_hom_eval]

end SerrePositivity.KST.DerivedBlowup
