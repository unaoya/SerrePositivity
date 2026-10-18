module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedRestrictionAssociativity

/-!
概要：KST §3.1 の標準局所導来制限同型の左右の単位整合性。
方針：主局所化前の加群上で成分を計算し、標準加群制限同型の単位条件を送る。
規約：標準単位・合成同型の指定経路の自然変換等式として述べる。
使われ方：局所導来制限の擬関手の単位条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R))

set_option maxHeartbeats 2000000 in
-- 標準単位・合成同型の主局所化前の成分を照合するために必要。
/-- 概要：始点の恒等包含との標準導来制限合成同型は始点の単位同型に一致する。
方針：実加群上で計算し、証明済み左単位条件の局所化像を使う。
規約：KST §3.1。使われ方：標準導来制限比較の左単位条件。 -/
theorem diagramAlgebraDerivedRestrictionCompIso_left_unit {i j : J} (h : i ≤ j) :
    (diagramAlgebraDerivedRestrictionCompIso F (le_refl i) h).hom =
      whiskerLeft (diagramAlgebraDerivedRestriction F h)
        (diagramAlgebraDerivedRestrictionIdIso F i).hom := by
  apply moduleDerivedNatTrans_ext R (AlgebraVertex (F.obj j))ᵒᵖ
  intro M
  change (diagramAlgebraDerivedRestrictionCompIso F (le_refl i) h).hom.app
      ((moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).obj M) =
    (diagramAlgebraDerivedRestrictionIdIso F i).hom.app
      ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).obj
        ((diagramAlgebraModuleRestriction F h).obj M))
  rw [diagramAlgebraDerivedRestrictionCompIso_hom_app_Q,
    transitionDerivedRestrictionIdIso_hom_app_Q]
  exact congrArg ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map)
    (diagramAlgebraRestrictionCompIso_left_unit F h M)

set_option maxHeartbeats 2000000 in
-- 導来制限の射の計算と標準単位・合成同型を照合するために必要。
/-- 概要：終点の恒等包含との標準導来制限合成同型は終点の単位同型の制限に一致する。
方針：実加群上で射の計算を行い、証明済み右単位条件の局所化像を使う。
規約：KST §3.1。使われ方：標準導来制限比較の右単位条件。 -/
theorem diagramAlgebraDerivedRestrictionCompIso_right_unit {i j : J} (h : i ≤ j) :
    (diagramAlgebraDerivedRestrictionCompIso F h (le_refl j)).hom =
      whiskerRight (diagramAlgebraDerivedRestrictionIdIso F j).hom
        (diagramAlgebraDerivedRestriction F h) := by
  apply moduleDerivedNatTrans_ext R (AlgebraVertex (F.obj j))ᵒᵖ
  intro M
  change (diagramAlgebraDerivedRestrictionCompIso F h (le_refl j)).hom.app
      ((moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).obj M) =
    (diagramAlgebraDerivedRestriction F h).map
      ((diagramAlgebraDerivedRestrictionIdIso F j).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).obj M))
  rw [diagramAlgebraDerivedRestrictionCompIso_hom_app_Q,
    transitionDerivedRestrictionIdIso_hom_app_Q, transitionDerivedRestriction_map_Q]
  exact congrArg ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map)
    (diagramAlgebraRestrictionCompIso_right_unit F h M)

end SerrePositivity.KST.DerivedBlowup
