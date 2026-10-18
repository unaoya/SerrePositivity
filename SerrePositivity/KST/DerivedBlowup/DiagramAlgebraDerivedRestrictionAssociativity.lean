module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedRestrictionCoherence
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraRestrictionUnits

/-!
概要：KST §3.1 の標準局所導来制限同型の結合整合性。
方針：主局所化前の加群上で等式を判定し、標準加群制限同型の結合条件を送る。
規約：四頂点の二つの標準合成経路を自然変換の等式として比較する。
使われ方：局所導来制限の擬関手の整合性。
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
-- 四頂点の導来制限と主局所化前の標準合成同型を照合するために必要。
/-- 概要：標準局所導来制限合成同型は四頂点の結合整合性を満たす。
方針：実加群上で成分を計算し、証明済み加群段階の結合条件を主局所化で送る。
規約：KST §3.1。使われ方：局所導来制限の擬関手の合成条件。 -/
theorem diagramAlgebraDerivedRestrictionCompIso_assoc {i j k l : J}
    (h : i ≤ j) (g : j ≤ k) (t : k ≤ l) :
    whiskerLeft (diagramAlgebraDerivedRestriction F t)
        (diagramAlgebraDerivedRestrictionCompIso F h g).hom ≫
        (diagramAlgebraDerivedRestrictionCompIso F (h.trans g) t).hom =
      whiskerRight (diagramAlgebraDerivedRestrictionCompIso F g t).hom
        (diagramAlgebraDerivedRestriction F h) ≫
        (diagramAlgebraDerivedRestrictionCompIso F h (g.trans t)).hom := by
  apply moduleDerivedNatTrans_ext R (AlgebraVertex (F.obj l))ᵒᵖ
  intro M
  change (diagramAlgebraDerivedRestrictionCompIso F h g).hom.app
      ((moduleToDerived R (AlgebraVertex (F.obj k))ᵒᵖ).obj
        ((diagramAlgebraModuleRestriction F t).obj M)) ≫
      (diagramAlgebraDerivedRestrictionCompIso F (h.trans g) t).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj l))ᵒᵖ).obj M) =
    (diagramAlgebraDerivedRestriction F h).map
      ((diagramAlgebraDerivedRestrictionCompIso F g t).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj l))ᵒᵖ).obj M)) ≫
      (diagramAlgebraDerivedRestrictionCompIso F h (g.trans t)).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj l))ᵒᵖ).obj M)
  rw [diagramAlgebraDerivedRestrictionCompIso_hom_app_Q,
    diagramAlgebraDerivedRestrictionCompIso_hom_app_Q,
    diagramAlgebraDerivedRestrictionCompIso_hom_app_Q,
    diagramAlgebraDerivedRestrictionCompIso_hom_app_Q,
    transitionDerivedRestriction_map_Q]
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map)
      (diagramAlgebraRestrictionCompIso_assoc F h g t M)

end SerrePositivity.KST.DerivedBlowup
