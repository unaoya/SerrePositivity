module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback

/-!
概要：スキームの同型に沿う、既存の構造層の Frobenius Čech 引き戻しは同型。
方針：切断環の app の同型を、既存の係数図式と Čech 関手へ渡す。
規約：元の引き戻しの射と逆像被覆を保つ。
使われ方：射影表示の同型を、実際の幾何の構造層の計算へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]

/-- スキームの同型に沿う元の app は、切断環の係数図式の同型。 -/
theorem schemeStructureRingPullbackCoefficient_isIso :
    IsIso (schemeStructureRingPullbackCoefficient f) := by
  have (O : Y.Opensᵒᵖ) : IsIso ((schemeStructureRingPullbackCoefficient f).app O) := by
    change IsIso (f.app O.unop)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

variable (p : ℕ) (hp : p.Prime)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable (hX : ∀ O, (p : X.presheaf.obj O) = 0)

/-- 同じ app の Frobenius 順極限は、同じ係数図式の同型。 -/
theorem schemeStructurePerfectPullbackCoefficient_isIso :
    IsIso (schemeStructurePerfectPullbackCoefficient f p hp hY hX) := by
  have := schemeStructureRingPullbackCoefficient_isIso f
  let e := frobeniusRingDiagramIso p hp hY
    (hE := fun O ↦ hX ((Opens.map f.base).op.obj O))
    (asIso (schemeStructureRingPullbackCoefficient f))
  change IsIso e.hom
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- 同型に沿う元の逆像 Čech の射そのものは、複体の同型。 -/
theorem schemeStructurePerfectCechPullbackMap_isIso {ι : Type} [DecidableEq ι]
    (U : ι → Y.Opens) : IsIso (schemeStructurePerfectCechPullbackMap f p hp hY hX U) := by
  have := schemeStructurePerfectPullbackCoefficient_isIso f p hp hY hX
  have (T : Finset ι) : IsIso ((openCoverCechCoefficientMap
      (schemeStructurePerfectPullbackCoefficient f p hp hY hX) U).app T) := by
    change IsIso ((schemeStructurePerfectPullbackCoefficient f p hp hY hX).app
      (Opposite.op (cechOpenIntersection U T)))
    infer_instance
  have : IsIso (openCoverCechCoefficientMap
      (schemeStructurePerfectPullbackCoefficient f p hp hY hX) U) :=
    NatIso.isIso_of_isIso_app _
  change IsIso (fullCechComplexFunctor.map (openCoverCechCoefficientMap
    (schemeStructurePerfectPullbackCoefficient f p hp hY hX) U) ≫
      (schemeCechPreimageComplexIso f (frobeniusRingDiagram X.presheaf p hp hX) U).hom)
  infer_instance

end SerrePositivity.AlgebraicGeometry
