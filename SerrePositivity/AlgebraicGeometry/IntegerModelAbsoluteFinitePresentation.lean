module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIntRingColimitFactor
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
概要：有限型 ℤ 上の局所有限表示模型を、終対象上の有限表示対象として扱う。
方針：同じ宇宙の ULift ℤ へ係数を移し、Spec ULift ℤ と終対象の同型を使う。
規約：スキームの宇宙を変えない。
使われ方：B03 の固定の平坦模型への射を有限係数段へ因子化する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 有限型 ℤ 上の局所有限表示模型は、終対象上でも局所有限表示。 -/
theorem locallyOfFinitePresentation_to_terminal_of_integer_model
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation p] :
    LocallyOfFinitePresentation (terminal.from Y) := by
  let Z := ULift.{u} ℤ
  let e : Z ≃+* ℤ := ULift.ringEquiv
  letI : IsNoetherianRing Z := isNoetherianRing_of_ringEquiv ℤ e.symm
  let f : CommRingCat.of Z ⟶ CommRingCat.of A :=
    CommRingCat.ofHom ((Int.castRingHom A).comp e.toRingHom)
  have hfA : (Int.castRingHom A).FiniteType := by
    rw [← show algebraMap ℤ A = Int.castRingHom A from Subsingleton.elim _ _]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hf : f.hom.FinitePresentation := RingHom.FinitePresentation.of_finiteType.mp
    (hfA.comp (RingHom.FiniteType.of_surjective e.toRingHom e.surjective))
  haveI : LocallyOfFinitePresentation (Spec.map f) :=
    (LocallyOfFinitePresentation.SpecMap_iff f).mpr hf
  let E := specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal
  have h : terminal.from Y = p ≫ Spec.map f ≫ E.hom := Subsingleton.elim _ _
  rw [h]
  infer_instance

end SerrePositivity.AlgebraicGeometry
