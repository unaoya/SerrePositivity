module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Exact.Basic

/-!
概要：長さ零のタプルの Čech 項を、空交叉の係数と同定する。
方針：空タプルの台の等式と、一点添字の直積の同型を使う。
規約：空交叉の係数は大域切断と一致するとは限らず、図式の空集合の値のまま扱う。
使われ方：開被覆の二重図式で、二つの被覆の共通の増大項を指定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- 空タプルの台は空集合。 -/
theorem cechTupleSupport_empty (t : Fin 0 → ι) : cechTupleSupport t = ∅ := by
  simp [cechTupleSupport]

/-- 長さ零の Čech 項と、係数図式の空集合の値の同型。 -/
def fullCechZeroCochainsEquiv (D : Finset ι ⥤ ModuleCat R) :
    FullCechCochains D 0 ≃ₗ[R] D.obj ∅ :=
  (LinearEquiv.piCongrRight (fun t : Fin 0 → ι ↦
    (D.mapIso (eqToIso (cechTupleSupport_empty t))).toLinearEquiv)).trans
      (LinearEquiv.funUnique (Fin 0 → ι) R (D.obj ∅))

/-- 空交叉の係数との同定は、係数図式の射に自然。 -/
theorem fullCechZeroCochainsEquiv_naturality
    {D E : Finset ι ⥤ ModuleCat R} (η : D ⟶ E) :
    (fullCechZeroCochainsEquiv E).toLinearMap.comp (fullCechCochainsMap η 0) =
      (η.app ∅).hom.comp (fullCechZeroCochainsEquiv D).toLinearMap := by
  apply LinearMap.ext
  intro a
  exact (congrArg (fun h ↦ h.hom (a (default : Fin 0 → ι)))
    (η.naturality (eqToHom (cechTupleSupport_empty (default : Fin 0 → ι))))).symm

/-- 増大項を空交叉の係数へ置き換えても、増大 Čech の完全性は同じ。 -/
theorem fullCechZeroCochainsEquiv_exact (D : Finset ι ⥤ ModuleCat R) :
    Function.Exact ((fullCechDifferential D 0).comp
        (fullCechZeroCochainsEquiv D).symm.toLinearMap) (fullCechDifferential D 1) ↔
      Function.Exact (fullCechDifferential D 0) (fullCechDifferential D 1) :=
  (fullCechZeroCochainsEquiv D).symm.surjective.comp_exact_iff_exact

end SerrePositivity.AlgebraicGeometry
