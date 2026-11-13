module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechResolution
public import SerrePositivity.AlgebraicGeometry.CechZeroCochains

/-!
概要：開被覆の増大 Čech 前層の零項を、元の前層と自然に同定する。
方針：空タプルの交叉は全空間であることと、一点添字の直積の同型を使う。
規約：この同型は開集合について自然で、被覆の完全性を仮定しない。
使われ方：二重図式の零番の行を、実際の細分写像へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat R) {κ : Type} [LinearOrder κ]
variable (V : κ → Opens X)

/-- 長さ零の被覆交叉を付けても、指定開集合は変わらない。 -/
theorem openCoverResolutionZeroIntersection (O : Opens X) (t : Fin 0 → κ) :
    O ⊓ cechOpenIntersection V (cechTupleSupport t) = O := by
  rw [cechTupleSupport_empty]
  simp [cechOpenIntersection]

/-- 増大 Čech 前層の零項と元の前層の、各開集合での同型。 -/
def openCoverCechResolutionZeroComponentIso (O : Opens X) :
    (openCoverCechResolution P V 0).obj (op O) ≅ P.obj (op O) := by
  let e : (∀ t : Fin 0 → κ,
      P.obj (op (O ⊓ cechOpenIntersection V (cechTupleSupport t)))) ≃ₗ[R]
      (Fin 0 → κ) → P.obj (op O) :=
    LinearEquiv.piCongrRight (fun t ↦ (P.mapIso
      (eqToIso (congrArg op (openCoverResolutionZeroIntersection V O t)))).toLinearEquiv)
  exact (e.trans (LinearEquiv.funUnique (Fin 0 → κ) R (P.obj (op O)))).toModuleIso

/-- 増大 Čech 前層の零項は、開集合について自然に元の前層と同型。 -/
def openCoverCechResolutionZeroIso : openCoverCechResolution P V 0 ≅ P :=
  NatIso.ofComponents (fun O ↦ openCoverCechResolutionZeroComponentIso P V O.unop) (by
    intro O O' h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (P.map _ ≫ P.map _).hom (a (default : Fin 0 → κ)) =
      (P.map _ ≫ P.map _).hom (a (default : Fin 0 → κ))
    rw [← P.map_comp, ← P.map_comp]
    congr 2)

end SerrePositivity.AlgebraicGeometry
