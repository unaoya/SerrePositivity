module

public import SerrePositivity.AlgebraicGeometry.FullCechH0Kernel
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
概要：環係数の Čech 次数零の適合する切断を部分環として扱う。
方針：二つの面の制限を環準同型として構成し、その equalizer を取る。
規約：乗法は元の切断環の成分ごとの乗法。
使われ方：射影 Čech H⁰ の有限性を切断の環へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {ι : Type v} [DecidableEq ι]

/-- 環係数の全タプル Čech 項。 -/
abbrev FullRingCechCochains (D : Finset ι ⥤ CommRingCat.{u}) (k : ℕ) :=
  (t : Fin k → ι) → D.obj (cechTupleSupport t)

/-- 二重点での片側の制限。 -/
def fullRingCechFace (D : Finset ι ⥤ CommRingCat.{u}) (i : Fin 2) :
    FullRingCechCochains D 1 →+* FullRingCechCochains D 2 where
  toFun a t := (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom
    (a (t ∘ i.succAbove))
  map_one' := by funext t; exact map_one _
  map_mul' a b := by funext t; exact map_mul _ _ _
  map_zero' := by funext t; exact map_zero _
  map_add' a b := by funext t; exact map_add _ _ _

/-- 二つの制限が一致する Čech 次数零の部分環。 -/
def fullRingCechEqualizer (D : Finset ι ⥤ CommRingCat.{u}) :
    Subring (FullRingCechCochains D 1) :=
  (fullRingCechFace D 0).eqLocus (fullRingCechFace D 1)

/-- 部分環への所属は、各二重点での一致と同値。 -/
theorem mem_fullRingCechEqualizer (D : Finset ι ⥤ CommRingCat.{u})
    (a : FullRingCechCochains D 1) :
    a ∈ fullRingCechEqualizer D ↔ ∀ t : Fin 2 → ι,
      fullRingCechFace D 0 a t = fullRingCechFace D 1 a t := by
  exact funext_iff

end SerrePositivity.AlgebraicGeometry
