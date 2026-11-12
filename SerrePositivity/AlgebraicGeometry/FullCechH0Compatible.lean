module

public import SerrePositivity.AlgebraicGeometry.FullCechH0Kernel

/-!
概要：次数零の Čech 余境界を二つの制限の差として計算する。
方針：二つの面の有限和を展開する。
規約：通常の次数零は長さ1のタプル。
使われ方：適合する切断の部分環と Čech H⁰ の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- 最初の余境界は二つの制限の差。 -/
theorem fullCechDifferential_one_apply (D : Finset ι ⥤ ModuleCat R)
    (a : FullCechCochains D 1) (t : Fin 2 → ι) :
    fullCechDifferential D 1 a t =
      (D.map (homOfLE (cechTupleSupport_face_subset t 0))).hom (a (t ∘ (0 : Fin 2).succAbove)) -
      (D.map (homOfLE (cechTupleSupport_face_subset t 1))).hom (a (t ∘ (1 : Fin 2).succAbove)) := by
  simp [fullCechDifferential_apply, Fin.sum_univ_two, sub_eq_add_neg]

end SerrePositivity.AlgebraicGeometry
