module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # 導来完備性の同型・シフト・完全三角形に関する閉性

局所化対象からの全次数の射の消滅を、導来圏の完全三角形の完全性へ接続する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 同型な対象の導来完備性を移す。 -/
theorem isComplete_of_iso (f : R) {X Y : ConcreteDerivedCategory R} (e : X ≅ Y)
    (hX : IsComplete R f X) : IsComplete R f Y := by
  intro n a
  apply (cancel_mono (e.inv⟦n⟧')).mp
  simpa only [zero_comp] using hX n (a ≫ e.inv⟦n⟧')

/-- 導来完備性はシフトで保たれる。 -/
theorem isComplete_shift (f : R) {X : ConcreteDerivedCategory R}
    (hX : IsComplete R f X) (m : ℤ) : IsComplete R f (X⟦m⟧) := by
  intro n a
  apply (cancel_mono ((shiftFunctorAdd (ConcreteDerivedCategory R) m n).inv.app X)).mp
  simpa only [zero_comp] using hX (m + n)
    (a ≫ (shiftFunctorAdd (ConcreteDerivedCategory R) m n).inv.app X)

/-- 完全三角形の両端が導来完備なら、中項も導来完備。 -/
theorem isComplete_triangle_middle (f : R) (T : Triangle (ConcreteDerivedCategory R))
    (hT : T ∈ distTriang _) (h1 : IsComplete R f T.obj₁) (h3 : IsComplete R f T.obj₃) :
    IsComplete R f T.obj₂ := by
  intro n a
  let S := T⟦n⟧
  have hS := Triangle.shift_distinguished T hT n
  have ha : a ≫ S.mor₂ = 0 := h3 n _
  obtain ⟨b, hb⟩ := S.coyoneda_exact₂ hS a ha
  rw [hb, h1 n b, zero_comp]

/-- 完全三角形の最初の二項が導来完備なら、第三項も導来完備。 -/
theorem isComplete_triangle_third (f : R) (T : Triangle (ConcreteDerivedCategory R))
    (hT : T ∈ distTriang _) (h1 : IsComplete R f T.obj₁) (h2 : IsComplete R f T.obj₂) :
    IsComplete R f T.obj₃ := by
  intro n a
  let S := T⟦n⟧
  have hS := Triangle.shift_distinguished T hT n
  have ha : a ≫ S.mor₃ = 0 := isComplete_shift R f h1 n 1 _
  obtain ⟨b, hb⟩ := S.coyoneda_exact₃ hS a ha
  rw [hb, h2 n b, zero_comp]

/-- 二つの導来像が完備なら、その間の写像錐の導来像も完備。 -/
theorem isComplete_Q_mappingCone (f : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)
    (hK : IsComplete R f (DerivedCategory.Q.obj K))
    (hL : IsComplete R f (DerivedCategory.Q.obj L)) :
    IsComplete R f (DerivedCategory.Q.obj (CochainComplex.mappingCone φ)) := by
  let e := DerivedCategory.quotientCompQhIso (ModuleCat R)
  apply isComplete_of_iso R f (e.app (CochainComplex.mappingCone φ))
  apply isComplete_triangle_third R f
    (DerivedCategory.Qh.mapTriangle.obj (CochainComplex.mappingCone.triangleh φ))
    (DerivedCategory.Qh.map_distinguished _ (Cone.triangleh_distinguished φ))
  · exact isComplete_of_iso R f (e.symm.app K) hK
  · exact isComplete_of_iso R f (e.symm.app L) hL

/-- 直積の導来像が完備なら、差分の錐で作ったホモトピー逆極限候補も完備。 -/
theorem isComplete_complexTowerHomotopyLimitObject (f : R)
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (hK : IsComplete R f (DerivedCategory.Q.obj (piObj K))) :
    IsComplete R f (complexTowerHomotopyLimitObject R K t) := by
  apply isComplete_of_iso R f
    ((DerivedCategory.Q.commShiftIso (-1)).symm.app
      (CochainComplex.mappingCone (complexTowerDifference R K t)))
  exact isComplete_shift R f
    (isComplete_Q_mappingCone R f (complexTowerDifference R K t) hK hK) (-1)

end SerrePositivity.DerivedCompletion
