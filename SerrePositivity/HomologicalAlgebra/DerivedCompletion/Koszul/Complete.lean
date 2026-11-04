module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import SerrePositivity.HomologicalAlgebra.KoszulCoordinateControl
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleResolution

/-! # Koszul の塔の完備化の導来完備性

## 概要

導来完備性が同型・シフト・完全三角形で閉じることを示し（`isComplete_triangle_middle` ほか）、各座標の零ホモトピーから各有限 Koszul 段の導来完備性を、局所化加群の K 射影分解で直積を検出して候補の対象 `koszulCompletionObject` の導来完備性を導く。

## 方針

局所化対象からの全次数の射の消滅を、導来圏の完全三角形の完全性へつなぐ。

## 規約

座標の正則性やねじれの有界性は仮定しない。旧 `Closure`・`KoszulStageComplete`・`TowerComplete`。

## 使われ方

`ComplexCompletion/Basic`、BhattScholze（`TowerComplete` の宣言）。
-/

@[expose] public noncomputable section

universe u

section ClosurePart

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

end ClosurePart

section KoszulStageCompletePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 環係数のKoszul複体は、零次数環にKoszul関手を適用した複体に等しい。 -/
theorem koszulComplex_eq_functor : ∀ {e : ℕ} (a : Fin e → R),
    koszulComplex a = (koszulFunctor a).obj
      ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
  | 0, _ => rfl
  | e + 1, a => by
    change CochainComplex.mappingCone (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) = _
    rw [koszulComplex_eq_functor]
    rfl

/-- Koszul複体の座標の作用は零ホモトピック。既存の係数複体版を再利用する。 -/
def koszulComplexCoordinateNullHomotopy {e : ℕ} (a : Fin e → R) (j : Fin e) :
    Homotopy (smulId (a j) (koszulComplex a)) 0 := by
  rw [koszulComplex_eq_functor]
  exact koszulCoordinateNullHomotopy a _ j

/-- 各冪の有限Koszul段は、その各座標に関して導来完備。 -/
theorem powerKoszulStage_isComplete {e : ℕ} (a : Fin e → R) (n : ℕ) (j : Fin e) :
    IsComplete R (a j) (DerivedCategory.Q.obj (powerKoszulTower R a n)) :=
  isComplete_Q_of_scalar_pow_nullHomotopic R (a j) _ n
    (koszulComplexCoordinateNullHomotopy R (fun i ↦ a i ^ n) j)

/-- 各冪のKoszulの任意の次数のホモロジーも、その各座標に関して導来完備。 -/
theorem powerKoszulStage_homology_isModuleComplete {e : ℕ} (a : Fin e → R)
    (n : ℕ) (j : Fin e) (q : ℤ) :
    IsModuleComplete R (a j) ((powerKoszulTower R a n).homology q) := by
  apply isModuleComplete_of_pow_smul_zero R (a j) _ n
  have h := (koszulComplexCoordinateNullHomotopy R (fun i ↦ a i ^ n) j).homologyMap_eq q
  rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  intro m
  exact congrArg (fun f ↦ f.hom m) h

end SerrePositivity.DerivedCompletion

end KoszulStageCompletePart

section TowerCompletePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 各複体の導来像が完備なら、実際の複体の直積の導来像も完備。 -/
theorem isComplete_Q_product (f : R) (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ n, IsComplete R f (DerivedCategory.Q.obj (K n))) :
    IsComplete R f (DerivedCategory.Q.obj (piObj K)) := by
  intro m a
  let P := moduleResolutionComplex R (ModuleCat.of R (Localization.Away f))
  let e := moduleResolutionDerivedIso R (ModuleCat.of R (Localization.Away f))
  have hzero : e.hom ≫ a = 0 := by
    apply Q_shiftedHom_eq_zero_of_product_projections R P K m
    intro n
    rw [assoc, hK n m (a ≫ (DerivedCategory.Q.map (Pi.π K n))⟦m⟧'), comp_zero]
  apply (cancel_epi e.hom).mp
  simpa only [comp_zero] using hzero

/-- 各段が導来完備なら、差分の錐のモデルによるホモトピー逆極限候補も導来完備。 -/
theorem isComplete_complexTowerHomotopyLimitObject_of_stages (f : R)
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (hK : ∀ n, IsComplete R f (DerivedCategory.Q.obj (K n))) :
    IsComplete R f (complexTowerHomotopyLimitObject R K t) :=
  isComplete_complexTowerHomotopyLimitObject R f K t (isComplete_Q_product R f K hK)

/-- Koszul完備化候補の実導来対象は、指定された各座標に関して導来完備。 -/
theorem koszulCompletionObject_isComplete {e : ℕ} (a : Fin e → R) (j : Fin e) :
    IsComplete R (a j) (koszulCompletionObject R a) :=
  isComplete_complexTowerHomotopyLimitObject_of_stages R (a j)
    (powerKoszulTower R a) (powerKoszulTransition R a)
    (fun n ↦ powerKoszulStage_isComplete R a n j)

end SerrePositivity.DerivedCompletion

end TowerCompletePart
