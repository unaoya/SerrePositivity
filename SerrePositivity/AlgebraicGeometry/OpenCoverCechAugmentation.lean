module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechAcyclic
public import SerrePositivity.AlgebraicGeometry.CechZeroCochains

/-!
概要：開被覆の Čech の共通の増大項を、大域切断として明示する。
方針：空タプルの項を大域切断と同定し、長さ一への写像を制限の対角とする。
規約：異なる被覆でも増大項は同じ前層の全空間での値。
使われ方：細分写像の cone に、増大項を保つ射の完全性判定を適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
open scoped BigOperators
section Basic
universe u v w
variable {X : Type u} [TopologicalSpace X] {R : Type w} [CommRing R]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
variable (U : ι → Opens X)

/-- 開被覆の空タプルの項と、大域切断の同型。 -/
def openCoverCechZeroEquiv : FullCechCochains (openCoverCechDiagram P U) 0 ≃ₗ[R] P.obj (op ⊤) :=
  (LinearEquiv.piCongrRight (fun t : Fin 0 → ι ↦
    (P.mapIso (eqToIso (congrArg op (show cechOpenIntersection U (cechTupleSupport t) = ⊤ by
      rw [cechTupleSupport_empty]
      simp [cechOpenIntersection])))).toLinearEquiv)).trans
    (LinearEquiv.funUnique (Fin 0 → ι) R (P.obj (op ⊤)))

/-- 大域切断を空タプルの項へ戻すと、その交叉への制限になる。 -/
theorem openCoverCechZeroEquiv_symm_apply (x : P.obj (op ⊤)) (t : Fin 0 → ι) :
    (openCoverCechZeroEquiv P U).symm x t =
      (P.map (homOfLE (show cechOpenIntersection U (cechTupleSupport t) ≤ ⊤ from le_top)).op).hom x := by
  change (P.map _).hom x = (P.map _).hom x
  congr 2

/-- 大域切断から各被覆開の切断への対角の制限。 -/
def openCoverCechAugmentation : P.obj (op ⊤) →ₗ[R]
    FullCechCochains (openCoverCechDiagram P U) 1 :=
  LinearMap.pi fun t ↦
    (P.map (homOfLE (show cechOpenIntersection U (cechTupleSupport t) ≤ ⊤ from le_top)).op).hom

/-- 対角の制限は、空タプルの項からの Čech 微分と一致。 -/
theorem openCoverCechAugmentation_eq :
    (fullCechDifferential (openCoverCechDiagram P U) 0).comp
      (openCoverCechZeroEquiv P U).symm.toLinearMap = openCoverCechAugmentation P U := by
  apply LinearMap.ext
  intro x
  funext t
  change fullCechDifferential (openCoverCechDiagram P U) 0
      ((openCoverCechZeroEquiv P U).symm x) t = _
  let D := openCoverCechDiagram P U
  let a := (openCoverCechZeroEquiv P U).symm x
  let z : Fin 1 → D.obj (cechTupleSupport t) := fun i ↦
    (-1 : ℤ) ^ i.val • (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom
      (a (t ∘ i.succAbove))
  have hd : fullCechDifferential D 0 a t = ∑ i : Fin 1, z i :=
    fullCechDifferential_apply D 0 a t
  have hs : (∑ i : Fin 1, z i) = z 0 := Fin.sum_univ_one z
  calc
    _ = z 0 := hd.trans hs
    _ = (D.map (homOfLE (cechTupleSupport_face_subset t (0 : Fin 1)))).hom
        (a (t ∘ (0 : Fin 1).succAbove)) := by
      change (1 : ℤ) • _ = _
      exact one_smul ℤ _
    _ = _ := by
      change (P.map _).hom ((openCoverCechZeroEquiv P U).symm x
        (t ∘ (0 : Fin 1).succAbove)) = (P.map _).hom x
      rw [openCoverCechZeroEquiv_symm_apply]
      change (P.map _ ≫ P.map _).hom x = (P.map _).hom x
      rw [← P.map_comp]
      congr 2

/-- 対角の制限のあとに Čech 微分を適用すると零。 -/
theorem openCoverCechAugmentation_squared :
    (fullCechDifferential (openCoverCechDiagram P U) 1).comp
      (openCoverCechAugmentation P U) = 0 := by
  rw [← openCoverCechAugmentation_eq, ← LinearMap.comp_assoc,
    fullCechAugmentedDifferential_squared, LinearMap.zero_comp]

variable (V : κ → Opens X) (ρ : κ → ι) (hρ : ∀ i, V i ≤ U (ρ i))

/-- 細分の写像は、共通の大域切断からの増大写像を保つ。 -/
theorem openCoverCechRefinement_augmentation :
    (openCoverCechRefinementCochains P U V ρ hρ 1).comp
      (openCoverCechAugmentation P U) = openCoverCechAugmentation P V := by
  apply LinearMap.ext
  intro x
  funext t
  change (P.map _ ≫ P.map _).hom x = (P.map _).hom x
  rw [← P.map_comp]
  congr 2

end Basic

section Acyclic
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable {ι : Type} [LinearOrder ι]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) (U : ι → Opens X)

/-- 増大 Čech が完全なら、大域切断からの対角の制限は単射。 -/
theorem openCoverCechAugmentation_injective (h : OpenCoverCechAcyclic P U) :
    Function.Injective (openCoverCechAugmentation P U) := by
  rw [← openCoverCechAugmentation_eq]
  exact h.injective_zero.comp (openCoverCechZeroEquiv P U).symm.injective

/-- 増大 Čech の完全性は、大域切断からの対角の制限でも完全。 -/
theorem openCoverCechAugmentation_exact (h : OpenCoverCechAcyclic P U) :
    Function.Exact (openCoverCechAugmentation P U)
      (fullCechDifferential (openCoverCechDiagram P U) 1) := by
  rw [← openCoverCechAugmentation_eq]
  exact (openCoverCechZeroEquiv P U).symm.surjective.comp_exact_iff_exact.mpr (h.exact 0)

end Acyclic

end SerrePositivity.AlgebraicGeometry
