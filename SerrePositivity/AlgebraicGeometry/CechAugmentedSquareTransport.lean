module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareMap
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：Čech 四角形の二つの複体を同型で移し、全複体と完全性を同じ同型で比較する。
方針：基底と中心を固定し、実際の三つの辺を合成して四角形の射を作る。
規約：新しい完全性を仮定せず、元の acyclicity から移す。
使われ方：F8 の固定した斉次局所化の全複体を native な構造層の複体へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare
variable (s : CechAugmentedSquare.{u} R)
variable {C E : CochainComplex (ModuleCat.{u} R) ℕ} (eC : s.C ≅ C) (eE : s.E ≅ E)

/-- 基底と中心は固定し、二つの複体と実際の辺を同型で移す。 -/
def transport : CechAugmentedSquare.{u} R where
  C := C
  E := E
  restriction := eC.inv ≫ s.restriction ≫ eE.hom
  base := s.base
  centerBase := s.centerBase
  scalar := (eC.hom.f 0).hom.comp s.scalar
  quotient := s.quotient
  center := (eE.hom.f 0).hom.comp s.center
  scalar_cycle := by
    intro x
    have h := congrArg (fun m ↦ m.hom (s.scalar x)) (eC.hom.comm 0 1)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, s.scalar_cycle, map_zero] using h
  center_cycle := by
    intro x
    have h := congrArg (fun m ↦ m.hom (s.center x)) (eE.hom.comm 0 1)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, s.center_cycle, map_zero] using h
  commutes := by
    apply LinearMap.ext
    intro x
    have h := congrArg (fun m : s.C ⟶ s.C ↦ (m.f 0).hom (s.scalar x)) eC.hom_inv_id
    change (eC.inv.f 0).hom ((eC.hom.f 0).hom (s.scalar x)) = s.scalar x at h
    change (eE.hom.f 0).hom ((s.restriction.f 0).hom
      ((eC.inv.f 0).hom ((eC.hom.f 0).hom (s.scalar x)))) =
      (eE.hom.f 0).hom (s.center (s.quotient x))
    rw [h]
    exact congrArg (eE.hom.f 0).hom (LinearMap.congr_fun s.commutes x)

/-- 移送の実際の四角形の射。 -/
def transportMap : Map s (s.transport eC eE) where
  left := eC.hom
  right := eE.hom
  base := LinearMap.id
  center := LinearMap.id
  restriction := by simp [transport, Category.assoc]
  scalar := by simp [transport]
  quotient := by simp [transport]
  center_naturality := by simp [transport]

/-- 移送が誘導する全複体の各項の射は同型。 -/
theorem transportMap_totalComplexMap_component_isIso (n : ℕ) :
    IsIso ((s.transportMap eC eE).totalComplexMap.f n) := by
  cases n with
  | zero => exact (Iso.refl s.base).isIso_hom
  | succ n =>
    cases n with
    | zero =>
      exact (LinearEquiv.toModuleIso
        (((HomologicalComplex.Hom.isoApp eC 0).toLinearEquiv).prodCongr
          (LinearEquiv.refl R s.centerBase))).isIso_hom
    | succ n =>
      exact (LinearEquiv.toModuleIso
        (((HomologicalComplex.Hom.isoApp eE n).toLinearEquiv).prodCongr
          ((HomologicalComplex.Hom.isoApp eC (n + 1)).toLinearEquiv))).isIso_hom

/-- 二つの複体の同型は、増大項も含めた全複体の同型を与える。 -/
def transportTotalComplexIso : s.totalComplex ≅ (s.transport eC eE).totalComplex := by
  haveI (n : ℕ) : IsIso ((s.transportMap eC eE).totalComplexMap.f n) :=
    s.transportMap_totalComplexMap_component_isIso eC eE n
  haveI : IsIso (s.transportMap eC eE).totalComplexMap :=
    HomologicalComplex.Hom.isIso_of_components _
  exact asIso (s.transportMap eC eE).totalComplexMap

/-- 元の全複体が acyclic なら、同じ射による移送後の全複体も acyclic。 -/
theorem transport_acyclic (hs : s.totalComplex.Acyclic) :
    (s.transport eC eE).totalComplex.Acyclic := by
  let e := s.transportTotalComplexIso eC eE
  intro n
  exact (exactAt_iff_of_quasiIsoAt e.hom n).mp (hs n)

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
