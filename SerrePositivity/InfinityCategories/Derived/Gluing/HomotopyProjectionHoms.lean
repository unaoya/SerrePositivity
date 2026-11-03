module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LeftFactorHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.RightFactorHom
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! 因子への Hom 射影の擬同型から、同じ H⁰ Hom 写像の全単射を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R]

/-- 指定した一対の Hom の擬同型だけから、同じ H⁰ 射写像の全単射を得る。 -/
lemma dgGluingHomotopyMap_bijective_at {C : Type v} [DGCategory R C]
    {E : Type w} [DGCategory R E] (F : DGFunctor R C E)
    (x y : ClosedCategory R C) (hF : QuasiIso (F.map x y)) :
    Function.Bijective (fun f : (toHomotopy R C).obj x ⟶ (toHomotopy R C).obj y =>
      F.onHomotopy.map f) := by
  let := hF
  let e := homotopyHomologyEquiv R C x y
  let e' := homotopyHomologyEquiv R E (F.onClosed.obj x) (F.onClosed.obj y)
  let b := (asIso (homologyMap (F.map x y) 0)).toLinearEquiv.toEquiv
  let k := (e.trans b).trans e'.symm
  have hk : (fun f : (toHomotopy R C).obj x ⟶ (toHomotopy R C).obj y =>
      F.onHomotopy.map f) = k := by
    funext f
    apply e'.injective
    change homotopyHomologyEquiv R E (F.onClosed.obj x) (F.onClosed.obj y)
      (F.onHomotopy.map f) = e' (e'.symm (b (e f)))
    rw [e'.apply_symm_apply]
    exact F.homotopyHomologyEquiv_map_naturality f
  rw [hk]
  exact k.bijective

variable (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : DGGluingObject R C D M)
local notation "G" => DGGluingObject R C D M

/-- C 因子への Hom の H⁰ 比較。順写像は同じ左射影の射写像。 -/
def dgGluingLeftHomotopyHomEquiv (hY : dgGluingFactorIsZero R D Y.right) :
    ((toHomotopy R G).obj (ForgetEnrichment.of (Complex R) X) ⟶
      (toHomotopy R G).obj (ForgetEnrichment.of (Complex R) Y)) ≃
    ((toHomotopy R C).obj (ForgetEnrichment.of (Complex R) X.left) ⟶
      (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) Y.left)) :=
  Equiv.ofBijective (dgGluingLeft R C D M).onHomotopy.map
    (dgGluingHomotopyMap_bijective_at R (dgGluingLeft R C D M)
      (ForgetEnrichment.of (Complex R) X) (ForgetEnrichment.of (Complex R) Y)
      (dgGluingLeftHomMap_quasiIso_of_target_right_zero R C D M X Y hY))

/-- D 因子からの Hom の H⁰ 比較。順写像は同じ右射影の射写像。 -/
def dgGluingRightHomotopyHomEquiv (hX : dgGluingFactorIsZero R C X.left) :
    ((toHomotopy R G).obj (ForgetEnrichment.of (Complex R) X) ⟶
      (toHomotopy R G).obj (ForgetEnrichment.of (Complex R) Y)) ≃
    ((toHomotopy R D).obj (ForgetEnrichment.of (Complex R) X.right) ⟶
      (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) Y.right)) :=
  Equiv.ofBijective (dgGluingRight R C D M).onHomotopy.map
    (dgGluingHomotopyMap_bijective_at R (dgGluingRight R C D M)
      (ForgetEnrichment.of (Complex R) X) (ForgetEnrichment.of (Complex R) Y)
      (by
        rw [dgGluingRight_map]
        exact dgGluingRightHomMap_quasiIso_of_source_left_zero R C D M X Y hX))

end SerrePositivity.InfinityCategories
