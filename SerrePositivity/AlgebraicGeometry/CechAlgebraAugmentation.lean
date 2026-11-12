module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraH0
public import SerrePositivity.AlgebraicGeometry.CechZeroCochains

/-!
概要：空交叉の切断から適合する切断の部分代数への実際の増大写像。
方針：各有限交叉への制限を取り、関手律で適合性を示す。
規約：基底環からの写像は部分代数のスカラー写像そのもの。
使われ方：次数零の余核と、Čech の増大写像の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type u} {ι : Type v} [CommRing R] [DecidableEq ι]
variable (D : Finset ι ⥤ CommAlgCat.{u} R)

/-- 空交叉から長さ1の各交叉への実際の制限。 -/
def fullAlgebraCechAugmentationCochains : D.obj ∅ →ₐ[R]
    FullRingCechCochains (algebraCechRingDiagram D) 1 where
  toFun x t := (D.map (homOfLE (Finset.empty_subset (cechTupleSupport t)))).hom x
  map_one' := by funext t; exact map_one _
  map_mul' x y := by funext t; exact map_mul _ _ _
  map_zero' := by funext t; exact map_zero _
  map_add' x y := by funext t; exact map_add _ _ _
  commutes' r := by funext t; exact AlgHom.commutes _ r

/-- 大域側から制限した切断族は適合する。 -/
theorem fullAlgebraCechAugmentation_mem (x : D.obj ∅) :
    fullAlgebraCechAugmentationCochains D x ∈ fullAlgebraCechEqualizer D := by
  change fullAlgebraCechFace D 0 _ = fullAlgebraCechFace D 1 _
  funext t
  change (D.map _).hom ((D.map _).hom x) = (D.map _).hom ((D.map _).hom x)
  change (D.map _ ≫ D.map _).hom x = (D.map _ ≫ D.map _).hom x
  rw [← D.map_comp, ← D.map_comp]
  congr 2

/-- 適合する切断の部分代数への実際の増大写像。 -/
def fullAlgebraCechAugmentation : D.obj ∅ →ₐ[R] fullAlgebraCechEqualizer D :=
  (fullAlgebraCechAugmentationCochains D).codRestrict (fullAlgebraCechEqualizer D)
    (fullAlgebraCechAugmentation_mem D)

/-- 増大写像を経由した基底環の写像は、部分代数のスカラー写像そのもの。 -/
theorem fullAlgebraCechAugmentation_algebraMap (r : R) :
    fullAlgebraCechAugmentation D (algebraMap R (D.obj ∅) r) =
      algebraMap R (fullAlgebraCechEqualizer D) r :=
  (fullAlgebraCechAugmentation D).commutes r

/-- 空タプルへの戻しは、その台への実際の制限。 -/
theorem fullAlgebraCechZeroEquiv_symm_apply (x : D.obj ∅) (t : Fin 0 → ι) :
    (fullCechZeroCochainsEquiv (algebraCechModuleDiagram D)).symm x t =
      (D.map (eqToHom (cechTupleSupport_empty t).symm)).hom x := by
  change (D.map _).hom x = (D.map _).hom x
  congr 2

/-- 部分代数への増大の各成分は、既存の増大 Čech 微分の次数零と一致。 -/
theorem fullAlgebraCechAugmentation_eq_differential :
    (fullAlgebraCechAugmentationCochains D).toLinearMap =
      (fullCechDifferential (algebraCechModuleDiagram D) 0).comp
        (fullCechZeroCochainsEquiv (algebraCechModuleDiagram D)).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  funext t
  symm
  change fullCechDifferential (algebraCechModuleDiagram D) 0
    ((fullCechZeroCochainsEquiv (algebraCechModuleDiagram D)).symm x) t = _
  rw [fullCechDifferential_apply, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  change (D.map _).hom
    ((fullCechZeroCochainsEquiv (algebraCechModuleDiagram D)).symm x _) = (D.map _).hom x
  rw [fullAlgebraCechZeroEquiv_symm_apply]
  change (D.map _ ≫ D.map _).hom x = (D.map _).hom x
  rw [← D.map_comp]
  congr 2

/-- 増大 Čech が次数零で完全なら、実際の増大の像は適合する切断すべてを含む。 -/
theorem fullAlgebraCechAugmentation_surjective_of_exact
    (h : Function.Exact (fullCechDifferential (algebraCechModuleDiagram D) 0)
      (fullCechDifferential (algebraCechModuleDiagram D) 1)) :
    Function.Surjective (fullAlgebraCechAugmentation D) := by
  intro x
  have hx : x.val ∈ LinearMap.ker (fullCechDifferential (algebraCechModuleDiagram D) 1) :=
    Eq.mp (congrArg (fun N ↦ x.val ∈ N) (fullAlgebraCechEqualizer_toSubmodule D)) x.property
  obtain ⟨a, ha⟩ := (h x.val).mp hx
  let e := fullCechZeroCochainsEquiv (algebraCechModuleDiagram D)
  refine ⟨e a, Subtype.ext ?_⟩
  have he := LinearMap.congr_fun (fullAlgebraCechAugmentation_eq_differential D) (e a)
  exact he.trans ((congrArg (fullCechDifferential (algebraCechModuleDiagram D) 0)
    (e.symm_apply_apply a)).trans ha)

end SerrePositivity.AlgebraicGeometry
