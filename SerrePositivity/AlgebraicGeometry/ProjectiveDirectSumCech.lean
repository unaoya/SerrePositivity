module

public import SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumFinitePi
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：有限個の標準開の Čech 複体は、係数の任意直和と項ごとに交換する。
方針：直和と有限積の線形同値を各項に使い、余境界の交代和との可換性を確かめる。
規約：添字は Type、係数の加群は基底環と同じ宇宙に置く。
使われ方：Rees 次数の直和と Čech コホモロジーの交換の、複体での比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory
open scoped DirectSum

universe u
variable {R : Type u} [CommRing R] {κ ι : Type} [DecidableEq κ] [DecidableEq ι] [Fintype ι]
variable (D : κ → Finset ι ⥤ ModuleCat.{u} R)

/-- 各有限交叉上で係数の直和を取った図式。 -/
def projectiveCechDirectSumDiagram : Finset ι ⥤ ModuleCat.{u} R where
  obj s := ModuleCat.of R (⨁ n, (D n).obj s)
  map f := ModuleCat.ofHom (DirectSum.lmap (fun n ↦ ((D n).map f).hom))
  map_id s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro n
    change ((D n).map (𝟙 s)).hom (x n) = x n
    rw [(D n).map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro n
    change ((D n).map (f ≫ g)).hom (x n) = _
    rw [(D n).map_comp]
    rfl

/-- 各 Čech 複体の項ごとの直和。 -/
def projectiveCechDirectSumComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of
    (fun q ↦ ModuleCat.of R (⨁ n, FullCechCochains (D n) (q + 1)))
    (fun q ↦ ModuleCat.ofHom (DirectSum.lmap (fun n ↦ fullCechDifferential (D n) (q + 1))))
    (by
      intro q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro n
      change fullCechDifferential (D n) (q + 2) (fullCechDifferential (D n) (q + 1) (x n)) = 0
      exact DFunLike.congr_fun (fullCechDifferential_squared (D n) q) (x n))

/-- 直和と有限なタプルの積を交換する、各 Čech 項の同値。 -/
def projectiveCechDirectSumTermLinearEquiv (k : ℕ) :
    (⨁ n, FullCechCochains (D n) k) ≃ₗ[R]
      FullCechCochains (projectiveCechDirectSumDiagram D) k :=
  projectiveDirectSumFinitePiLinearEquiv (R := R)
    (fun n (t : Fin k → ι) ↦ (D n).obj (cechTupleSupport t))

/-- 各項の比較は、有限な面の交代和と可換。 -/
theorem projectiveCechDirectSumTermLinearEquiv_differential (k : ℕ) :
    (projectiveCechDirectSumTermLinearEquiv D (k + 1)).toLinearMap.comp
      (DirectSum.lmap (fun n ↦ fullCechDifferential (D n) k)) =
        (fullCechDifferential (projectiveCechDirectSumDiagram D) k).comp
          (projectiveCechDirectSumTermLinearEquiv D k).toLinearMap := by
  apply LinearMap.ext
  intro x
  funext t
  apply DFinsupp.ext
  intro n
  change fullCechDifferential (D n) k (x n) t =
    (DirectSum.component R κ (fun j ↦ (D j).obj (cechTupleSupport t)) n)
      (fullCechDifferential (projectiveCechDirectSumDiagram D) k
        (projectiveCechDirectSumTermLinearEquiv D k x) t)
  rw [fullCechDifferential_apply, fullCechDifferential_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  rfl

/-- 係数の直和の Čech 複体と、Čech 複体の項ごとの直和の同型。 -/
def projectiveCechDirectSumComplexIso :
    projectiveCechDirectSumComplex D ≅ fullCechComplex (projectiveCechDirectSumDiagram D) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (projectiveCechDirectSumTermLinearEquiv D (q + 1)).toModuleIso) (by
      intro i j hij
      have h : i + 1 = j := hij
      subst j
      change ModuleCat.ofHom (projectiveCechDirectSumTermLinearEquiv D (i + 1)).toLinearMap ≫
          (fullCechComplex (projectiveCechDirectSumDiagram D)).d i (i + 1) =
        (projectiveCechDirectSumComplex D).d i (i + 1) ≫
          ModuleCat.ofHom (projectiveCechDirectSumTermLinearEquiv D (i + 2)).toLinearMap
      simp only [projectiveCechDirectSumComplex, fullCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
        (projectiveCechDirectSumTermLinearEquiv_differential D (i + 1)).symm)

end SerrePositivity.AlgebraicGeometry
