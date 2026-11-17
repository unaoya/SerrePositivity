module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCanonicalComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalComponents

/-!
# 元のTot比較から標準完備増大への帰結

## 概要
元の通常Tot比較と終域の完備化単位が同型なら、標準完備Tot比較の同型性を標準増大へ戻す。

## 方針
同じ元の単位で指定した比較の一意性により、増大・通常Tot比較・行の単位へ分解する。

## 規約
対象の同型の存在から増大の同型性を推論しない。元の射の分解を証明する。

## 使われ方
元のηの終域の完備した半自由増大の擬同型性を検査する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
open DifferentialGraded DerivedCompletion DifferentialGraded.ScalarExtension HomologicalAlgebra
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の完備な対象の標準完備化単位の同型。 -/
def completeFiniteUnitIso {r : ℕ} (x : Fin r → S) (K : Complex S)
    (hc : ∀ j, IsComplete S (x j) (DerivedCategory.Q.obj K)) :
    DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj K) := by
  haveI := finiteCompletionUnit_isIso_of_isComplete x K hc
  exact asIso (DerivedCategory.Q.map (finiteCompletionUnit x K))

/-- 同じ元の完備比較は、完備した増大と終域の標準単位の逆から計算できる。 -/
theorem finiteCompletedComparison_factor_augmentation (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) {P : Complex R} (q : P ⟶ total K)
    (hc : ∀ j, IsComplete S (f (x j)) (DerivedCategory.Q.obj (baseChange f (total K)))) :
    finiteCompletedBaseChangeModelComparison f x K q =
      DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => f (x j))).map
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q)) ≫
      (completeFiniteUnitIso (fun j => f (x j)) (baseChange f (total K)) hc).inv ≫
      DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K (𝟙 _)) := by
  haveI := finiteCompletionUnit_isIso_of_isComplete (fun j => f (x j)) (baseChange f (total K)) hc
  apply finiteCompletionHom_ext (fun j => f (x j)) (baseChange f P)
    (DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x K)))
    (total_finiteCompletedRows_isComplete (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))
  rw [unit_comp_finiteCompletedBaseChangeModelComparison]
  have hu := congrArg DerivedCategory.Q.map (finiteCompletionUnit_naturality
    (fun j => f (x j)) (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q))
  simp only [Functor.map_comp] at hu
  rw [← Category.assoc, ← hu]
  simp only [Category.assoc, completeFiniteUnitIso, asIso_inv, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp]
  congr 1
  dsimp only [baseChangeModelToCompletedRows]
  rw [((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map_id]
  simp only [Category.id_comp]

/-- 元の標準完備比較が同型なら、同じ元の完備した増大が擬同型。 -/
theorem completedAugmentation_quasiIso_of_totalComparison (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) {P : Complex R} (q : P ⟶ total K)
    (hq : QuasiIso q) (hP : complexKFlat R P)
    (hc : ∀ j, IsComplete S (f (x j)) (DerivedCategory.Q.obj (baseChange f (total K))))
    [IsIso (canonicalCompletedBaseChangeComparison f x K)]
    [IsIso (baseChangeTotalComparison f K)]
    [QuasiIso ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
      (finiteCompletionRowsUnit (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K)))] :
    QuasiIso ((finiteCompletionFunctor (fun j => f (x j))).map
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q)) := by
  haveI := finiteCompletionUnit_isIso_of_isComplete (fun j => f (x j)) (baseChange f (total K)) hc
  haveI : IsIso (finiteCompletedBaseChangeModelComparison f x K q) := by
    have hh := nativeCompletedComparison_eq_canonical f x K q hq hP
    haveI : IsIso ((nativeCompletedScalarModelIso f x q hq hP).hom ≫
        finiteCompletedBaseChangeModelComparison f x K q) := by rw [hh]; infer_instance
    exact IsIso.of_isIso_comp_left (nativeCompletedScalarModelIso f x q hq hP).hom _
  haveI : IsIso (DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K (𝟙 _))) := by
    dsimp only [baseChangeModelToCompletedRows]
    rw [((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map_id]
    simp only [Category.id_comp, Functor.map_comp]
    infer_instance
  have hfactor := finiteCompletedComparison_factor_augmentation f x K q hc
  haveI : IsIso (DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => f (x j))).map
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q)) ≫
      (completeFiniteUnitIso (fun j => f (x j)) (baseChange f (total K)) hc).inv ≫
      DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K (𝟙 _))) := by
    rw [← hfactor]
    infer_instance
  haveI : IsIso (DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => f (x j))).map
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q))) :=
    IsIso.of_isIso_comp_right _
      ((completeFiniteUnitIso (fun j => f (x j)) (baseChange f (total K)) hc).inv ≫
        DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K (𝟙 _)))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} S) _).mp inferInstance

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
