module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AssociatedCompleteness
public import SerrePositivity.HomologicalAlgebra.Complex.Cone

/-!
# 生成元の向きの単位と元のスカラー錐

## 概要
a*u 倍の元の錐を、a 倍の錐へ零次数側の恒等射を保って移す。

## 方針
始域を u 倍、終域を恒等射とする元の矢の同型を、既存の錐関手で写す。

## 規約
単位 u を具体的な鎖写像に残す。通常商への射に使う終域の包含は保持する。

## 使われ方
Construction 6.1 の α(d)=p*u による正則商の比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HomologicalComplex CochainComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 元の複体上の単位 v 倍の自己同型。 -/
def scalarUnitSelfIso (v : Rˣ) (K : Complex R) : K ≅ K where
  hom := (v : R) • 𝟙 K
  inv := ((v⁻¹ : Rˣ) : R) • 𝟙 K
  hom_inv_id := by simp [Linear.smul_comp, Linear.comp_smul, smul_smul]
  inv_hom_id := by simp [Linear.smul_comp, Linear.comp_smul, smul_smul]

/-- 単位の向きの変更を、始域で u 倍し終域を保つ元の矢の同型で読む。 -/
def scalarConeOrientationArrow (a : R) (v : Rˣ) (K : Complex R) :
    Arrow.mk (SerrePositivity.smulId (a * (v : R)) K) ≅
      Arrow.mk (SerrePositivity.smulId a K) :=
  Arrow.isoMk (scalarUnitSelfIso v K) (Iso.refl K) (by
    simp [scalarUnitSelfIso, SerrePositivity.smulId, Linear.smul_comp,
      Linear.comp_smul, smul_smul, mul_comm])

/-- 元の a*u 倍の錐は、元の a 倍の錐と指定された鎖同型を持つ。 -/
def scalarConeOrientationIso (a : R) (v : Rˣ) (K : Complex R) :
    mappingCone (SerrePositivity.smulId (a * (v : R)) K) ≅
      mappingCone (SerrePositivity.smulId a K) :=
  homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by simp⟩) (scalarConeOrientationArrow a v K)

/-- 指定された錐の同型は、元の終域側の包含を保つ。 -/
theorem scalarConeOrientationIso_inr (a : R) (v : Rˣ) (K : Complex R) :
    mappingCone.inr (SerrePositivity.smulId (a * (v : R)) K) ≫ (scalarConeOrientationIso a v K).hom =
      mappingCone.inr (SerrePositivity.smulId a K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (mappingCone.inr _).f n ≫
    (SerrePositivity.cochainConeArrowMap _ _ (scalarConeOrientationArrow a v K).hom).f n = _
  rw [SerrePositivity.cochainConeArrowMap_inr]
  simp [scalarConeOrientationArrow]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
