module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrientedRowBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedRowUnits
public import SerrePositivity.HomologicalAlgebra.AlgebraScalarExtensionModule

/-!
# 元の向き付き行の標準通常係数射の同型性

## 概要
終域の生成元がpのとき、元の標準通常係数射は各行で同型となる。

## 方針
元の純テンソル上の式で、同じ元の射を検証済みの剰余行の代数同型と一致させる。

## 規約
対象間に同型が存在することだけから標準射の同型性を結論しない。

## 使われ方
HT04の標準半自由完備行の比較を、同じ係数射のsingleの同型へ接続する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B))
include hg

/-- 元の標準通常係数射は、終域が結晶的なとき各剰余行で同型。 -/
theorem affineBaseAnyOrdinaryCoefficientMap_app_isIso (r : ℕ) (n : SimplexCategory) :
    IsIso ((affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n) := by
  letI := f.toRingHom.toAlgebra
  letI : Algebra A ((reducedModel P hP r).obj n) :=
    ((affineBaseCoefficients P hP r).app n).hom.toAlgebra
  letI : Algebra B ((reducedModel Q hQ r).obj n) :=
    ((affineBaseCoefficients Q hQ r).app n).hom.toAlgebra
  obtain ⟨e, he⟩ := exists_affineOrientedRowBaseChangeEquiv f hP hQ hg r n
  let E : (ModuleCat.extendScalars f.toRingHom).obj ((affineBaseModules P hP r).obj n) ≅
      (affineBaseModules Q hQ r).obj n :=
    algebraScalarExtensionModuleIso A B ((affineBaseModules P hP r).obj n) ≪≫
      e.toLinearEquiv.toModuleIso
  have hE : (affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n = E.hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    erw [affineBaseAnyOrdinaryCoefficientMap_unit f hP hQ r n x]
    change (affineHTCoefficientReducedAny f hP hQ r).app n x =
      e ((algebraScalarExtensionModuleIso A B ((affineBaseModules P hP r).obj n)).hom
        ((1 : B) ⊗ₜ[A,f.toRingHom] x))
    erw [algebraScalarExtensionModuleIso_tmul]
    exact (he x).symm
  rw [hE]
  infer_instance

/-- 元の標準のsingle行の係数射も、同じ終域で各行ごとに同型。 -/
theorem affineAnyExtendedSingleRowsMap_app_isIso (r : ℕ) (n : SimplexCategory) :
    IsIso ((affineAnyExtendedSingleRowsMap f hP hQ r).app n) := by
  haveI := affineBaseAnyOrdinaryCoefficientMap_app_isIso f hP hQ hg r n
  change IsIso ((HTUniversalCrystallineInput.coefficientExtendedSingleRowsIso f.toRingHom
    (affineBaseModules P hP r)).hom.app n ≫
      (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).map
        ((affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n))
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
