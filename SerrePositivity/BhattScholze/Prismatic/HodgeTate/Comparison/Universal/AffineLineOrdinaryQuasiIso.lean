module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinarySquares
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrientedFormsBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineDegrees
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryHomology

/-!
# 元のηの通常被覆像の擬同型性

## 概要
被覆上の標準HT同型を明示した入力として、元のηの通常係数拡大を検査する。

## 方針
零次・一次の元の正方形と、その外の同じ複体のホモロジーの零性を使う。

## 規約
元のηを選び直さず、始域の生成元をpに制限せず、一般結晶比較を入力にしない。

## 使われ方
HT04.R2から同じηの指定完備被覆像の判定への接続。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B))

/-- 特定の終域のHT同型の下で、元のηの同じ通常被覆像が擬同型になる。 -/
theorem affineLineOrdinaryBaseRealization_quasiIso
    (hHT : HodgeTateIsoStatement Q hQ 1)
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)
    (h0 : (affineLineFormalZeroIso P).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0))
    (h1 : (affineLineFormalOneIso P).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1)) :
    QuasiIso (affineLineOrdinaryBaseRealization f hP hQ hg η) := by
  let g := affineLineOrdinaryBaseRealization f hP hQ hg η
  have hb (i : ℕ) : Function.Bijective (affineBaseHTMap Q hQ 1 i) :=
    (affineBaseHTMap_bijective_iff Q hQ 1 i).mpr
      ((hodgeTateIsoStatement_iff_affineHTMap_bijective Q hQ 1).mp hHT i)
  have hzero : IsIso (homologyMap g 0) := by
    letI := Module.compHom (affineForms Q 1 0) (affineBaseToPolynomialMap Q 1)
    obtain ⟨e, he⟩ := exists_affineOrientedFormsBaseChangeEquiv 1 0 f hg
    haveI : IsIso (ModuleCat.ofHom (affineBaseHTMap Q hQ 1 0)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hb 0)
    haveI : IsIso ((affineLineFormalOrdinaryZeroIso P f.toRingHom).hom ≫
        homologyMap g 0 ≫ ((affineBaseComplex Q hQ 1).extendHomologyIso
          ComplexShape.embeddingUpNat (j := 0) (j' := (0 : ℤ)) rfl).hom) := by
      rw [affineLineOrdinaryBaseRealization_zero_square f hP hQ hg η h0 e he]
      change IsIso (e.toModuleIso.hom ≫ ModuleCat.ofHom (affineBaseHTMap Q hQ 1 0))
      infer_instance
    haveI := IsIso.of_isIso_comp_left (affineLineFormalOrdinaryZeroIso P f.toRingHom).hom
      (homologyMap g 0 ≫ ((affineBaseComplex Q hQ 1).extendHomologyIso
        ComplexShape.embeddingUpNat (j := 0) (j' := (0 : ℤ)) rfl).hom)
    exact IsIso.of_isIso_comp_right _ ((affineBaseComplex Q hQ 1).extendHomologyIso
      ComplexShape.embeddingUpNat (j := 0) (j' := (0 : ℤ)) rfl).hom
  have hone : IsIso (homologyMap g 1) := by
    letI := Module.compHom (affineForms Q 1 1) (affineBaseToPolynomialMap Q 1)
    obtain ⟨e, he⟩ := exists_affineOrientedFormsBaseChangeEquiv 1 1 f hg
    obtain ⟨v, hv, _⟩ := f.existsUnique_generator_unit
    have hbu : Function.Bijective (((v⁻¹ : Bˣ) : B) • affineBaseHTMap Q hQ 1 1) :=
      (LinearEquiv.smulOfUnit (M := (affineBaseComplex Q hQ 1).homology 1) v⁻¹).bijective.comp (hb 1)
    haveI : IsIso (ModuleCat.ofHom ((((v⁻¹ : Bˣ) : B) • affineBaseHTMap Q hQ 1 1) :
          affineForms Q 1 1 →ₗ[B] (affineBaseComplex Q hQ 1).homology 1)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbu
    haveI : IsIso ((affineLineFormalOrdinaryOneIso P f.toRingHom).hom ≫
        homologyMap g 1 ≫ ((affineBaseComplex Q hQ 1).extendHomologyIso
          ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl).hom) := by
      rw [affineLineOrdinaryBaseRealization_one_square f hP hQ hg η h1 v hv e he]
      change IsIso (e.toModuleIso.hom ≫
        ModuleCat.ofHom ((((v⁻¹ : Bˣ) : B) • affineBaseHTMap Q hQ 1 1) :
          affineForms Q 1 1 →ₗ[B] (affineBaseComplex Q hQ 1).homology 1))
      infer_instance
    haveI := IsIso.of_isIso_comp_left (affineLineFormalOrdinaryOneIso P f.toRingHom).hom
      (homologyMap g 1 ≫ ((affineBaseComplex Q hQ 1).extendHomologyIso
        ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl).hom)
    exact IsIso.of_isIso_comp_right _ ((affineBaseComplex Q hQ 1).extendHomologyIso
      ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl).hom
  rw [quasiIso_iff]
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
  by_cases hi0 : i = 0
  · subst i; exact hzero
  by_cases hi1 : i = 1
  · subst i; exact hone
  have hs := affineLineFormalOrdinary_homology_isZero P f.toRingHom i hi0 hi1
  have hK : IsZero ((affineHTTotalComplex Q hQ 1).homology i) := by
    by_cases hn : i < 0
    · exact affineHTTotal_homology_negative Q hQ 1 i hn
    · lift i to ℕ using (by omega : 0 ≤ i)
      exact affineHTTotal_homology_high_of_HT Q hQ hHT i (by omega)
  let U := ModuleCat.restrictScalars (affineBaseToPolynomialMap Q 1)
  have hL : IsZero ((affineComplexOnBase Q 1 (affineHTTotalComplex Q hQ 1)).homology i) :=
    (U.map_isZero hK).of_iso (((affineHTTotalComplex Q hQ 1).sc i).mapHomologyIso U)
  have ht : IsZero (((affineBaseComplex Q hQ 1).extend ComplexShape.embeddingUpNat).homology i) :=
    hL.of_iso ((homologyFunctor _ (.up ℤ) i).mapIso (affineOriginalBaseComplexIso Q hQ 1)).symm
  have he : homologyMap g i = (hs.iso ht).hom := hs.eq_of_src _ _
  rw [he]
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
