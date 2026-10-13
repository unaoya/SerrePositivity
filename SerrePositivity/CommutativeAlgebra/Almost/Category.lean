module

public import SerrePositivity.CommutativeAlgebra.Almost.Morphism
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-! # 冪等イデアルに関する almost 加群の圏

I で消える加群が Serre 類をなすことを I*I=I の下で証明し、
その核・余核を持つ写像を反転した実際の局所化圏を構成する。
対象の almost 同型はこの圏の同型であり、単一の線形写像の存在とは定義しない。
CLMST への適用では p^N を法としたイデアルの冪等性を別途供給する。
perfectoid ideal の一般的な冪等性や平坦性はこのモジュールで仮定していない。
-/

@[expose] public section
universe u
namespace SerrePositivity.Almost
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- イデアル I によって消える加群の対象の性質。 -/
def zeroObjects : ObjectProperty (ModuleCat.{u} R) := fun M ↦ IsAlmostZero I M

instance : (zeroObjects I).ContainsZero where
  exists_zero := by
    have : Subsingleton (0 : ModuleCat.{u} R) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
    exact ⟨0, isZero_zero _, IsAlmostZero.of_subsingleton I _⟩

instance : (zeroObjects I).IsClosedUnderSubobjects where
  prop_of_mono f _ hN :=
    IsAlmostZero.of_injective f.hom ((ModuleCat.mono_iff_injective _).mp inferInstance) hN

instance : (zeroObjects I).IsClosedUnderQuotients where
  prop_of_epi f _ hM :=
    IsAlmostZero.of_surjective f.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance) hM

variable [Fact (I * I = I)]

instance : (zeroObjects I).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ :=
    IsAlmostZero.of_exact (Fact.out : I * I = I) S.f.hom S.g.hom
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) h₁ h₃

instance : (zeroObjects I).IsSerreClass where

/-- almost 加群の圏：核と余核が I で消える射を反転する。 -/
abbrev ModuleCategory := (zeroObjects I).isoModSerre.Localization

/-- 加群から almost 加群への局所化関手。 -/
noncomputable abbrev localization : ModuleCat.{u} R ⥤ ModuleCategory I :=
  (zeroObjects I).isoModSerre.Q

noncomputable instance : PreservesFiniteLimits (localization I) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits (localization I) (zeroObjects I)

noncomputable instance : PreservesFiniteColimits (localization I) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits (localization I) (zeroObjects I)

/-- 対象が almost 圏で零であることと、I で消えることは同値。 -/
theorem isZero_localization_obj_iff (M : ModuleCat.{u} R) :
    IsZero ((localization I).obj M) ↔ IsAlmostZero I M :=
  ObjectProperty.SerreClassLocalization.isZero_obj_iff (localization I) (zeroObjects I) M

/-- almost 同型の対象は、局所化圏での同型として定義する。
原典の M^a≃N^a を単一の写像の kernel/cokernel 条件へ弱めない。 -/
def IsIsomorphic (M N : ModuleCat.{u} R) : Prop :=
  Nonempty ((localization I).obj M ≅ (localization I).obj N)

/-- almost 圏で同型になる写像は、核と余核が I で消える写像にちょうど一致する。 -/
theorem isIso_localization_map_iff {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    IsIso ((localization I).map f) ↔ (zeroObjects I).isoModSerre f :=
  ObjectProperty.SerreClassLocalization.isIso_map_iff (localization I) (zeroObjects I) f

/-- categorical な核・余核の条件と、線形写像の almost 同型条件は一致する。 -/
theorem isoModSerre_iff_isAlmostIso {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (zeroObjects I).isoModSerre f ↔ IsAlmostIso I f.hom := by
  change IsAlmostZero I (kernel f : ModuleCat.{u} R) ∧
    IsAlmostZero I (cokernel f : ModuleCat.{u} R) ↔
    IsAlmostZero I f.hom.ker ∧ IsAlmostZero I (N ⧸ f.hom.range)
  exact and_congr
    (IsAlmostZero.equiv_iff (ModuleCat.kernelIsoKer f).toLinearEquiv)
    (IsAlmostZero.equiv_iff (ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv)

/-- 線形写像の核・余核条件は、almost 局所化関手で写像が同型になることと同値。 -/
theorem isIso_localization_map_iff_isAlmostIso {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    IsIso ((localization I).map f) ↔ IsAlmostIso I f.hom :=
  (isIso_localization_map_iff I f).trans (isoModSerre_iff_isAlmostIso I f)

/-- almost 同型の写像は、almost 圏で対象の同型を与える。 -/
theorem isIsomorphic_of_isoModSerre {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : (zeroObjects I).isoModSerre f) : IsIsomorphic I M N := by
  have : IsIso ((localization I).map f) := (isIso_localization_map_iff I f).mpr hf
  exact ⟨asIso ((localization I).map f)⟩

end SerrePositivity.Almost
