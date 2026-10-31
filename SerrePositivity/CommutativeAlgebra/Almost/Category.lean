module

public import SerrePositivity.CommutativeAlgebra.Almost.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Category
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # almost 加群の圏

## 概要

I * I = I のもとで I で消える加群が Serre 類をなすことを示し、その核・余核を持つ写像を反転した実際の局所化圏を作る。J のある冪で消える加群の圏を I で消える加群の Serre 類で割った圏（長さの加法性の定義域を保つ）も作り、全加群での almost 同型と冪ねじれ部分圏での同型を比べる。

## 方針

全加群の Serre 局所化で同型な冪ねじれ加群を、冪ねじれの中間加群（分数表示の二つの像の和）への二つの almost 同型写像で比べる。

## 規約

対象の almost 同型はこの圏の同型で、単一の線形写像の存在とは定義しない。CLMST への適用では p^N を法としたイデアルの冪等性を別に供給する。

## 使われ方

LengthAlgebra/Almost、CLMST の長さの比較。
-/

@[expose] public noncomputable section

universe u

section CategoryPart

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

end CategoryPart

section TorsionCategoryPart

namespace SerrePositivity.Almost
open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] (I J : Ideal R) [Fact (I * I = I)]

/-- 冪ねじれ加群の中で I により消える対象の性質。 -/
def torsionZeroObjects : ObjectProperty (PowTorsionModule J) :=
  (zeroObjects I).inverseImage (powTorsionModule J).ι

instance : (torsionZeroObjects I J).IsSerreClass := inferInstanceAs
  ((zeroObjects I).inverseImage (powTorsionModule J).ι).IsSerreClass

/-- J 冪ねじれ加群の almost 圏。I 零の核・余核を持つ射を反転する。 -/
abbrev TorsionModuleCategory := (torsionZeroObjects I J).isoModSerre.Localization

/-- 冪ねじれ加群の almost 局所化関手。 -/
noncomputable abbrev torsionLocalization :
    PowTorsionModule J ⥤ TorsionModuleCategory I J :=
  (torsionZeroObjects I J).isoModSerre.Q

noncomputable instance : PreservesFiniteLimits (torsionLocalization I J) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits
    (torsionLocalization I J) (torsionZeroObjects I J)

noncomputable instance : PreservesFiniteColimits (torsionLocalization I J) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits
    (torsionLocalization I J) (torsionZeroObjects I J)

/-- 冪ねじれ対象が almost 圏で零になることと、I で消えることは同値。 -/
theorem isZero_torsionLocalization_obj_iff (M : PowTorsionModule J) :
    IsZero ((torsionLocalization I J).obj M) ↔ IsAlmostZero I M.obj :=
  ObjectProperty.SerreClassLocalization.isZero_obj_iff
    (torsionLocalization I J) (torsionZeroObjects I J) M

/-- 冪ねじれ対象の almost 同型は局所化圏での同型を意味する。 -/
def IsTorsionIsomorphic (M N : PowTorsionModule J) : Prop :=
  Nonempty ((torsionLocalization I J).obj M ≅ (torsionLocalization I J).obj N)

end SerrePositivity.Almost

end TorsionCategoryPart

section SerreComparisonPart

namespace SerrePositivity.Almost
open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]

/-- 二つの冪ねじれ加群の写像の像の和は、再び一つのイデアル冪で消える。 -/
theorem isPowTorsion_sup_range (J : Ideal R) {M N Z : ModuleCat.{u} R}
    (f : M ⟶ Z) (g : N ⟶ Z) (hM : IsPowTorsion J M) (hN : IsPowTorsion J N) :
    IsPowTorsion J ↥(f.hom.range ⊔ g.hom.range : Submodule R Z) := by
  obtain ⟨a, ha⟩ := hM
  obtain ⟨b, hb⟩ := hN
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe] at ha hb
  refine ⟨a + b, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  intro r hr
  rw [Module.mem_annihilator]
  intro z
  apply Subtype.ext
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp z.property
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  change r • (z : Z) = 0
  rw [← hxy, smul_add, ← map_smul, ← map_smul]
  rw [Module.mem_annihilator.mp (ha (Ideal.pow_le_pow_right (Nat.le_add_right a b) hr)) m,
    Module.mem_annihilator.mp (hb (Ideal.pow_le_pow_right (Nat.le_add_left b a) hr)) n]
  simp

/-- almost 同型写像の終域を、その像を含む部分加群へ制限しても almost 同型である。 -/
theorem isAlmostIso_codRestrict (I : Ideal R) {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (hf : IsAlmostIso I f) (S : Submodule R N)
    (hS : ∀ m, f m ∈ S) : IsAlmostIso I (f.codRestrict S hS) := by
  constructor
  · rw [IsAlmostInjective.iff_smul_eq_zero]
    intro m hm r hr
    exact hf.1.smul_eq_zero m (congrArg Subtype.val hm) hr
  · rw [IsAlmostSurjective.iff_smul_mem_range]
    intro r hr n
    obtain ⟨m, hm⟩ := hf.2.smul_mem_range hr (n : N)
    exact ⟨m, Subtype.ext hm⟩

variable (I J : Ideal R) [Fact (I * I = I)]

/-- 全加群の almost 同型を、冪ねじれの中間対象への almost 同型の余スパンで表す。
単一の almost 同型写像の存在を同型の定義にすることはせず、分数表示から導く。 -/
theorem exists_torsion_cospan_of_iso (M N : PowTorsionModule J)
    (e : (localization I).obj M.obj ≅ (localization I).obj N.obj) :
    ∃ (U : PowTorsionModule J) (f : M ⟶ U) (g : N ⟶ U),
      IsAlmostIso I f.hom.hom ∧ IsAlmostIso I g.hom.hom := by
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction (localization I)
    (zeroObjects I).isoModSerre e.hom
  have hfmap : (localization I).map φ.f = e.hom ≫ (localization I).map φ.s := by
    rw [hφ]
    exact (φ.map_comp_map_s (localization I) (Localization.inverts _ _)).symm
  have : IsIso ((localization I).map φ.f) := by rw [hfmap]; infer_instance
  have hf := (isIso_localization_map_iff_isAlmostIso I φ.f).mp inferInstance
  have hg := (isoModSerre_iff_isAlmostIso I φ.s).mp φ.hs
  let S : Submodule R φ.Y' := φ.f.hom.range ⊔ φ.s.hom.range
  let U : PowTorsionModule J := ⟨ModuleCat.of R S,
    isPowTorsion_sup_range J φ.f φ.s M.property N.property⟩
  let f : M ⟶ U := ObjectProperty.homMk
    (ModuleCat.ofHom (φ.f.hom.codRestrict S
      (fun m ↦ (show φ.f.hom.range ≤ S from le_sup_left) ⟨m, rfl⟩)))
  let g : N ⟶ U := ObjectProperty.homMk
    (ModuleCat.ofHom (φ.s.hom.codRestrict S
      (fun n ↦ (show φ.s.hom.range ≤ S from le_sup_right) ⟨n, rfl⟩)))
  exact ⟨U, f, g,
    isAlmostIso_codRestrict I φ.f.hom hf S _,
    isAlmostIso_codRestrict I φ.s.hom hg S _⟩

/-- 部分圏の包含は核と余核を保つので、almost 同型写像の条件も一致する。 -/
theorem torsion_isoModSerre_iff_isAlmostIso {M N : PowTorsionModule J} (f : M ⟶ N) :
    (torsionZeroObjects I J).isoModSerre f ↔ IsAlmostIso I f.hom.hom := by
  have hk := IsAlmostZero.equiv_iff
    (PreservesKernel.iso (powTorsionModule J).ι f).toLinearEquiv (I := I)
  have hc := IsAlmostZero.equiv_iff
    (PreservesCokernel.iso (powTorsionModule J).ι f).toLinearEquiv (I := I)
  change IsAlmostZero I (kernel f).obj ↔
    IsAlmostZero I (kernel f.hom : ModuleCat.{u} R) at hk
  change IsAlmostZero I (cokernel f).obj ↔
    IsAlmostZero I (cokernel f.hom : ModuleCat.{u} R) at hc
  change (IsAlmostZero I (kernel f).obj ∧ IsAlmostZero I (cokernel f).obj) ↔ _
  exact (and_congr hk hc).trans (isoModSerre_iff_isAlmostIso I f.hom)

/-- 全加群の almost 局所化における同型は、冪ねじれ部分圏の局所化でも同型になる。 -/
theorem isTorsionIsomorphic_of_iso (M N : PowTorsionModule J)
    (e : (localization I).obj M.obj ≅ (localization I).obj N.obj) :
    IsTorsionIsomorphic I J M N := by
  obtain ⟨U, f, g, hf, hg⟩ := exists_torsion_cospan_of_iso I J M N e
  have : IsIso ((torsionLocalization I J).map f) :=
    Localization.inverts _ (torsionZeroObjects I J).isoModSerre f
      ((torsion_isoModSerre_iff_isAlmostIso I J f).mpr hf)
  have : IsIso ((torsionLocalization I J).map g) :=
    Localization.inverts _ (torsionZeroObjects I J).isoModSerre g
      ((torsion_isoModSerre_iff_isAlmostIso I J g).mpr hg)
  exact ⟨asIso ((torsionLocalization I J).map f) ≪≫
    (asIso ((torsionLocalization I J).map g)).symm⟩

/-- 全加群での almost 同型という命題から、冪ねじれ部分圏での同型を得る。 -/
theorem isTorsionIsomorphic_of_isIsomorphic (M N : PowTorsionModule J)
    (h : IsIsomorphic I M.obj N.obj) : IsTorsionIsomorphic I J M N := by
  obtain ⟨e⟩ := h
  exact isTorsionIsomorphic_of_iso I J M N e

end SerrePositivity.Almost

end SerreComparisonPart
