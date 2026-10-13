module

public import SerrePositivity.CommutativeAlgebra.Almost.TorsionCategory
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # 全加群の almost 同型と冪ねじれ部分圏の比較

全加群の Serre 局所化で同型な冪ねじれ加群を、冪ねじれの中間加群への二つの
almost 同型写像で比較する。中間対象は分数表示の二つの像の和に取る。
これにより、全加群での almost 同型から長さの定義域での局所化同型へ戻れる。
-/

@[expose] public section
universe u
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
