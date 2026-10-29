module

public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import SerrePositivity.LinearAlgebra.BasisSaturation

/-! # 代数的な整域拡大の基底を分数体へ移す

元の基底の像の独立性はMathlibの局所化の一般論から得る。
生成性は代数的な分母を底環へ移す一般論から得る。
Noether性・局所性・分離性は要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Map
variable {A D : Type*} [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]

/-- 指定した単射を、そのまま分数体の写像へ延長する。 -/
def fractionRingMap (f : A →+* D) (hf : Function.Injective f) :
    FractionRing A →+* FractionRing D :=
  IsFractionRing.lift (K := FractionRing A)
    (g := (algebraMap D (FractionRing D)).comp f)
    ((IsFractionRing.injective D (FractionRing D)).comp hf)

@[simp] theorem fractionRingMap_algebraMap (f : A →+* D) (hf : Function.Injective f) (a : A) :
    fractionRingMap f hf (algebraMap A (FractionRing A) a) =
      algebraMap D (FractionRing D) (f a) :=
  IsFractionRing.lift_algebraMap _ _

/-- 延長した写像そのものによる分数体上の係数作用。 -/
@[instance_reducible] def fractionRingMapModule (f : A →+* D) (hf : Function.Injective f) :
    Module (FractionRing A) (FractionRing D) :=
  @Algebra.toModule _ _ _ _ (fractionRingMap f hf).toAlgebra

/-- 指定した環写像の合成と分数体への延長は両立する。 -/
theorem fractionRingMap_comp {B : Type*} [CommRing B] [IsDomain B]
    (f : D →+* B) (hf : Function.Injective f)
    (g : A →+* D) (hg : Function.Injective g) :
    fractionRingMap (f.comp g) (hf.comp hg) =
      (fractionRingMap f hf).comp (fractionRingMap g hg) := by
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  simp only [fractionRingMap_algebraMap, RingHom.comp_apply]

end Map

/-- 基底に1が含まれる環拡大では、底環の像は非零スカラーについて飽和。 -/
theorem mem_range_algebraMap_of_smul_mem_of_basis_one
    {A D ι : Type*} [CommRing A] [IsDomain A] [CommRing D] [Algebra A D]
    (B : Module.Basis ι A D) (i : ι) (hi : B i = 1)
    {a : A} (ha : a ≠ 0) {d : D} (hd : a • d ∈ Set.range (algebraMap A D)) :
    d ∈ Set.range (algebraMap A D) := by
  obtain ⟨c, hc⟩ := hd
  have hx : a • d ∈ A ∙ B i := by
    apply Submodule.mem_span_singleton.mpr
    exact ⟨c, by simpa only [hi, Algebra.smul_def, mul_one] using hc⟩
  have hd := basis_mem_span_image_of_smul_mem B {i}
    (fun _ h ↦ (mul_eq_zero.mp h).resolve_left ha) (by simpa using hx)
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp (by simpa using hd)
  exact ⟨u, by simpa only [hi, Algebra.smul_def, mul_one] using hu⟩

/-- 基底に1を持つ整域拡大では、底環の分数体の像と元の環の交わりは底環の像。 -/
theorem algebraMap_mem_fractionRingMap_fieldRange_iff_of_basis_one
    {A D ι : Type*} [CommRing A] [IsDomain A] [CommRing D] [IsDomain D] [Algebra A D]
    (hf : Function.Injective (algebraMap A D)) (B : Module.Basis ι A D)
    (i : ι) (hi : B i = 1) (d : D) :
    algebraMap D (FractionRing D) d ∈ (fractionRingMap (algebraMap A D) hf).fieldRange ↔
      d ∈ Set.range (algebraMap A D) := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A z
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hEq : algebraMap D (FractionRing D) d =
        algebraMap D (FractionRing D) (algebraMap A D a) /
          algebraMap D (FractionRing D) (algebraMap A D b) := by
      simpa only [map_div₀, fractionRingMap_algebraMap] using hz.symm
    have hb' : algebraMap D (FractionRing D) (algebraMap A D b) ≠ 0 := by
      intro h
      apply hb0
      apply hf
      apply IsFractionRing.injective D (FractionRing D)
      simpa only [map_zero] using h
    have hmul : algebraMap A D b * d = algebraMap A D a := by
      apply IsFractionRing.injective D (FractionRing D)
      simpa only [map_mul, mul_comm] using (eq_div_iff hb').mp hEq
    apply mem_range_algebraMap_of_smul_mem_of_basis_one B i hi hb0
    exact ⟨a, by simpa only [Algebra.smul_def] using hmul.symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨algebraMap A (FractionRing A) a, fractionRingMap_algebraMap _ _ _⟩

/-- 代数的な整域拡大では、元の環の像が分数体を底環の分数体上張る。 -/
theorem span_range_fractionRing_eq_top
    (A D K L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    [Field K] [Field L] [Algebra A D] [Algebra.IsAlgebraic A D]
    [Algebra A K] [IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L] [IsScalarTower A D L] [IsScalarTower A K L] :
    Submodule.span K (Set.range (algebraMap D L)) = ⊤ := by
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hh := IsFractionRing.ideal_span_singleton_map_subset (R := A) (S := D) (K := K) (L := L)
    (a := 1) (b := Set.univ) hinj (by simp)
  apply top_unique
  intro x _
  have hx : x ∈ (Ideal.span {(algebraMap D L) 1} : Ideal L) := by simp
  simpa only [Set.image_univ, SetLike.mem_coe] using hh hx

open scoped TensorProduct

/-- 有限な整域拡大の分数体拡大は有限次元である。
有限加群の係数拡大から分数体への全射を、元の環の像が張ることから構成する。 -/
theorem finiteDimensional_fractionRing_of_finite
    (A D K L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    [Field K] [Field L] [Algebra A D] [Module.Finite A D]
    [Algebra A K] [IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L] [IsScalarTower A D L] [IsScalarTower A K L] :
    FiniteDimensional K L := by
  let f : K ⊗[A] D →ₐ[K] L := Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId K L) (IsScalarTower.toAlgHom A D L)
  apply Module.Finite.of_surjective f.toLinearMap
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← span_range_fractionRing_eq_top A D K L]
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  refine ⟨1 ⊗ₜ[A] d, ?_⟩
  change algebraMap K L 1 * algebraMap D L d = _
  rw [map_one, one_mul]

/-- 有限単射の同じ写像を分数体へ延長して得る有限拡大。
自己作用と混同しないよう、加群構造を指定した写像から取る。 -/
theorem fractionRingMap_finite {A D : Type*}
    [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    (f : A →+* D) (hf : Function.Injective f) (hfin : f.Finite) :
    letI : Algebra (FractionRing A) (FractionRing D) := (fractionRingMap f hf).toAlgebra
    letI : Module (FractionRing A) (FractionRing D) := fractionRingMapModule f hf
    Module.Finite (FractionRing A) (FractionRing D) := by
  let : Algebra A D := f.toAlgebra
  let : Module A D := @Algebra.toModule _ _ _ _ f.toAlgebra
  let : Module.Finite A D := hfin
  let : Algebra A (FractionRing D) := ((algebraMap D (FractionRing D)).comp f).toAlgebra
  let : SMul D (FractionRing D) := (inferInstance : Algebra D (FractionRing D)).toSMul
  let : SMul A (FractionRing D) := (inferInstance : Algebra A (FractionRing D)).toSMul
  let : IsScalarTower A D (FractionRing D) := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (FractionRing A) (FractionRing D) := (fractionRingMap f hf).toAlgebra
  let : Module (FractionRing A) (FractionRing D) := fractionRingMapModule f hf
  let : IsScalarTower A (FractionRing A) (FractionRing D) :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (fractionRingMap_algebraMap f hf a).symm)
  exact finiteDimensional_fractionRing_of_finite A D (FractionRing A) (FractionRing D)

section Basis
variable {A D K L α : Type*} [CommRing A] [instDomainA : IsDomain A]
  [CommRing D] [instDomainD : IsDomain D] [Field K] [Field L] [Algebra A D]
  [instAlgebraic : Algebra.IsAlgebraic A D] [instAK : Algebra A K]
  [instFracAK : IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
  [Algebra A L] [Algebra K L] [IsScalarTower A D L] [instTowerAKL : IsScalarTower A K L]

/-- 代数的な整域拡大の指定基底は、そのまま分数体の指定基底になる。 -/
def fractionRingBasisOfAlgebraic (B : Module.Basis α A D) : Module.Basis α K L := by
  have hli : LinearIndependent A (fun i ↦ algebraMap D L (B i)) :=
    B.linearIndependent.map' (IsScalarTower.toAlgHom A D L).toLinearMap
      (LinearMap.ker_eq_bot_of_injective (IsFractionRing.injective D L))
  have hliK : LinearIndependent K (fun i ↦ algebraMap D L (B i)) :=
    hli.localization K (nonZeroDivisors A)
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hspan : (Ideal.span ({1} : Set D) : Set D) ⊆
      Submodule.span A (Set.range B) := by rw [B.span_eq]; exact Set.subset_univ _
  have hh := IsFractionRing.ideal_span_singleton_map_subset (R := A) (S := D) (K := K) (L := L)
    (a := 1) (b := Set.range B) hinj hspan
  apply Module.Basis.mk hliK
  intro x _
  have hx : x ∈ (Ideal.span {(algebraMap D L) 1} : Ideal L) := by simp
  simpa only [← Set.range_comp, Function.comp_def, SetLike.mem_coe] using hh hx

@[simp] theorem fractionRingBasisOfAlgebraic_apply (B : Module.Basis α A D) (i : α) :
    fractionRingBasisOfAlgebraic (K := K) (L := L) B i = algebraMap D L (B i) := by
  simp only [fractionRingBasisOfAlgebraic, Module.Basis.mk_apply]

include instDomainA instDomainD instAlgebraic instAK instFracAK instTowerAKL in
/-- 有限な指定基底の大きさは、分数体へ移しても変わらない。 -/
theorem finrank_fractionRing_eq_natCard_basis [Finite α] (B : Module.Basis α A D) :
    Module.finrank K L = Nat.card α := by
  classical
  let : Fintype α := Fintype.ofFinite α
  rw [Module.finrank_eq_card_basis (fractionRingBasisOfAlgebraic (K := K) (L := L) B),
    Nat.card_eq_fintype_card]

end Basis

/-- 体の写像による作用と、その実際の像の部分体による作用は同じ拡大次数を持つ。 -/
theorem finrank_fieldRange {E L : Type*} [Field E] [Field L] (f : E →+* L) :
    letI : Algebra E L := f.toAlgebra
    letI : Module E L := @Algebra.toModule _ _ _ _ f.toAlgebra
    Module.finrank f.fieldRange L = Module.finrank E L := by
  let : Algebra E L := f.toAlgebra
  let : Module E L := @Algebra.toModule _ _ _ _ f.toAlgebra
  exact (Algebra.finrank_eq_of_equiv_equiv f.rangeRestrictFieldEquiv (RingEquiv.refl L)
    (by ext x; rfl)).symm

/-- 有限単射の延長の実際の像の部分体上でも、分数体は有限次元。 -/
theorem fractionRingMap_fieldRange_finite {A D : Type*}
    [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    (f : A →+* D) (hf : Function.Injective f) (hfin : f.Finite) :
    Module.Finite (fractionRingMap f hf).fieldRange (FractionRing D) := by
  apply Module.finite_of_finrank_pos
  rw [finrank_fieldRange]
  let : Algebra (FractionRing A) (FractionRing D) := (fractionRingMap f hf).toAlgebra
  let : Module (FractionRing A) (FractionRing D) := fractionRingMapModule f hf
  let : Module.Finite (FractionRing A) (FractionRing D) := fractionRingMap_finite f hf hfin
  exact Module.finrank_pos

end SerrePositivity
