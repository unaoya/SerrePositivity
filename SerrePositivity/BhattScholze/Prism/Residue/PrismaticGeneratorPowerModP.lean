module

public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticPowerResidueCanonical

/-! # 生成元冪商の標準mod p還元と二生成剰余

G9のA/(dⁿ)上の標準mod p商と、G10側のA/(p,dⁿ)を比較する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (p : ℕ) (d : A) (n : ℕ)
local notation "Iₙ" => Ideal.span (Set.singleton (d ^ n))
local notation "Jₙ" => Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Tₙ" => A ⧸ Iₙ
local notation "Qₙ" => A ⧸ Jₙ
local notation "qₙ" => Ideal.Quotient.mk Iₙ
local notation "qₚ" => Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ)))
local notation "q₀" => Ideal.Quotient.mk Jₙ

/-- 生成元冪商から二生成剰余への具体的標準射。 -/
def prismaticGeneratorPowerModPMap : Tₙ →+* Qₙ :=
  Ideal.quotientMap Jₙ (RingHom.id A) (by
    intro x hx
    change x ∈ Jₙ
    exact (Ideal.span_mono (Set.singleton_subset_iff.mpr
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) hx)

local notation "rₙ" => prismaticGeneratorPowerModPMap p d n

/-- 元のAからの標準射との可換性。 -/
theorem prismaticGeneratorPowerModPMap_comp : (rₙ).comp qₙ = q₀ := rfl

/-- 生成元冪商から二生成剰余への標準射は全射。 -/
theorem prismaticGeneratorPowerModPMap_surjective : Function.Surjective rₙ :=
  Ideal.quotientMap_surjective Function.surjective_id

/-- 標準射の核は、生成元冪商内のpの主イデアル。 -/
theorem prismaticGeneratorPowerModPMap_ker :
    RingHom.ker rₙ = Ideal.span {(p : Tₙ)} := by
  rw [prismaticGeneratorPowerModPMap, Ideal.quotientMap, Ideal.ker_quotient_lift]
  simp only [RingHom.comp_id, Ideal.mk_ker]
  have hd : qₙ (d ^ n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self _)
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      change qₙ (p : A) ∈ Ideal.span {(p : Tₙ)}
      rw [map_natCast]
      exact Ideal.mem_span_singleton_self _
    · obtain rfl := Set.mem_singleton_iff.mp hx
      change qₙ (d ^ n) ∈ Ideal.span {(p : Tₙ)}
      rw [hd]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    rw [← map_natCast qₙ p]
    exact Ideal.mem_map_of_mem qₙ (Ideal.subset_span (Set.mem_insert _ _))

/-- 標準mod p商は二生成剰余Qₙに同型。n=0も含む。 -/
def prismaticGeneratorPowerModPEquiv : Tₙ ⧸ Ideal.span {(p : Tₙ)} ≃+* Qₙ :=
  (Ideal.quotEquivOfEq (prismaticGeneratorPowerModPMap_ker p d n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (prismaticGeneratorPowerModPMap_surjective p d n))

local notation "eₙ" => prismaticGeneratorPowerModPEquiv p d n

/-- mod p商同型は具体的な標準剰余射を保つ。 -/
theorem prismaticGeneratorPowerModPEquiv_comp_mk : (eₙ).toRingHom.comp qₚ = rₙ := by
  apply RingHom.ext
  intro x
  rfl

/-- 商同型の逆は、標準剰余射をG9の標準mod p商射へ戻す。 -/
theorem prismaticGeneratorPowerModPEquiv_symm_comp :
    (eₙ).symm.toRingHom.comp rₙ = qₚ := by
  apply RingHom.ext
  intro x
  apply (eₙ).injective
  change (eₙ) ((eₙ).symm ((rₙ) x)) = (eₙ) ((qₚ) x)
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (prismaticGeneratorPowerModPEquiv_comp_mk p d n) x).symm

/-- 二段階mod p還元と二生成剰余を比較する複体上の同型。 -/
def prismaticGeneratorPowerModPCochainIso :
    (ModuleCat.extendScalars qₙ).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars qₚ).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars q₀).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.restrictScalars (eₙ).toRingHom).mapHomologicalComplex (.up ℤ) := by
  have h : (qₚ).comp qₙ = (eₙ).symm.toRingHom.comp q₀ := by
    rw [← prismaticGeneratorPowerModPEquiv_symm_comp p d n,
      RingHom.comp_assoc, prismaticGeneratorPowerModPMap_comp]
  let e : ModuleCat.extendScalars qₙ ⋙ ModuleCat.extendScalars qₚ ≅
      ModuleCat.extendScalars q₀ ⋙ ModuleCat.restrictScalars (eₙ).toRingHom :=
    (ModuleCat.extendScalarsComp qₙ qₚ).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars h) ≪≫
      ModuleCat.extendScalarsComp q₀ (eₙ).symm.toRingHom ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars q₀)
        (restrictScalarsIsoExtendInverse eₙ).symm
  exact Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars q₀ ⋙ ModuleCat.restrictScalars (eₙ).toRingHom))
      (.up ℤ)).symm

/-- G9の実標準mod p還元は、実Qₙ還元の商同型による係数制限と同型。 -/
def prismaticGeneratorPowerModPDerivedIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange qₚ).obj ((boundedAboveDerivedBaseChange qₙ).obj X) ≅
      (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).obj
        ((boundedAboveDerivedBaseChange q₀).obj X) :=
  ObjectProperty.isoMk _
    (boundedAboveDerivedBaseChangeModelIso qₚ ((boundedAboveDerivedBaseChange qₙ).obj X)
        (boundedAboveDerivedBaseChangeModel qₙ X) ≪≫
      DerivedCategory.Q.mapIso ((prismaticGeneratorPowerModPCochainIso p d n).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      ((derivedRestrictScalarsFactors (eₙ).toRingHom).app
        (baseChange q₀ (boundedAboveDerivedChosenModel X).complex)).symm ≪≫
      (derivedRestrictScalars (eₙ).toRingHom).mapIso
        (boundedAboveDerivedBaseChangeModelIso q₀ X (boundedAboveDerivedChosenModel X)).symm)

variable (X : DerivedCategory.Minus (ModuleCat.{u} A))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₚ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X)
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X

/-- 標準mod p実還元のホモロジーと、実二生成剰余の係数制限との同型。 -/
def prismaticGeneratorPowerModPHomologyIso (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Y₀).obj ≅
      (ModuleCat.restrictScalars (eₙ).toRingHom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Z₀).obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).mapIso
      (DerivedCategory.Minus.ι.mapIso (prismaticGeneratorPowerModPDerivedIso p d n X)) ≪≫
    (derivedRestrictScalarsHomologyIso (eₙ).toRingHom i).app (Z₀).obj

/-- 実二生成剰余の次数消滅は、G9の標準mod p実還元へ移る。 -/
theorem prismaticGeneratorPowerModP_homology_isZero (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Z₀).obj)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Y₀).obj) :=
  ((ModuleCat.restrictScalars (eₙ).toRingHom).map_isZero h).of_iso
    (prismaticGeneratorPowerModPHomologyIso p d n X i)

/-- 実二生成剰余のH0平坦性は、正確なmod p商環上のH0平坦性へ移る。 -/
theorem prismaticGeneratorPowerModPH0_flat
    (h : Module.Flat Qₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Z₀).obj)) :
    Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Y₀).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Z₀).obj
  let := (eₙ).toRingHom.toAlgebra
  let : Module Mₙ M := Module.compHom M (eₙ).toRingHom
  let : IsScalarTower Mₙ Qₙ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Mₙ ≃ₐ[Mₙ] Qₙ := AlgEquiv.ofBijective (Algebra.ofId Mₙ Qₙ) (eₙ).bijective
  have : Module.Flat Mₙ Qₙ := Module.Flat.of_linearEquiv eA.symm.toLinearEquiv
  have : Module.Flat Qₙ M := h
  have : Module.Flat Mₙ M := Module.Flat.trans Mₙ Qₙ M
  exact Module.Flat.of_linearEquiv (R := Mₙ) (M := M)
    (prismaticGeneratorPowerModPHomologyIso p d n X 0).toLinearEquiv

end SerrePositivity.BhattScholze
