module

public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticGeneratorPowerModP

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

local notation "eₙ" => prismaticGeneratorPowerModPEquiv p d n

variable (X : DerivedCategory.Minus (ModuleCat.{u} A))

local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₚ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X)
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X

/-- 実二生成剰余のH0忠実平坦性は、正確なmod p商環上のH0忠実平坦性へ移る。 -/
theorem prismaticGeneratorPowerModPH0_faithfullyFlat
    (h : Module.FaithfullyFlat Qₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Z₀).obj)) :
    Module.FaithfullyFlat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Y₀).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Z₀).obj
  let := (eₙ).toRingHom.toAlgebra
  let : Module Mₙ M := Module.compHom M (eₙ).toRingHom
  let : IsScalarTower Mₙ Qₙ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Mₙ ≃ₐ[Mₙ] Qₙ := AlgEquiv.ofBijective (Algebra.ofId Mₙ Qₙ) (eₙ).bijective
  have : Module.FaithfullyFlat Mₙ Qₙ :=
    Module.FaithfullyFlat.of_linearEquiv Mₙ Mₙ eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat Qₙ M := h
  have : Module.FaithfullyFlat Mₙ M := Module.FaithfullyFlat.trans Mₙ Qₙ M
  exact Module.FaithfullyFlat.of_linearEquiv (R := Mₙ) (M := M)
    (prismaticGeneratorPowerModPHomologyIso p d n X 0).toLinearEquiv

end SerrePositivity.BhattScholze
