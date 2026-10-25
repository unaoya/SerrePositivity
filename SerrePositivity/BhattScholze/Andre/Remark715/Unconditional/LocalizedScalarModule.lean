module

public import SerrePositivity.HomologicalAlgebra.TorBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# 係数を固定する実源作用の局所化

## 概要
BS Rem 7.15（著者版 p.62）の実源の右因子を係数局所化へ運ぶ。

## 方針
分母集合を固定する環自己射による加群作用について、元の局所化射が加群局所化になる。

## 規約
元の係数射と作用を保持し、自己射の可逆性は要求しない。

## 使われ方
元の二因子導来源と局所化先の二因子源との比較に用いる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (α : R →+* R) (β : S →+* S)
variable (hcomm : β.comp (algebraMap R S) = (algebraMap R S).comp α)

/-- 概要：可換な自己射を持つ局所化射を、元の自己射作用間の線形射として表す。
方針：環射の可換性をスカラー作用の可換性へ書き直す。
規約：台写像は元の標準係数射。
使われ方：BS Rem 7.15（著者版 p.62）の右因子の比較。 -/
def unconditionalScalarModuleCoefficientMap :
    baseChangeScalarModule α →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj (baseChangeScalarModule β) where
  toFun := algebraMap R S
  map_add' := map_add _
  map_smul' r x := by
    change R at x
    change algebraMap R S (α r * x) = β (algebraMap R S r) * algebraMap R S x
    rw [map_mul, show β (algebraMap R S r) = algebraMap R S (α r) from
      DFunLike.congr_fun hcomm r]

/-- 概要：分母集合を固定する自己射の係数加群も、元の局所化射で局所化される。
方針：通常局所化の単元性・分数表示・核判定を元の作用へ移す。
規約：自己射の単射性・平坦性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実源右因子の係数拡大。 -/
theorem unconditionalScalarModuleCoefficientMap_isLocalizedModule
    (M : Submonoid R) [IsLocalization M S] (hfix : ∀ s : M, α s = s) :
    IsLocalizedModule M (unconditionalScalarModuleCoefficientMap α β hcomm) where
  map_units := by
    intro s
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun x : S => β (algebraMap R S s) * x)
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp ((IsLocalization.map_units S s).map β)
  surj y := by
    change S at y
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj M y
    refine ⟨(x, s), ?_⟩
    change β (algebraMap R S s) * y = algebraMap R S x
    rw [show β (algebraMap R S s) = algebraMap R S (α s) from
      DFunLike.congr_fun hcomm (s : R), hfix]
    exact (mul_comm _ _).trans hs
  exists_of_eq := by
    intro x y hxy
    change R at x y
    change algebraMap R S x = algebraMap R S y at hxy
    obtain ⟨s, hs⟩ := IsLocalization.eq_iff_exists M S |>.mp hxy
    refine ⟨s, ?_⟩
    change α s * x = α s * y
    rw [hfix]
    exact hs

/-- 概要：自己射で作用する元の加群の係数拡大は、局所化先の自己射係数加群。
方針：元の係数射の加群局所化性を通常テンソルの普遍性へ移す。
規約：元の自己射作用と標準係数拡大を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の二因子源の右因子の実比較。 -/
def unconditionalScalarModuleLocalizationEquiv
    (M : Submonoid R) [IsLocalization M S] (hfix : ∀ s : M, α s = s) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (baseChangeScalarModule α) ≃ₗ[S]
      baseChangeScalarModule β := by
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj (baseChangeScalarModule β)
  letI : Module S N := Module.compHom S β
  letI : IsScalarTower R S N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let f := unconditionalScalarModuleCoefficientMap α β hcomm
  have : IsLocalizedModule M f :=
    unconditionalScalarModuleCoefficientMap_isLocalizedModule α β hcomm M hfix
  let h := IsLocalizedModule.isBaseChange M S f
  exact (extendScalarsObjEquivTensor R S (baseChangeScalarModule α)).trans h.equiv

end SerrePositivity.BhattScholze.Andre
