module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.LocalizedScalarModule

/-!
# 実評価因子の係数局所化

## 概要
BS Rem 7.15（著者版 p.62）の実源の左評価因子を係数局所化へ運ぶ。

## 方針
可換な環射の正方形について、分母像での局所化を加群局所化として比較する。

## 規約
評価射の単射性・平坦性を要求せず、元の標準係数射を保つ。

## 使われ方
元の二因子導来源と局所化先の二因子源との比較に用いる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
variable [Algebra R S] [Algebra T U]
variable (φ : R →+* T) (ψ : S →+* U)
variable (hcomm : ψ.comp (algebraMap R S) = (algebraMap T U).comp φ)

/-- 概要：可換な環射の正方形の係数射を、評価作用を保つ線形射にする。
方針：正方形の可換性をスカラー作用へ適用する。
規約：台写像は元の標準係数射。
使われ方：BS Rem 7.15（著者版 p.62）の左評価因子の局所化。 -/
def unconditionalEvaluationCoefficientMap :
    baseChangeScalarModule φ →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj (baseChangeScalarModule ψ) where
  toFun := algebraMap T U
  map_add' := map_add _
  map_smul' r x := by
    change T at x
    change algebraMap T U (φ r * x) = ψ (algebraMap R S r) * algebraMap T U x
    rw [map_mul, show ψ (algebraMap R S r) = algebraMap T U (φ r) from
      DFunLike.congr_fun hcomm r]

/-- 概要：分母像で局所化した評価環への係数射は、元の評価加群の局所化。
方針：実局所化の分数表示と核判定を分母像の代表元に沿って移す。
規約：評価環自体の元の作用を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の左因子の通常係数拡大比較。 -/
theorem unconditionalEvaluationCoefficientMap_isLocalizedModule
    (M : Submonoid R) [IsLocalization M S] [IsLocalization (M.map φ.toMonoidHom) U] :
    IsLocalizedModule M (unconditionalEvaluationCoefficientMap φ ψ hcomm) where
  map_units := by
    intro s
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun x : U => ψ (algebraMap R S s) * x)
    rw [show ψ (algebraMap R S s) = algebraMap T U (φ s) from
      DFunLike.congr_fun hcomm (s : R)]
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp
      (IsLocalization.map_units (M := M.map φ.toMonoidHom) U
        ⟨φ s, ⟨s, s.property, rfl⟩⟩)
  surj y := by
    change U at y
    obtain ⟨⟨x, t⟩, ht⟩ := IsLocalization.surj (M.map φ.toMonoidHom) y
    obtain ⟨s, hs, hst⟩ := t.property
    change φ s = (t : T) at hst
    refine ⟨(x, ⟨s, hs⟩), ?_⟩
    change ψ (algebraMap R S s) * y = algebraMap T U x
    rw [show ψ (algebraMap R S s) = algebraMap T U (φ s) from
      DFunLike.congr_fun hcomm s, hst]
    exact (mul_comm _ _).trans ht
  exists_of_eq := by
    intro x y hxy
    change T at x y
    change algebraMap T U x = algebraMap T U y at hxy
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists (M.map φ.toMonoidHom) U).mp hxy
    obtain ⟨s, hs, hst⟩ := t.property
    change φ s = (t : T) at hst
    refine ⟨⟨s, hs⟩, ?_⟩
    change φ s * x = φ s * y
    rw [hst]
    exact ht

/-- 概要：元の評価加群の標準係数拡大は、局所化先の評価加群。
方針：元の係数射の加群局所化性を通常テンソル普遍性へ移す。
規約：二つの評価射と標準係数射を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の二因子源の左因子の実比較。 -/
def unconditionalEvaluationLocalizationEquiv
    (M : Submonoid R) [IsLocalization M S] [IsLocalization (M.map φ.toMonoidHom) U] :
    (ModuleCat.extendScalars (algebraMap R S)).obj (baseChangeScalarModule φ) ≃ₗ[S]
      baseChangeScalarModule ψ := by
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj (baseChangeScalarModule ψ)
  letI : Module S N := Module.compHom U ψ
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let f := unconditionalEvaluationCoefficientMap φ ψ hcomm
  have : IsLocalizedModule M f :=
    unconditionalEvaluationCoefficientMap_isLocalizedModule φ ψ hcomm M
  let h := IsLocalizedModule.isBaseChange M S f
  exact (extendScalarsObjEquivTensor R S (baseChangeScalarModule φ)).trans h.equiv

end SerrePositivity.BhattScholze.Andre
