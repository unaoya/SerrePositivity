module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericKernel
public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.NilDiagonal
public import Mathlib.RingTheory.Localization.Integral

/-!
# 一般点での普遍単射性の分母払い

## 概要
局所化後の体値点の一意性を、対角射の nil な核に翻訳して延長する。

## 方針
テンソル積の両因子を局所化し、乗法射の可換図式に核の延長を適用する。

## 規約
基底、有限モデル、有限代数、一般ファイバーの代数構造を明示する。

## 使われ方
一般点での純非分離部分から主開集合上の普遍同相を作る。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 局所化された基底上で体値点の延長が一意なら、元の基底上でも一意。 -/
theorem injective_fieldMaps_of_localization_base
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Algebra A' B] [IsScalarTower A A' B]
    (M : Submonoid A) [IsLocalization M A']
    (hf : IsUniversalHomeomorphism (algebraMap A' B)) :
    ∀ (K : Type u) [Field K],
      Function.Injective (fun g : B →+* K ↦ g.comp (algebraMap A B)) := by
  intro K _ g₁ g₂ he
  apply hf.injective_fieldMaps K
  apply IsLocalization.ringHom_ext M
  simpa only [RingHom.comp_assoc, IsScalarTower.algebraMap_eq A A' B] using he

/-- 一般ファイバーで nil な対角核を、一つの主開集合へ広げる。 -/
theorem exists_away_nil_diagonal_of_localized_fieldMaps
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B C]
    [IsScalarTower A B C] [IsNoetherianRing (B ⊗[A] B)]
    (M : Submonoid R) [IsLocalization (Algebra.algebraMapSubmonoid B M) C]
    (hf : ∀ (K : Type u) [Field K],
      Function.Injective (fun g : C →+* K ↦ g.comp (algebraMap A C))) :
    ∃ g : M, RingHom.ker (Localization.awayMap
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom
      (algebraMap R (B ⊗[A] B) g)) ≤
        nilradical (Localization.Away (algebraMap R (B ⊗[A] B) g)) := by
  let f := IsScalarTower.toAlgHom A B C
  let F := Algebra.TensorProduct.map f f
  let : IsLocalization
      (Algebra.algebraMapSubmonoid B (Algebra.algebraMapSubmonoid A M)) C := by
    rw [Algebra.algebraMapSubmonoid_map_map]
    infer_instance
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid A M) f.toLinearMap := inferInstance
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid A M) F.toLinearMap :=
    inferInstanceAs (IsLocalizedModule (Algebra.algebraMapSubmonoid A M)
      (TensorProduct.map f.toLinearMap f.toLinearMap))
  let : IsLocalizedModule M (F.restrictScalars R).toLinearMap :=
    IsLocalizedModule.restrictScalars M F.toLinearMap
  apply exists_away_nil_kernel_of_localized_nil_kernel M (F.restrictScalars R)
    (f.restrictScalars R) ((Algebra.TensorProduct.lmul' A (S := B)).restrictScalars R)
    ((Algebra.TensorProduct.lmul' A (S := C)).restrictScalars R)
  · ext x y
    simp [F, f]
  · exact IsNoetherian.noetherian _
  · exact nil_diagonal_of_injective_fieldMaps hf

/-- 主局所化した対角核が nil なら、その主開集合で体値点の延長は一意。 -/
theorem injective_fieldMaps_away_of_nil_diagonal
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (g : A)
    (hn : (RingHom.ker (Algebra.TensorProduct.lmul' A (S := B)).toRingHom).map
      (algebraMap (B ⊗[A] B) (Localization.Away (algebraMap A (B ⊗[A] B) g))) ≤
        nilradical (Localization.Away (algebraMap A (B ⊗[A] B) g))) :
    ∀ (K : Type u) [Field K], Function.Injective
      (fun u : Localization.Away (algebraMap A B g) →+* K ↦
        u.comp (Localization.awayMap (algebraMap A B) g)) := by
  intro K _ u v he
  let B' := Localization.Away (algebraMap A B g)
  let D := B ⊗[A] B
  let D' := Localization.Away (algebraMap A D g)
  let u₀ := u.comp (algebraMap B B')
  let v₀ := v.comp (algebraMap B B')
  have he₀ : u₀.comp (algebraMap A B) = v₀.comp (algebraMap A B) := by
    ext x
    have h := RingHom.congr_fun he (algebraMap A (Localization.Away g) x)
    simpa only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq] using h
  let : Algebra A K := (u₀.comp (algebraMap A B)).toAlgebra
  let φ : B →ₐ[A] K := { __ := u₀, commutes' := fun _ ↦ rfl }
  let ψ : B →ₐ[A] K :=
    { __ := v₀, commutes' := fun x ↦ (RingHom.congr_fun he₀ x).symm }
  let t : D →ₐ[A] K := Algebra.TensorProduct.lift φ ψ fun _ _ ↦ Commute.all _ _
  have hg : IsUnit (t (algebraMap A D g)) := by
    rw [t.commutes]
    exact (IsLocalization.Away.algebraMap_isUnit (algebraMap A B g)).map u
  let t' : D' →+* K := IsLocalization.Away.lift (algebraMap A D g) hg
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A B g))
  ext x
  have hk : x ⊗ₜ[A] (1 : B) - (1 : B) ⊗ₜ[A] x ∈
      RingHom.ker (Algebra.TensorProduct.lmul' A (S := B)).toRingHom := by
    simp [RingHom.mem_ker]
  have hnil := mem_nilradical.mp (hn (Ideal.mem_map_of_mem (algebraMap D D') hk))
  have hz := (hnil.map t').eq_zero
  apply sub_eq_zero.mp
  simpa [t', t, φ, ψ, u₀, v₀, IsLocalization.Away.lift_eq] using hz

/-- 整な単射の主局所化は、対角核が nil なら普遍同相。 -/
theorem isUniversalHomeomorphism_away_of_nil_diagonal
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (hi : Function.Injective (algebraMap A B)) (g : A)
    (hn : (RingHom.ker (Algebra.TensorProduct.lmul' A (S := B)).toRingHom).map
      (algebraMap (B ⊗[A] B) (Localization.Away (algebraMap A (B ⊗[A] B) g))) ≤
        nilradical (Localization.Away (algebraMap A (B ⊗[A] B) g))) :
    IsUniversalHomeomorphism (Localization.awayMap (algebraMap A B) g) := by
  have hint : (Localization.awayMap (algebraMap A B) g).IsIntegral :=
    IsLocalization.isIntegral_localization
  have hinj : Function.Injective (Localization.awayMap (algebraMap A B) g) :=
    IsLocalization.map_injective_of_injective _ _ _ hi
  exact isUniversalHomeomorphism_of_injective_fieldMaps _ hint (hint.comap_surjective hinj)
    (injective_fieldMaps_away_of_nil_diagonal g hn)

/-- 一般ファイバーで体値点の延長が一意な整単射は、一つの主開集合で普遍同相。 -/
theorem exists_away_isUniversalHomeomorphism_of_localized_fieldMaps
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B C]
    [IsScalarTower A B C] [IsNoetherianRing (B ⊗[A] B)] [Algebra.IsIntegral A B]
    (hi : Function.Injective (algebraMap A B))
    (M : Submonoid R) [IsLocalization (Algebra.algebraMapSubmonoid B M) C]
    (hf : ∀ (K : Type u) [Field K],
      Function.Injective (fun g : C →+* K ↦ g.comp (algebraMap A C))) :
    ∃ g : M, IsUniversalHomeomorphism
      (Localization.awayMap (algebraMap A B) (algebraMap R A g)) := by
  obtain ⟨g, hg⟩ := exists_away_nil_diagonal_of_localized_fieldMaps R A B C M hf
  rw [IsLocalization.ker_map _ _ (Submonoid.map_powers _ _)] at hg
  refine ⟨g, isUniversalHomeomorphism_away_of_nil_diagonal hi (algebraMap R A g) ?_⟩
  have he : algebraMap A (B ⊗[A] B) (algebraMap R A g) =
      algebraMap R (B ⊗[A] B) g :=
    (IsScalarTower.algebraMap_apply R A (B ⊗[A] B) g).symm
  simpa only [he] using hg

end SerrePositivity.CommutativeAlgebra
