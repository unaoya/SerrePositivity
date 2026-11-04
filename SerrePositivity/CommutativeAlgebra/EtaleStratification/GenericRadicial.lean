module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericKernel
public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.NilDiagonal

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

end SerrePositivity.CommutativeAlgebra
