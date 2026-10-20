module

public import SerrePositivity.EInfinity.HomologyZero.PairingRepresentatives

/-!
# 実際の H⁰ に誘導される双線形作用

概要：BF §1 の H⁰ の積の加法性とスカラー線形性を実際の加群構造で証明する。
方針：任意の H⁰ の元を単位からの射で表し、鎖射の双線形性を使う。
規約：複体の有界性や平坦性は仮定しない。
使われ方：E 代数の H⁰ の積と分配法則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.HomologyZero

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {K L M : Complex A} (μ : K ⊗ L ⟶ M)

/-- 概要：H⁰ の二入力作用は左入力で加法的（BF §1）。
方針：三元を単位からの射で表して計算する。
規約：既存の H⁰ の加法を使う。
使われ方：左入力の線形性。 -/
lemma pairingValue_add_left (x y : K.homology 0) (z : L.homology 0) :
    pairingValue μ (x + y) z = pairingValue μ x z + pairingValue μ y z := by
  obtain ⟨f, rfl⟩ := unitClass_surjective K x
  obtain ⟨g, rfl⟩ := unitClass_surjective K y
  obtain ⟨h, rfl⟩ := unitClass_surjective L z
  rw [← map_add (unitClass K) f g, pairingValue_class, pairingValue_class, pairingValue_class]
  simp only [map_add, LinearMap.add_apply]

/-- 概要：H⁰ の二入力作用は右入力で加法的（BF §1）。
方針：三元を単位からの射で表して計算する。
規約：既存の H⁰ の加法を使う。
使われ方：右入力の線形性。 -/
lemma pairingValue_add_right (x : K.homology 0) (y z : L.homology 0) :
    pairingValue μ x (y + z) = pairingValue μ x y + pairingValue μ x z := by
  obtain ⟨f, rfl⟩ := unitClass_surjective K x
  obtain ⟨g, rfl⟩ := unitClass_surjective L y
  obtain ⟨h, rfl⟩ := unitClass_surjective L z
  rw [← map_add (unitClass L) g h, pairingValue_class, pairingValue_class, pairingValue_class]
  simp only [map_add]

/-- 概要：H⁰ の二入力作用は左入力のスカラー倍を保つ（BF §1）。
方針：代表射のスカラー倍で計算する。
規約：元の基礎環 A の加群構造。
使われ方：左入力の線形性。 -/
lemma pairingValue_smul_left (a : A) (x : K.homology 0) (y : L.homology 0) :
    pairingValue μ (a • x) y = a • pairingValue μ x y := by
  obtain ⟨f, rfl⟩ := unitClass_surjective K x
  obtain ⟨g, rfl⟩ := unitClass_surjective L y
  rw [← map_smul (unitClass K) a f, pairingValue_class, pairingValue_class]
  simp only [map_smul, LinearMap.smul_apply]

/-- 概要：H⁰ の二入力作用は右入力のスカラー倍を保つ（BF §1）。
方針：代表射のスカラー倍で計算する。
規約：元の基礎環 A の加群構造。
使われ方：右入力の線形性。 -/
lemma pairingValue_smul_right (a : A) (x : K.homology 0) (y : L.homology 0) :
    pairingValue μ x (a • y) = a • pairingValue μ x y := by
  obtain ⟨f, rfl⟩ := unitClass_surjective K x
  obtain ⟨g, rfl⟩ := unitClass_surjective L y
  rw [← map_smul (unitClass L) a g, pairingValue_class, pairingValue_class]
  simp only [map_smul]

/-- 概要：二入力複体射は実際の H⁰ の双線形作用を与える（BF §1）。
方針：代表元独立な値に証明済みの二変数の線形性を付ける。
規約：元の三つの homology 0 の A 加群構造を保つ。
使われ方：E 代数の H⁰ の積と分配法則。 -/
def pairing : K.homology 0 →ₗ[A] L.homology 0 →ₗ[A] M.homology 0 where
  toFun x := {
    toFun := pairingValue μ x
    map_add' := pairingValue_add_right μ x
    map_smul' a y := pairingValue_smul_right μ a x y }
  map_add' x y := LinearMap.ext (fun z => pairingValue_add_left μ x y z)
  map_smul' a x := LinearMap.ext (fun y => pairingValue_smul_left μ a x y)

end SerrePositivity.EInfinity.HomologyZero
