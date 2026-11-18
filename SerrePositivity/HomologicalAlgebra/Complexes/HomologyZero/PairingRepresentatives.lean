module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.HomotopyClasses
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric

/-!
# 鎖写像の二入力作用を H⁰ の代表へ適用する

概要：BF §1 の H⁰ の積に必要な二入力作用の代表元独立性を示す。
方針：単位からの代表射をテンソルし、テンソルが鎖ホモトピーを保つことを使う。
規約：任意の二入力複体射、追加の平坦性や有界性を仮定しない。
使われ方：実際の H⁰ の加群上の双線形作用。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomologyZero

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：実際の H⁰ の元の単位からの代表射を選ぶ（BF §1）。
方針：線形同値でホモトピー類へ戻し、既存の標準代表を取る。
規約：選択は後の作用の値に影響しない。
使われ方：H⁰ の二入力作用の定義。 -/
def representative (K : Complex A) (x : K.homology 0) : 𝟙_ (Complex A) ⟶ K :=
  ((_root_.SerrePositivity.HomologyZero.unitHomLinearEquiv K).symm x).out

/-- 概要：選んだ代表射の H⁰ の類は元の元（BF §1）。
方針：線形同値の逆を評価する。
規約：実際の homology 0 の等式。
使われ方：演算の代表元公式。 -/
lemma representative_class (K : Complex A) (x : K.homology 0) :
    _root_.SerrePositivity.HomologyZero.unitClass K (_root_.SerrePositivity.HomologyZero.representative K x) = x := by
  change _root_.SerrePositivity.HomologyZero.homotopyClassMap K ((_root_.SerrePositivity.HomologyZero.unitHomLinearEquiv K).symm x) = x
  exact (_root_.SerrePositivity.HomologyZero.unitHomLinearEquiv K).apply_symm_apply x

/-- 概要：元の射から選び直した代表は元の射とホモトピック（BF §1）。
方針：H⁰ の類の一致をホモトピーに戻す。
規約：モデル圏による置換は使わない。
使われ方：入力代表の選択独立性。 -/
lemma representative_homotopy (K : Complex A) (f : 𝟙_ (Complex A) ⟶ K) :
    Nonempty (Homotopy (_root_.SerrePositivity.HomologyZero.representative K (_root_.SerrePositivity.HomologyZero.unitClass K f)) f) :=
  (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff K _ _).mp (_root_.SerrePositivity.HomologyZero.representative_class K _)

/-- 概要：二入力の複体射を単位からの二射へ適用する双線形写像（BF §1）。
方針：単位を二つに分け、テンソルした二射の後で作用を適用する。
規約：Koszul テンソルの既存の双線形性を使う。
使われ方：H⁰ 作用の鎖射による表示。 -/
def unitPairing {K L M : Complex A} (μ : K ⊗ L ⟶ M) :
    (𝟙_ (Complex A) ⟶ K) →ₗ[A] (𝟙_ (Complex A) ⟶ L) →ₗ[A] (𝟙_ (Complex A) ⟶ M) where
  toFun f := {
    toFun g := (λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g) ≫ μ
    map_add' g h := by
      simp only [MonoidalPreadditive.tensor_add, Preadditive.comp_add, Preadditive.add_comp]
    map_smul' a g := by
      simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul,
        Linear.comp_smul, Linear.smul_comp, RingHom.id_apply] }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    change (λ_ (𝟙_ (Complex A))).inv ≫ ((f + g) ⊗ₘ h) ≫ μ =
      ((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ h) ≫ μ) +
      ((λ_ (𝟙_ (Complex A))).inv ≫ (g ⊗ₘ h) ≫ μ)
    simp only [MonoidalPreadditive.add_tensor,
      Preadditive.comp_add, Preadditive.add_comp]
  map_smul' a f := by
    apply LinearMap.ext
    intro g
    change (λ_ (𝟙_ (Complex A))).inv ≫ ((a • f) ⊗ₘ g) ≫ μ =
      a • ((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g) ≫ μ)
    simp only [tensorHom_def,
      MonoidalLinear.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp]

/-- 概要：二入力作用は両入力の鎖ホモトピーを保つ（BF §1）。
方針：左右のテンソルホモトピーを連結し、単位の分割と作用を合成する。
規約：実際の複体射の鎖ホモトピー。
使われ方：H⁰ の作用が代表元によらないこと。 -/
def unitPairingHomotopy {K L M : Complex A} (μ : K ⊗ L ⟶ M)
    {f f' : 𝟙_ (Complex A) ⟶ K} {g g' : 𝟙_ (Complex A) ⟶ L}
    (hf : Homotopy f f') (hg : Homotopy g g') :
    Homotopy (_root_.SerrePositivity.HomologyZero.unitPairing μ f g) (_root_.SerrePositivity.HomologyZero.unitPairing μ f' g') :=
  (((SerrePositivity.cochainTensorHomotopyLeft hf g).trans
    (SerrePositivity.cochainTensorHomotopyRight f' hg)).compLeft
      (λ_ (𝟙_ (Complex A))).inv).compRight μ

/-- 概要：二入力複体射が実際の H⁰ の二元に与える値（BF §1）。
方針：各入力の代表を選び、二入力の作用の類を取る。
規約：値は実際の標的の homology 0。
使われ方：双線形な H⁰ 作用の定義。 -/
def pairingValue {K L M : Complex A} (μ : K ⊗ L ⟶ M)
    (x : K.homology 0) (y : L.homology 0) : M.homology 0 :=
  _root_.SerrePositivity.HomologyZero.unitClass M (_root_.SerrePositivity.HomologyZero.unitPairing μ (_root_.SerrePositivity.HomologyZero.representative K x) (_root_.SerrePositivity.HomologyZero.representative L y))

/-- 概要：二入力作用の H⁰ 値を任意の代表射で計算できる（BF §1）。
方針：選び直した二代表と元の代表を結ぶホモトピーを作用へ移す。
規約：選択した標準代表の具体的な値には依存しない。
使われ方：双線形性と環公理の代表元による検証。 -/
lemma pairingValue_class {K L M : Complex A} (μ : K ⊗ L ⟶ M)
    (f : 𝟙_ (Complex A) ⟶ K) (g : 𝟙_ (Complex A) ⟶ L) :
    _root_.SerrePositivity.HomologyZero.pairingValue μ (_root_.SerrePositivity.HomologyZero.unitClass K f) (_root_.SerrePositivity.HomologyZero.unitClass L g) = _root_.SerrePositivity.HomologyZero.unitClass M (_root_.SerrePositivity.HomologyZero.unitPairing μ f g) :=
  (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff M _ _).mpr
    ⟨_root_.SerrePositivity.HomologyZero.unitPairingHomotopy μ (_root_.SerrePositivity.HomologyZero.representative_homotopy K f).some
      (_root_.SerrePositivity.HomologyZero.representative_homotopy L g).some⟩

end SerrePositivity.HomologyZero
