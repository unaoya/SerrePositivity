module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.Classes
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# H⁰ と単位複体からの鎖ホモトピー類

概要：BF §1 の H⁰ の演算を、単位からの射のホモトピー類で検証できるようにする。
方針：境界判定と既存のホモトピー境界公式から全単射を得る。
規約：実際の H⁰ の加群構造と HomotopyCategory の加群構造を同定する。
使われ方：E 代数の積の代表元独立性と環公理。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomologyZero

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] (K : Complex A)

/-- 概要：単位からの二射は H⁰ で一致するちょうどその時ホモトピック（BF §1）。
方針：差の類が零であることを境界として読み、既存の単位ホモトピー公式を使う。
規約：実際の複体射と鎖ホモトピー。
使われ方：演算の代表元独立性。 -/
lemma unitClass_eq_iff (f g : 𝟙_ (Complex A) ⟶ K) :
    _root_.SerrePositivity.HomologyZero.unitClass K f = _root_.SerrePositivity.HomologyZero.unitClass K g ↔ Nonempty (Homotopy f g) := by
  rw [← sub_eq_zero, ← map_sub]
  change _root_.SerrePositivity.HomologyZero.classMap K ((_root_.SerrePositivity.HomologyZero.unitCycleLinearEquiv K) (f - g)) = 0 ↔ _
  rw [_root_.SerrePositivity.HomologyZero.classMap_eq_zero_iff]
  exact (unit_homotopy_boundary K f g).symm

/-- 概要：ホモトピー類の標準代表を選び直しても H⁰ の類は変わらない（BF §1）。
方針：商関手の代表と元の射を結ぶ既存のホモトピーを使う。
規約：標準代表の具体的な選択には依存しない。
使われ方：HomotopyCategory からの線形写像の構成。 -/
lemma unitClass_out_map (f : 𝟙_ (Complex A) ⟶ K) :
    _root_.SerrePositivity.HomologyZero.unitClass K ((HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map f).out =
      _root_.SerrePositivity.HomologyZero.unitClass K f :=
  (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff K _ _).mpr ⟨HomotopyCategory.homotopyOutMap f⟩

/-- 概要：単位からの鎖ホモトピー類を実際の H⁰ へ送る線形写像（BF §1）。
方針：代表を選び、類の加法・スカラーは商関手の線形性で比較する。
規約：既存の HomotopyCategory を使う。
使われ方：ホモトピー類上の積を実際のホモロジーへ移す。 -/
def homotopyClassMap :
    ((HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj (𝟙_ (Complex A)) ⟶
      (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj K) →ₗ[A] K.homology 0 where
  toFun f := _root_.SerrePositivity.HomologyZero.unitClass K f.out
  map_add' f g := by
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map_surjective f
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map_surjective g
    rw [← Functor.map_add, _root_.SerrePositivity.HomologyZero.unitClass_out_map, _root_.SerrePositivity.HomologyZero.unitClass_out_map, _root_.SerrePositivity.HomologyZero.unitClass_out_map, map_add]
  map_smul' a f := by
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map_surjective f
    rw [← Functor.map_smul, _root_.SerrePositivity.HomologyZero.unitClass_out_map, _root_.SerrePositivity.HomologyZero.unitClass_out_map, map_smul]
    rfl

/-- 概要：ホモトピー類から H⁰ への写像は元の射の類を返す（BF §1）。
方針：標準代表を選び直しても類が変わらないことを使う。
規約：実際の商関手の像。
使われ方：H⁰ の元で演算を評価する。 -/
lemma homotopyClassMap_apply_map (f : 𝟙_ (Complex A) ⟶ K) :
    _root_.SerrePositivity.HomologyZero.homotopyClassMap K ((HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map f) =
      _root_.SerrePositivity.HomologyZero.unitClass K f := _root_.SerrePositivity.HomologyZero.unitClass_out_map K f

/-- 概要：単位からのホモトピー類と H⁰ の対応は全単射（BF §1）。
方針：類の等式判定から単射性、閉元の代表から全射性を得る。
規約：平坦性や有界性を要求しない。
使われ方：H⁰ の環構造の線形移送。 -/
lemma homotopyClassMap_bijective : Function.Bijective (_root_.SerrePositivity.HomologyZero.homotopyClassMap K) := by
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map_surjective f
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map_surjective g
    rw [_root_.SerrePositivity.HomologyZero.homotopyClassMap_apply_map, _root_.SerrePositivity.HomologyZero.homotopyClassMap_apply_map] at h
    exact HomotopyCategory.eq_of_homotopy _ _ ((_root_.SerrePositivity.HomologyZero.unitClass_eq_iff K f g).mp h).some
  · intro x
    obtain ⟨f, hf⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective K x
    exact ⟨_, (_root_.SerrePositivity.HomologyZero.homotopyClassMap_apply_map K f).trans hf⟩

/-- 概要：単位からの鎖ホモトピー類は実際の H⁰ と線形同値（BF §1）。
方針：構成済みの全単射線形写像を同値に束ねる。
規約：両辺の既存の加群構造を保つ。
使われ方：E 代数の H⁰ の可換環構造の移送。 -/
def unitHomLinearEquiv :
    ((HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj (𝟙_ (Complex A)) ⟶
      (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj K) ≃ₗ[A] K.homology 0 :=
  LinearEquiv.ofBijective (_root_.SerrePositivity.HomologyZero.homotopyClassMap K) (_root_.SerrePositivity.HomologyZero.homotopyClassMap_bijective K)

end SerrePositivity.HomologyZero
