module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.PairingLinear
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# H⁰ の双線形作用のホモトピー不変性と交換

概要：BF §1 の E の係数ホモトピーを H⁰ の積の等式へ移す。
方針：実際の単位からの代表で作用を計算し、作用のホモトピーと交換の自然性を使う。
規約：元の H⁰ の加群構造と Koszul 対称性を使う。
使われ方：E 代数の H⁰ の可換性と結合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomologyZero

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {K L M : Complex A}

/-- 概要：ホモトピックな二入力作用は H⁰ に同じ双線形作用を与える（BF §1）。
方針：入力代表のテンソルを前合成して、作用のホモトピーを類の一致へ移す。
規約：実際の H⁰ 上の線形写像の等式。
使われ方：E の係数の違いを H⁰ で消す。 -/
lemma pairing_homotopy {μ ν : K ⊗ L ⟶ M} (h : Homotopy μ ν) :
    _root_.SerrePositivity.HomologyZero.pairing μ = _root_.SerrePositivity.HomologyZero.pairing ν := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff M _ _).mpr
  exact ⟨h.compLeft ((λ_ (𝟙_ (Complex A))).inv ≫
    (_root_.SerrePositivity.HomologyZero.representative K x ⊗ₘ _root_.SerrePositivity.HomologyZero.representative L y))⟩

/-- 概要：入力を交換した鎖射の H⁰ 作用は二入力を交換した値（BF §1）。
方針：代表射のテンソルと交換の自然性を使い、単位の交換を相殺する。
規約：実際の Koszul 対称性で、零次に余分な符号は生じない。
使われ方：E 代数の H⁰ の積の可換性。 -/
lemma pairing_braiding (μ : L ⊗ K ⟶ M) (x : K.homology 0) (y : L.homology 0) :
    _root_.SerrePositivity.HomologyZero.pairing ((β_ K L).hom ≫ μ) x y = _root_.SerrePositivity.HomologyZero.pairing μ y x := by
  change _root_.SerrePositivity.HomologyZero.unitClass M ((λ_ (𝟙_ (Complex A))).inv ≫
      (_root_.SerrePositivity.HomologyZero.representative K x ⊗ₘ _root_.SerrePositivity.HomologyZero.representative L y) ≫ (β_ K L).hom ≫ μ) =
    _root_.SerrePositivity.HomologyZero.unitClass M ((λ_ (𝟙_ (Complex A))).inv ≫
      (_root_.SerrePositivity.HomologyZero.representative L y ⊗ₘ _root_.SerrePositivity.HomologyZero.representative K x) ≫ μ)
  rw [BraidedCategory.braiding_naturality_assoc, ← Category.assoc,
    leftUnitor_inv_braiding, unitors_inv_equal]

end SerrePositivity.HomologyZero
