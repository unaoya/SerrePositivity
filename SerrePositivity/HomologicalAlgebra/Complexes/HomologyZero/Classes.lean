module

public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# 閉次数零の元から実際の H⁰ への類

概要：BF §1 の E 代数の H⁰ の演算を作るため、元のホモロジー加群への全射を明示する。
方針：ModuleCat の明示的な kernel・quotient のホモロジーデータを使う。
規約：任意の非有界整数複体と可換基礎環、ホモロジーの型を置き換えない。
使われ方：H⁰ の積の代表元独立性と環公理の検証。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomologyZero

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] (K : Complex A)

/-- 概要：実際の H⁰ と閉元の境界による商の標準比較（BF §1）。
方針：隣接する三次数を明示し、加群のホモロジーの商表示を使う。
規約：次数 −1・0・1 を指定する。
使われ方：H⁰ の元の代表と境界の判定。 -/
def quotientIso : K.homology 0 ≅ (K.sc' (-1) 0 1).moduleCatLeftHomologyData.H :=
  (K.homologyIsoSc' (-1) 0 1 (by simp [CochainComplex.prev])
    (by simp [CochainComplex.next])) ≪≫ (K.sc' (-1) 0 1).moduleCatHomologyIso

/-- 概要：閉次数零の元を実際の H⁰ の類へ送る線形写像（BF §1）。
方針：明示的な kernel の商からホモロジーへの標準同型を使う。
規約：終域は元の複体の homology 0。
使われ方：H⁰ の演算の代表元表示。 -/
def classMap : zeroCycles K →ₗ[A] K.homology 0 :=
  ((K.sc' (-1) 0 1).moduleCatLeftHomologyData.π ≫ (_root_.SerrePositivity.HomologyZero.quotientIso K).inv).hom

/-- 概要：実際の H⁰ の全ての元は閉次数零の元で表される（BF §1）。
方針：加群の商写像と標準同型が全射であることを使う。
規約：複体の有界性・平坦性は不要。
使われ方：H⁰ の演算と等式を代表元に帰着する。 -/
lemma classMap_surjective : Function.Surjective (_root_.SerrePositivity.HomologyZero.classMap K) := by
  change Function.Surjective ((_root_.SerrePositivity.HomologyZero.quotientIso K).inv ∘
    (K.sc' (-1) 0 1).moduleCatToCycles.range.mkQ)
  apply ((ModuleCat.epi_iff_surjective _).mp
    (inferInstance : Epi (_root_.SerrePositivity.HomologyZero.quotientIso K).inv)).comp
  exact Submodule.mkQ_surjective _

/-- 概要：閉次数零の元の類が零であることは境界であることと同値（BF §1）。
方針：商写像の kernel を明示的な境界の range に同定する。
規約：境界は実際の次数 −1 の元。
使われ方：ホモトピーから H⁰ の等式を得る。 -/
lemma classMap_eq_zero_iff (c : zeroCycles K) :
    _root_.SerrePositivity.HomologyZero.classMap K c = 0 ↔ ∃ h : K.X (-1), K.d (-1) 0 h = c.val := by
  have hi : Function.Injective (_root_.SerrePositivity.HomologyZero.quotientIso K).inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  change (_root_.SerrePositivity.HomologyZero.quotientIso K).inv
    ((K.sc' (-1) 0 1).moduleCatToCycles.range.mkQ c) = 0 ↔ _
  constructor
  · intro hc
    have hq : (K.sc' (-1) 0 1).moduleCatToCycles.range.mkQ c = 0 :=
      hi (hc.trans (map_zero (_root_.SerrePositivity.HomologyZero.quotientIso K).inv.hom).symm)
    obtain ⟨h, hh⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    exact ⟨h, congrArg Subtype.val hh⟩
  · rintro ⟨h, hh⟩
    have hc : c ∈ (K.sc' (-1) 0 1).moduleCatToCycles.range := ⟨h, Subtype.ext hh⟩
    have hq : (K.sc' (-1) 0 1).moduleCatToCycles.range.mkQ c = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hc
    exact (congrArg (fun q => (_root_.SerrePositivity.HomologyZero.quotientIso K).inv q) hq).trans
      (map_zero (_root_.SerrePositivity.HomologyZero.quotientIso K).inv.hom)

/-- 概要：単位からの射と閉次数零の元の対応は線形（BF §1）。
方針：既存の同値に加法とスカラーの評価公式を付ける。
規約：実際の単位複体を使う。
使われ方：単位からのホモトピー類上の積を H⁰ へ移す。 -/
def unitCycleLinearEquiv : (𝟙_ (Complex A) ⟶ K) ≃ₗ[A] zeroCycles K where
  toEquiv := unitCycleEquiv K
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' a f := by apply Subtype.ext; rfl

/-- 概要：単位複体からの射を実際の H⁰ の類へ送る（BF §1）。
方針：単位の一での評価と閉元の類写像を合成する。
規約：線形写像として構成する。
使われ方：E 代数の H⁰ の演算を単位からの射で表す。 -/
def unitClass : (𝟙_ (Complex A) ⟶ K) →ₗ[A] K.homology 0 :=
  (_root_.SerrePositivity.HomologyZero.classMap K).comp (_root_.SerrePositivity.HomologyZero.unitCycleLinearEquiv K).toLinearMap

/-- 概要：H⁰ の全ての元は単位からの射で表される（BF §1）。
方針：二つの全射を合成する。
規約：ホモトピー類の型はまだ選ばない。
使われ方：H⁰ の環公理を実際の複体射に帰着する。 -/
lemma unitClass_surjective : Function.Surjective (_root_.SerrePositivity.HomologyZero.unitClass K) :=
  (_root_.SerrePositivity.HomologyZero.classMap_surjective K).comp (_root_.SerrePositivity.HomologyZero.unitCycleLinearEquiv K).surjective

end SerrePositivity.HomologyZero
