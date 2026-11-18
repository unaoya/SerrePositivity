module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.NormalizationDescent
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# 退化を消す双線形写像の正規化への降下

概要：Berger–Fresse §1.1.3 の shuffle を正規化するための二変数の降下を与える。
方針：二つの変数の正規化射影に対する不変性を内部の線形写像加群で証明する。
規約：正規化 Moore 部分複体を使い、非退化単体の基底を選ばない。
使われ方：一般の shuffle の生成元公式を正規化鎖上で得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.AlgebraicTopology.DoldKan
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A]

/-- 概要：単体加群上の双線形写像を二つの Moore 部分加群へ制限（Berger–Fresse §1.1.3）。
方針：両入力へ正規化 Moore 包含を前置する。
規約：この定義自体には退化消滅を要求しない。
使われ方：shuffle の正規化鎖上の双線形写像を定義する。 -/
def normalizedBilinear (X Y : SimplicialObject (ModuleCat.{u} A)) (p q : ℕ)
    {Z : ModuleCat.{u} A} (b : X _⦋p⦌ →ₗ[A] Y _⦋q⦌ →ₗ[A] Z) :
    ((normalizedMooreComplex (ModuleCat A)).obj X).X p →ₗ[A]
      ((normalizedMooreComplex (ModuleCat A)).obj Y).X q →ₗ[A] Z :=
  b.compl₁₂ ((inclusionOfMooreComplexMap X).f p).hom ((inclusionOfMooreComplexMap Y).f q).hom

/-- 概要：両変数の退化を消す双線形写像の降下は元の値を復元（Berger–Fresse §1.1.3）。
方針：各変数の Dold–Kan 射影への不変性を使い、包含との合成を消す。
規約：零次数にも同じ型の退化条件を使う。
使われ方：shuffle の正規化生成元上の公式。 -/
lemma normalizedBilinear_normalization (X Y : SimplicialObject (ModuleCat.{u} A))
    (p q : ℕ) {Z : ModuleCat.{u} A} (b : X _⦋p⦌ →ₗ[A] Y _⦋q⦌ →ₗ[A] Z)
    (hX : ∀ (k : ℕ) (e : k + 1 = p) (i : Fin (k + 1)),
      (X.σ i ≫ eqToHom (congrArg (fun j => X _⦋j⦌) e)) ≫ ModuleCat.ofHom b = 0)
    (hY : ∀ (k : ℕ) (e : k + 1 = q) (i : Fin (k + 1)),
      (Y.σ i ≫ eqToHom (congrArg (fun j => Y _⦋j⦌) e)) ≫ ModuleCat.ofHom b.flip = 0)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.normalizedBilinear X Y p q b ((PInftyToNormalizedMooreComplex X).f p x)
        ((PInftyToNormalizedMooreComplex Y).f q y) = b x y := by
  have hpX := congrArg (fun φ => φ.f p x)
    (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X)
  have hpY := congrArg (fun φ => φ.f q y)
    (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y)
  change ((inclusionOfMooreComplexMap X).f p) ((PInftyToNormalizedMooreComplex X).f p x) =
    (PInfty.f p : X _⦋p⦌ ⟶ X _⦋p⦌) x at hpX
  change ((inclusionOfMooreComplexMap Y).f q) ((PInftyToNormalizedMooreComplex Y).f q y) =
    (PInfty.f q : Y _⦋q⦌ ⟶ Y _⦋q⦌) y at hpY
  change b (((inclusionOfMooreComplexMap X).f p) ((PInftyToNormalizedMooreComplex X).f p x))
    (((inclusionOfMooreComplexMap Y).f q) ((PInftyToNormalizedMooreComplex Y).f q y)) = _
  rw [hpX, hpY]
  have hx := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projector_comp_of_degeneracies_zero X p (ModuleCat.ofHom b)
    (fun k e i => by simpa only [Category.assoc] using hX k e i)
  have hy := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projector_comp_of_degeneracies_zero Y q (ModuleCat.ofHom b.flip)
    (fun k e i => by simpa only [Category.assoc] using hY k e i)
  have hx' := congrArg (fun φ => φ x ((PInfty.f q : Y _⦋q⦌ ⟶ Y _⦋q⦌) y)) hx
  have hy' := congrArg (fun φ => φ y x) hy
  exact hx'.trans hy'

end SerrePositivity.SimplicialChains.Shuffle
