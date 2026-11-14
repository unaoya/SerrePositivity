module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# 有限多項式代数の圏と係数変更

## 概要
係数環上の有限多項式代数を変数の個数で表し、係数射による変更を関手にする。

## 方針
多項式の射は各変数への代入で記述する。係数変更が代入と可換であることを、
係数と変数の像で確認する。

## 規約
変数は `Fin n`。射は基底を保つ代数射。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の多項式模型の厳密な関手性。
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- 有限多項式代数の小さい圏の対象。 -/
structure Poly (k : Type u) [CommRing k] : Type u where
  /-- 多項式変数の個数。 -/
  n : ℕ

instance {k : Type u} [CommRing k] : SmallCategory (Poly k) where
  Hom P Q := MvPolynomial (Fin P.n) k →ₐ[k] MvPolynomial (Fin Q.n) k
  id _ := AlgHom.id k _
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- 多項式圏の射を多項式環の代数準同型として読む。 -/
abbrev Poly.hom {k : Type u} [CommRing k] {P Q : Poly k} (g : P ⟶ Q) :
    MvPolynomial (Fin P.n) k →ₐ[k] MvPolynomial (Fin Q.n) k := g

/-- 多項式代数を基底上の可換代数として読む。 -/
def polynomialAlgebras (k : Type u) [CommRing k] : Poly k ⥤ CommAlgCat.{u} k where
  obj Q := CommAlgCat.of k (MvPolynomial (Fin Q.n) k)
  map f := CommAlgCat.ofHom f

variable {k l : Type u} [CommRing k] [CommRing l]

/-- 多項式の代入射の各係数を指定の環射で送る。 -/
def changePolyHom (f : k →+* l) {P Q : Poly k} (g : P ⟶ Q) :
    MvPolynomial (Fin P.n) l →ₐ[l] MvPolynomial (Fin Q.n) l :=
  MvPolynomial.aeval (fun i => MvPolynomial.map f ((Poly.hom g) (MvPolynomial.X i)))

/-- 係数の写像と多項式代入の写像は可換。 -/
theorem changePolyHom_map (f : k →+* l) {P Q : Poly k} (g : P ⟶ Q)
    (x : MvPolynomial (Fin P.n) k) :
    changePolyHom f g (MvPolynomial.map f x) = MvPolynomial.map f ((Poly.hom g) x) := by
  have e : (changePolyHom f g).toRingHom.comp (MvPolynomial.map f) =
      (MvPolynomial.map f).comp (Poly.hom g).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change changePolyHom f g (MvPolynomial.map f (MvPolynomial.C a)) =
        MvPolynomial.map f ((Poly.hom g) (MvPolynomial.C a))
      rw [MvPolynomial.map_C]
      change changePolyHom f g (algebraMap l _ (f a)) =
        MvPolynomial.map f ((Poly.hom g) (algebraMap k _ a))
      rw [AlgHom.commutes, AlgHom.commutes]
      exact (MvPolynomial.map_C f a).symm
    · intro i
      change changePolyHom f g (MvPolynomial.map f (MvPolynomial.X i)) =
        MvPolynomial.map f ((Poly.hom g) (MvPolynomial.X i))
      rw [MvPolynomial.map_X]
      exact MvPolynomial.aeval_X _ _
  exact DFunLike.congr_fun e x

/-- 多項式代数の係数変更関手。 -/
def changePoly (f : k →+* l) : Poly k ⥤ Poly l where
  obj Q := ⟨Q.n⟩
  map g := changePolyHom f g
  map_id Q := by
    apply MvPolynomial.algHom_ext
    intro i
    change changePolyHom f (𝟙 Q) (MvPolynomial.X i) = MvPolynomial.X i
    rw [changePolyHom, MvPolynomial.aeval_X]
    exact MvPolynomial.map_X f i
  map_comp g h := by
    apply MvPolynomial.algHom_ext
    intro i
    change changePolyHom f (g ≫ h) (MvPolynomial.X i) =
      changePolyHom f h (changePolyHom f g (MvPolynomial.X i))
    have hX : changePolyHom f g (MvPolynomial.X i) =
        MvPolynomial.map f ((Poly.hom g) (MvPolynomial.X i)) := MvPolynomial.aeval_X _ _
    rw [hX, changePolyHom_map]
    exact MvPolynomial.aeval_X _ _

end SerrePositivity.BhattScholze.Prismatic
