module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# 余単体的可換環の主イデアルによる商

## 概要
余単体的に保存される元の冪で各項を割り、商射と商の間の誘導射を作る。

## 方針
余面と余退化を商に降ろし、写像の等式を商射上で確かめる。

## 規約
商は各次数で取る。元の正則性は要求しない。

## 使われ方
余単体的な Bockstein の短完全列と、結晶比較の mod p の模型。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.Cosimplicial

/-- 指定元を保つ環射が、その冪の商に誘導する環準同型。 -/
def quotientPowHom {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) (y : S)
    (h : f x = y) (j : ℕ) :
    (R ⧸ Ideal.span {x ^ j}) →+* (S ⧸ Ideal.span {y ^ j}) :=
  Ideal.quotientMap _ f.hom (by
    rw [Ideal.span_le]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    change f.hom (x ^ j) ∈ Ideal.span {y ^ j}
    rw [map_pow, show f.hom x = y from h]
    exact Ideal.subset_span rfl)

variable (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n : SimplexCategory, C.obj n)
  (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)

/-- 概要：余単体的可換環を各項で元の冪によって割った余単体的可換環。
方針：構造射を商に降ろす。
規約：指定元はすべての単体圏の射で保存される。
使われ方：Bockstein の短完全列と mod p の模型。 -/
def quotPow (j : ℕ) : CosimplicialObject CommRingCat.{u} where
  obj n := CommRingCat.of (C.obj n ⧸ Ideal.span {d n ^ j})
  map {m n} θ := CommRingCat.ofHom (quotientPowHom (C.map θ) (d m) (d n) (hd_nat θ) j)
  map_id n := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk _ (C.map (𝟙 n) a) = Ideal.Quotient.mk _ a
    simp
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk _ (C.map (f ≫ g) a) =
      Ideal.Quotient.mk _ (C.map g (C.map f a))
    simp

/-- 概要：元の冪による商への自然な射。
方針：各項の商準同型を使う。
規約：冪の指数は全次数で一定。
使われ方：商の係数環を指定する。 -/
def quotProjection (j : ℕ) : C ⟶ quotPow C d hd_nat j where
  app n := CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {d n ^ j}))
  naturality _ _ _ := rfl

/-- 概要：指定元を保存する余単体的環射が冪の商に誘導する射。
方針：各項の商の普遍性を用い、商射上で自然性を確かめる。
規約：二つの商の指数は等しい。
使われ方：Bockstein の自然性と結晶側への橋。 -/
def quotPowMap {C' : CosimplicialObject CommRingCat.{u}} (d' : ∀ n, C'.obj n)
    (hd' : ∀ {m n} (θ : m ⟶ n), C'.map θ (d' m) = d' n) (g : C ⟶ C')
    (hg : ∀ n, g.app n (d n) = d' n) (j : ℕ) :
    quotPow C d hd_nat j ⟶ quotPow C' d' hd' j where
  app n := CommRingCat.ofHom (quotientPowHom (g.app n) (d n) (d' n) (hg n) j)
  naturality m n θ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk _ ((C.map θ ≫ g.app n) a) =
      Ideal.Quotient.mk _ ((g.app m ≫ C'.map θ) a)
    rw [g.naturality]

end SerrePositivity.Cosimplicial
