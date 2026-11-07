module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# 正則元による商の余単体的短完全列

## 概要
余単体的可換環の各項で正則な元 d に対し、d 倍と商射から短完全列を作る。

## 方針
短完全性は商の代表元で確かめる。d 倍の単射性は各項での正則性による。

## 規約
加群の係数環は全次数で共通とする。

## 使われ方
Hodge–Tate 比較の Bockstein。
-/

@[expose] public section
noncomputable section

universe u

open CategoryTheory

namespace SerrePositivity.Cosimplicial

section Pointwise

variable {R : Type u} [CommRing R] (x : R)

local notation "I" => Ideal.span {x ^ (1 : ℕ)}
local notation "J" => Ideal.span {x ^ (2 : ℕ)}

/-- 概要：主イデアル商から二乗による商への d 倍写像。
方針：d 倍した後で商射を取り、主イデアルを消すことを確かめる。
規約：元の環上の線形写像。
使われ方：正則元による短完全列の左端。 -/
def principalQuotientMul : (R ⧸ I) →ₗ[R] (R ⧸ J) :=
  (I).liftQ ((J).mkQ.comp (LinearMap.mulLeft R x)) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    apply (Submodule.Quotient.mk_eq_zero J).2
    apply Ideal.mem_span_singleton.mpr
    exact ⟨b, by simp [pow_two, mul_assoc]⟩)

@[simp]
theorem principalQuotientMul_mk (a : R) :
    principalQuotientMul x (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (x * a) :=
  rfl

/-- 二乗による商から主イデアルによる商への標準商射。 -/
def principalQuotientReduction : (R ⧸ J) →+* (R ⧸ I) :=
  Ideal.Quotient.factor (Ideal.span_le.mpr (by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact Ideal.mem_span_singleton.mpr ⟨x, by simp [pow_two]⟩))

@[simp]
theorem principalQuotientReduction_mk (a : R) :
    principalQuotientReduction x (Ideal.Quotient.mk J a) = Ideal.Quotient.mk I a :=
  rfl

/-- 正則元による主イデアル商から二乗の商への倍写像は単射。 -/
theorem principalQuotientMul_injective (hx : Function.Injective (fun a : R => x * a)) :
    Function.Injective (principalQuotientMul x) := by
  apply (injective_iff_map_eq_zero (principalQuotientMul x)).2
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [principalQuotientMul_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at ha
  obtain ⟨b, hb⟩ := ha
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨b, hx (by simpa [pow_two, mul_assoc] using hb)⟩

/-- 倍写像の像は主イデアル商への射の核。 -/
theorem principalQuotient_exact :
    Function.Exact (principalQuotientMul x) (principalQuotientReduction x) := by
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [principalQuotientReduction_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk I b, by simp⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [principalQuotientMul_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      Ideal.mem_span_singleton] at hb
    obtain ⟨c, hc⟩ := hb
    refine ⟨b - x * c, ?_⟩
    rw [pow_one, mul_sub, ← mul_assoc, ← pow_two, ← hc, sub_sub_cancel]

/-- 主イデアル商への標準商射は全射。 -/
theorem principalQuotientReduction_surjective :
    Function.Surjective (principalQuotientReduction x) := by
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk J a, rfl⟩

end Pointwise

section Cosimplicial

variable (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n : SimplexCategory, C.obj n)
  (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)
  (hd_reg : ∀ n, Function.Injective (fun x : C.obj n => d n * x))
  (k : Type u) [CommRing k]
  (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C)

local notation "M[" j "]" =>
  toModules k (quotPow C d hd_nat j) (ι ≫ quotProjection C d hd_nat j)

/-- 正則元による主イデアル商から二乗の商への項ごとの倍写像。 -/
def quotPowMul : M[1] ⟶ M[2] where
  app n := ConcreteCategory.ofHom (C := ModuleCat k) (X := (M[1]).obj n)
    (Y := (M[2]).obj n) {
      toFun := principalQuotientMul (d n)
      map_add' := (principalQuotientMul (d n)).map_add
      map_smul' := fun r a => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change Ideal.Quotient.mk _ (d n * ((ι.app n).hom r * a)) =
          Ideal.Quotient.mk _ ((ι.app n).hom r * (d n * a))
        rw [mul_left_comm]
    }
  naturality m n θ := by
    apply ConcreteCategory.hom_ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk _ (d n * C.map θ a) =
      Ideal.Quotient.mk _ ((C.map θ).hom (d m * a))
    apply congrArg (Ideal.Quotient.mk _)
    rw [map_mul, show (C.map θ).hom (d m) = d n from hd_nat θ]

/-- 二乗の商から主イデアル商への項ごとの標準商射。 -/
def quotPowReduce : M[2] ⟶ M[1] where
  app n := ConcreteCategory.ofHom (C := ModuleCat k) (X := (M[2]).obj n)
    (Y := (M[1]).obj n) {
      toFun := principalQuotientReduction (d n)
      map_add' := (principalQuotientReduction (d n)).map_add
      map_smul' := fun r a => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        rfl
    }
  naturality m n θ := by
    apply ConcreteCategory.hom_ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl


/-- 概要：各項で正則な元 d による余単体的短完全列。
方針：d 倍、標準商射、各項での短完全性を組み合わせる。
規約：短完全列の項は共通の係数環の加群として読む。
使われ方：Hodge–Tate 比較の Bockstein。 -/
def regularShortExact : CosimplicialShortExact M[1] M[2] M[1] where
  ι := quotPowMul C d hd_nat k ι
  π := quotPowReduce C d hd_nat k ι
  zero := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro a
    exact ((principalQuotient_exact (d n)) _).2 ⟨a, rfl⟩
  exact n := ModuleCat.shortComplex_shortExact _
    (principalQuotient_exact (d n))
    (principalQuotientMul_injective (d n) (hd_reg n))
    (principalQuotientReduction_surjective (d n))

/-- 正則元による商の短完全列が誘導する連結写像。 -/
def regularBockstein (i : ℕ) :=
  (regularShortExact C d hd_nat hd_reg k ι).bockstein i

end Cosimplicial

end SerrePositivity.Cosimplicial
