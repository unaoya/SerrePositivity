module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDCechNerveNaturality
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.PolynomialCompletionFunctor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDBase

/-!
# 大きい分冪 Čech 模型

## 概要
完備多項式代数の全元を枠の変数とする分冪 Čech 脈体を厳密に関手化する。

## 方針
完備多項式の代入を剰余へ降ろし、枠の変数の改名に分冪包の普遍性を適用する。

## 規約
係数の射は基底の分冪イデアルを p の生成するイデアルへ送る。

## 使われ方
BS 著者版 Theorem 6.4 の Witt 基底上の大きい結晶模型。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A k : Type u} [CommRing A] [CommRing k]
variable (P : OrientedPrism p A) [Algebra k (A ⧸ P.ideal)]

local notation "C" => (A ⧸ P.ideal)

/-- 大きい枠の剰余環。 -/
abbrev bigResidue (Q : Poly C) :=
  polyCompletion P Q.n ⧸ Ideal.span {(p : polyCompletion P Q.n)}

/-- 基底の係数を指定した剰余環上の代数構造。 -/
instance bigResidueAlgebra (Q : Poly C) : Algebra k (bigResidue P Q) :=
  ((Ideal.Quotient.mk _).comp
    ((algebraMap C (polyCompletion P Q.n)).comp (algebraMap k C))).toAlgebra

variable {J : Ideal k}
variable (hcoeff : J ≤ (Ideal.span {(p : A ⧸ P.ideal)}).comap (algebraMap k (A ⧸ P.ideal)))

include hcoeff in
/-- 基底の分冪イデアルは大きい枠の剰余環で消える。 -/
theorem bigResidue_ker (Q : Poly C) :
    J ≤ RingHom.ker (algebraMap k (bigResidue P Q)) := by
  intro x hx
  change Ideal.Quotient.mk _ (algebraMap C (polyCompletion P Q.n) (algebraMap k C x)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hm : algebraMap k C x ∈ Ideal.span {(p : C)} := hcoeff hx
  have h := Ideal.mem_map_of_mem (algebraMap C (polyCompletion P Q.n)) hm
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

private theorem bigResidueMap_le {Q Q' : Poly C} (f : Q ⟶ Q') :
    Ideal.span {(p : polyCompletion P Q.n)} ≤
      (Ideal.span {(p : polyCompletion P Q'.n)}).comap (polyCompletionMap P f) := by
  rw [Ideal.span_singleton_le_iff_mem]
  change polyCompletionMap P f (p : polyCompletion P Q.n) ∈ Ideal.span {(p : polyCompletion P Q'.n)}
  rw [map_natCast]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- 完備多項式代入の p を法とする剰余への降下。 -/
def bigResidueMap {Q Q' : Poly C} (f : Q ⟶ Q') :
    bigResidue P Q →ₐ[k] bigResidue P Q' := by
  refine ⟨Ideal.quotientMap _ (polyCompletionMap P f).toRingHom (bigResidueMap_le P f), ?_⟩
  intro x
  change Ideal.Quotient.mk _ (polyCompletionMap P f (algebraMap C _ (algebraMap k C x))) =
    Ideal.Quotient.mk _ (algebraMap C _ (algebraMap k C x))
  rw [AlgHom.commutes]

/-- 剰余の写像は完備多項式の代入と可換。 -/
@[simp] theorem bigResidueMap_mk {Q Q' : Poly C} (f : Q ⟶ Q') (x : polyCompletion P Q.n) :
    bigResidueMap (k := k) P f (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (polyCompletionMap P f x) := by
  unfold bigResidueMap
  rfl

/-- 剰余の写像は恒等を保つ。 -/
@[simp] theorem bigResidueMap_id (Q : Poly C) :
    bigResidueMap (k := k) P (𝟙 Q) = AlgHom.id k (bigResidue P Q) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [bigResidueMap_mk, polyCompletionMap_id]
  rfl

/-- 剰余の写像は合成を保つ。 -/
theorem bigResidueMap_comp {Q Q' Q'' : Poly C} (f : Q ⟶ Q') (g : Q' ⟶ Q'') :
    bigResidueMap (k := k) P (f ≫ g) =
      (bigResidueMap (k := k) P g).comp (bigResidueMap (k := k) P f) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [polyCompletionMap_comp]

variable (γ : DividedPowers J) (hp : (p : k) ∈ J)

/-- 変数を完備多項式代数の全元に取る分冪 Čech 模型の厳密な関手。 -/
def bigPDModel :
    Poly C ⥤ SimplexCategory ⥤ Under (CommRingCat.of k) where
  obj Q := pdCechNerve p γ hp (bigResidue_ker P hcoeff Q) (Ideal.Quotient.mk _)
  map {Q Q'} f := PDCechNerve.rename p γ hp
    (bigResidue_ker P hcoeff Q) (bigResidue_ker P hcoeff Q')
    (Ideal.Quotient.mk _) (Ideal.Quotient.mk _) (bigResidueMap (k := k) P f)
    (polyCompletionMap P f) (fun x => (bigResidueMap_mk P f x).symm)
  map_id Q := by
    change PDCechNerve.rename p γ hp _ _ _ _ (bigResidueMap (k := k) P (𝟙 Q))
      (polyCompletionMap P (𝟙 Q)) _ = _
    refine (PDCechNerve.rename_congr p γ hp _ _ _ _ _ _ _
      (bigResidueMap_id (k := k) P Q) ?_).trans (PDCechNerve.rename_id ..)
    exact congrArg (fun f : polyCompletion P Q.n →ₐ[C] polyCompletion P Q.n => ⇑f)
      (polyCompletionMap_id P Q)
  map_comp {Q Q' Q''} f g := by
    change PDCechNerve.rename p γ hp _ _ _ _ (bigResidueMap (k := k) P (f ≫ g))
      (polyCompletionMap P (f ≫ g)) _ = _
    refine (PDCechNerve.rename_congr p γ hp _ _ _ _ _ _ _
      (bigResidueMap_comp (k := k) P f g) ?_).trans (PDCechNerve.rename_comp ..).symm
    exact congrArg (fun h : polyCompletion P Q.n →ₐ[C] polyCompletion P Q''.n => ⇑h)
      (polyCompletionMap_comp P f g)

/-- Witt 基底での大きい分冪 Čech 模型。係数は第 0 Witt 成分で作用する。 -/
def wittBigPdModel (hpC : Function.Injective (fun x : C => (p : C) * x))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : C)) :
    Poly C ⥤ SimplexCategory ⥤ Under (CommRingCat.of (WittVector p C)) := by
  letI := (wZero p C).toAlgebra
  exact bigPDModel P (J := wittPdIdeal p C) (by rfl)
    (wittPdStructure p C hpC hlocal) (p_mem_wittPdIdeal p C)

end SerrePositivity.BhattScholze.Prismatic
