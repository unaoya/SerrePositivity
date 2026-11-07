module

public import SerrePositivity.BhattScholze.Delta.Division.Relations
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# δ 除算の通常の底変換

## 概要
δ 射で係数を移した δ 除算の添加環は、台の可換環の押し出しである。

## 方針
反復 δ 関係式を用い、終域の δ 構造を使わずに押し出しの普遍性を示す。

## 規約
ここでは関係式による商を取る。ねじれの除去と完備化は別に扱う。

## 使われ方
結晶比較の Frobenius に沿う底変換。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
  {σ : Type u} (D : DeltaStructure p A) (E : DeltaStructure p B)
  (f : A →+* B) (hf : D.IsDeltaHom E f) (d : A) (a : σ → A)

local notation "A₁" => DeltaAdjoinDivision D d a
local notation "B₁" => DeltaAdjoinDivision E (f d) (fun s => f (a s))
local notation "jA" => deltaAdjoinDivisionMap D d a
local notation "jB" => deltaAdjoinDivisionMap E (f d) (fun s => f (a s))
local notation "qA" => (Ideal.Quotient.mk (DeltaStructure.deltaClosure
  (relativeFreeDeltaStructure σ D) (deltaDivisionRelationIdeal d a)))
local notation "qB" => (Ideal.Quotient.mk (DeltaStructure.deltaClosure
  (relativeFreeDeltaStructure σ E) (deltaDivisionRelationIdeal (f d) (fun s => f (a s)))))

include hf in
private theorem polynomialMap_isDeltaHom :
    (relativeFreeDeltaStructure σ D).IsDeltaHom (relativeFreeDeltaStructure σ E)
      (MvPolynomial.map f) := by
  apply DeltaStructure.isDeltaHom_mvPolynomial
  · intro x
    simp only [relativeFreeDeltaStructure_delta_C, MvPolynomial.map_C, hf x]
  · rintro ⟨s, n⟩
    simp only [relativeFreeDeltaStructure_delta_X, MvPolynomial.map_X]

include hf in
private theorem iteratedRelation_map (s : σ) (n : ℕ) :
    MvPolynomial.map f (deltaDivisionIteratedRelation D d a s n) =
      deltaDivisionIteratedRelation E (f d) (fun s => f (a s)) s n := by
  induction n with
  | zero => simp [deltaDivisionIteratedRelation]
  | succ n ih =>
      unfold deltaDivisionIteratedRelation at ih ⊢
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        polynomialMap_isDeltaHom D E f hf, ih]

/-- δ 射による係数の底変換は、添加する変数をそのまま送る。 -/
def deltaAdjoinDivisionBaseChange : A₁ →+* B₁ :=
  deltaDivisionIteratedRelationsLift D d a ((qB).comp (MvPolynomial.map f)) fun s n => by
    change qB (MvPolynomial.map f (deltaDivisionIteratedRelation D d a s n)) = 0
    rw [iteratedRelation_map D E f hf]
    exact deltaDivisionIteratedRelation_quotient_eq_zero E (f d) (fun s => f (a s)) s n

/-- 底変換の射と添加前の多項式環の係数変換の可換式。 -/
theorem deltaAdjoinDivisionBaseChange_mk (x : RelativeFreeDeltaRing (R := A) σ) :
    deltaAdjoinDivisionBaseChange D E f hf d a (qA x) = qB (MvPolynomial.map f x) := by
  unfold deltaAdjoinDivisionBaseChange
  rfl

/-- δ 除算を添加した後の底変換と、基底を移してからの添加は通常の可換環の押し出しをなす。 -/
theorem deltaAdjoinDivisionBaseChange_isPushout :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom jA) (CommRingCat.ofHom jB)
      (CommRingCat.ofHom (deltaAdjoinDivisionBaseChange D E f hf d a)) := by
  have hw : CommRingCat.ofHom f ≫ CommRingCat.ofHom jB =
      CommRingCat.ofHom jA ≫ CommRingCat.ofHom (deltaAdjoinDivisionBaseChange D E f hf d a) := by
    apply CommRingCat.hom_ext
    ext x
    change qB (MvPolynomial.C (f x)) = qB (MvPolynomial.map f (MvPolynomial.C x))
    rw [MvPolynomial.map_C]
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.isColimitAux' _ fun S => ?_)
  let g : B →+* S.pt := S.inl.hom
  let h : A₁ →+* S.pt := S.inr.hom
  let ev : RelativeFreeDeltaRing (R := B) σ →+* S.pt :=
    MvPolynomial.eval₂Hom g (fun i => h (qA (MvPolynomial.X i)))
  have hcomp : ev.comp (MvPolynomial.map f) = h.comp qA := by
    apply MvPolynomial.ringHom_ext'
    · ext x
      change ev (MvPolynomial.map f (MvPolynomial.C x)) = h (qA (MvPolynomial.C x))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      exact ConcreteCategory.congr_hom S.condition x
    · intro i
      change ev (MvPolynomial.map f (MvPolynomial.X i)) = h (qA (MvPolynomial.X i))
      rw [MvPolynomial.map_X]
      simp [ev]
  let L : B₁ →+* S.pt := deltaDivisionIteratedRelationsLift E (f d) (fun s => f (a s)) ev
    (fun s n => by
      rw [← iteratedRelation_map D E f hf d a s n]
      change (ev.comp (MvPolynomial.map f)) (deltaDivisionIteratedRelation D d a s n) = 0
      rw [hcomp, RingHom.comp_apply, deltaDivisionIteratedRelation_quotient_eq_zero, map_zero])
  have hL (x : RelativeFreeDeltaRing (R := B) σ) : L (qB x) = ev x := rfl
  refine ⟨CommRingCat.ofHom L, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    ext x
    change L (qB (MvPolynomial.C x)) = g x
    rw [hL, MvPolynomial.eval₂Hom_C]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change L (qB (MvPolynomial.map f x)) = h (qA x)
    rw [hL]
    exact DFunLike.congr_fun hcomp x
  · intro l hl hr
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext'
    · ext x
      change l (qB (MvPolynomial.C x)) = L (qB (MvPolynomial.C x))
      rw [hL, MvPolynomial.eval₂Hom_C]
      exact ConcreteCategory.congr_hom hl x
    · intro i
      change l (qB (MvPolynomial.X i)) = L (qB (MvPolynomial.X i))
      rw [hL]
      have H := ConcreteCategory.congr_hom hr (qA (MvPolynomial.X i))
      change l (qB (MvPolynomial.map f (MvPolynomial.X i))) = h (qA (MvPolynomial.X i)) at H
      rw [MvPolynomial.map_X] at H
      exact H.trans (by simp [ev])

end SerrePositivity.BhattScholze
