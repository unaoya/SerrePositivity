module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomRestriction
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
# 直和の両包含への内部 Hom の制限

概要：Berger–Moerdijk 命題 4.1 の区間の両端への制限を二項直和で表す。
方針：二つの次数付き射を直和の射影で延長して足す。
規約：値域の複体は任意であり、入力の二つの複体も独立に選べる。
使われ方：境界への Hom の制限を両端点評価の対へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomBiprodRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex _root_.CochainComplex.HomComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

private lemma biprod_element_ext {X Y : Complex A} {n : ℤ} {x y : (X ⊞ Y).X n}
    (hf : (biprod.fst : X ⊞ Y ⟶ X).f n x = (biprod.fst : X ⊞ Y ⟶ X).f n y)
    (hs : (biprod.snd : X ⊞ Y ⟶ Y).f n x = (biprod.snd : X ⊞ Y ⟶ Y).f n y) : x = y := by
  have ht := congrArg (fun f : X ⊞ Y ⟶ X ⊞ Y => f.f n) (biprod.total (X := X) (Y := Y))
  have hx := congrArg (fun f => f x) ht
  have hy := congrArg (fun f => f y) ht
  change (biprod.inl : X ⟶ X ⊞ Y).f n ((biprod.fst : X ⊞ Y ⟶ X).f n x) +
    (biprod.inr : Y ⟶ X ⊞ Y).f n ((biprod.snd : X ⊞ Y ⟶ Y).f n x) = x at hx
  change (biprod.inl : X ⟶ X ⊞ Y).f n ((biprod.fst : X ⊞ Y ⟶ X).f n y) +
    (biprod.inr : Y ⟶ X ⊞ Y).f n ((biprod.snd : X ⊞ Y ⟶ Y).f n y) = y at hy
  rw [← hx, ← hy, hf, hs]

/-- 概要：直和からの内部 Hom を両包含へ制限する射（BM 命題 4.1）。
方針：前合成の二つの chain map を直和への射に束ねる。
規約：出力の直和は複体の二項直和。
使われ方：区間の境界への制限を両端点での制限へ移す。 -/
def homBiprodRestriction (X Y B : Complex A) :
    homComplex A (X ⊞ Y) B ⟶ homComplex A X B ⊞ homComplex A Y B :=
  biprod.lift (homPrecompose biprod.inl B) (homPrecompose biprod.inr B)

/-- 概要：直和の両包含への制限は全次数で全射（BM 命題 4.1）。
方針：二つの次数付き射を射影で前合成して足し合わせる。
規約：各成分で延長し、微分との可換性を延長の入力に要求しない。
使われ方：境界制限から両端点評価への移送で全射性を保存する。 -/
lemma homBiprodRestriction_degreewise_surjective (X Y B : Complex A) (n : ℤ) :
    Function.Surjective ((_root_.SerrePositivity.HomBiprodRestriction.homBiprodRestriction X Y B).f n) := by
  intro z
  let a := (biprod.fst : homComplex A X B ⊞ homComplex A Y B ⟶ homComplex A X B).f n z
  let b := (biprod.snd : homComplex A X B ⊞ homComplex A Y B ⟶ homComplex A Y B).f n z
  let w : Homogeneous (X ⊞ Y) B n := Cochain.mk (fun p q hpq =>
    (biprod.fst : X ⊞ Y ⟶ X).f p ≫ a.v p q hpq +
      (biprod.snd : X ⊞ Y ⟶ Y).f p ≫ b.v p q hpq)
  refine ⟨w, _root_.SerrePositivity.HomBiprodRestriction.biprod_element_ext ?_ ?_⟩
  · change ((_root_.SerrePositivity.HomBiprodRestriction.homBiprodRestriction X Y B) ≫ biprod.fst).f n w = a
    rw [_root_.SerrePositivity.HomBiprodRestriction.homBiprodRestriction, biprod.lift_fst, homPrecompose_apply]
    apply Cochain.ext
    intro p q hpq
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, w, Cochain.mk_v,
      Preadditive.comp_add, biprod_inl_fst_f_assoc, biprod_inl_snd_f_assoc,
      zero_comp, add_zero]
  · change ((_root_.SerrePositivity.HomBiprodRestriction.homBiprodRestriction X Y B) ≫ biprod.snd).f n w = b
    rw [_root_.SerrePositivity.HomBiprodRestriction.homBiprodRestriction, biprod.lift_snd, homPrecompose_apply]
    apply Cochain.ext
    intro p q hpq
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, w, Cochain.mk_v,
      Preadditive.comp_add, biprod_inr_fst_f_assoc, biprod_inr_snd_f_assoc,
      zero_comp, zero_add]

end SerrePositivity.HomBiprodRestriction
