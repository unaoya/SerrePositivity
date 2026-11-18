module

public import SerrePositivity.KST.LocalizingInvariants.CochainConnectiveLift
public import Mathlib.Algebra.Homology.Homotopy

/-!
# 非正源から非負標的への鎖ホモトピーの剛性

概要：非正次数の源と非負次数の標的の間のホモトピックな鎖写像は等しい。
方針：零次以外を支持で消し、零次の二つのホモトピー項も支持で消す。
規約：係数環の標数や平坦性を仮定しない。
使われ方：零次集中 E 代数の作用を実 augmentation に沿って降ろす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomologyZero
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] {K L : Complex A}

lemma nonpositive_nonnegative_homotopy_eq [K.IsStrictlyLE 0] [L.IsStrictlyGE 0]
    {f g : K ⟶ L} (h : Homotopy f g) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact (L.isZero_of_isStrictlyGE 0 i hi).eq_of_tgt _ _
  · have h₁ : h.hom 1 0 = 0 :=
      (K.isZero_of_isStrictlyLE 0 1 (by decide)).eq_of_src _ _
    have hprev : h.hom 0 (-1) = 0 :=
      (L.isZero_of_isStrictlyGE 0 (-1) (by decide)).eq_of_tgt _ _
    have hc := h.comm 0
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl), h₁, hprev,
      comp_zero, zero_comp, zero_add, zero_add] at hc
    exact hc
  · exact (K.isZero_of_isStrictlyLE 0 i hi).eq_of_src _ _

end SerrePositivity.HomologyZero
