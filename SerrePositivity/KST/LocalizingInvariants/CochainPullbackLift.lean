module

public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：一致する二つの実 cochain を、元の複体 pullback に持ち上げる。
方針：評価関手の pullback 保存を各次数に使い、元の両射影を厳密に回収する。
規約：cochain の次数は任意。使われ方：実経路関手と pullback の両立。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.CochainPullback
variable {R : Type u} [CommRing R] {K P Q D : Complex R} (f : P ⟶ D) (g : Q ⟶ D)

def graded (n : ℤ) : IsPullback ((pullback.fst f g).f n) ((pullback.snd f g).f n)
    (f.f n) (g.f n) :=
  Functor.map_isPullback (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n)
    (IsPullback.of_hasPullback f g)

variable (k : ℤ) (a : Cochain K P k) (b : Cochain K Q k)
  (h : a.comp (Cochain.ofHom f) (add_zero k) = b.comp (Cochain.ofHom g) (add_zero k))

def lift : Cochain K (pullback f g) k :=
  Cochain.mk (fun p q hpq => (graded f g q).lift (a.v p q hpq) (b.v p q hpq) (by
    have he := Cochain.congr_v h p q hpq
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using he))

lemma lift_fst : (lift f g k a b h).comp (Cochain.ofHom (pullback.fst f g)) (add_zero k) = a := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  exact (graded f g q).lift_fst _ _ _

lemma lift_snd : (lift f g k a b h).comp (Cochain.ofHom (pullback.snd f g)) (add_zero k) = b := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  exact (graded f g q).lift_snd _ _ _

lemma hom_ext {a b : Cochain K (pullback f g) k}
    (hf : a.comp (Cochain.ofHom (pullback.fst f g)) (add_zero k) =
      b.comp (Cochain.ofHom (pullback.fst f g)) (add_zero k))
    (hg : a.comp (Cochain.ofHom (pullback.snd f g)) (add_zero k) =
      b.comp (Cochain.ofHom (pullback.snd f g)) (add_zero k)) : a = b := by
  apply Cochain.ext
  intro p q hpq
  apply (graded f g q).hom_ext
  · have he := Cochain.congr_v hf p q hpq
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using he
  · have he := Cochain.congr_v hg p q hpq
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using he

end SerrePositivity.KST.LocalizingInvariants.CochainPullback
