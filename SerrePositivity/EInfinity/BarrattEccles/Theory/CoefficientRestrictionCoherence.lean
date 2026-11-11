module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientOperad
public import SerrePositivity.EInfinity.BarrattEccles.Theory.LaxTensorPower

/-!
# 係数制限と環準同型の恒等・合成

## 概要
HA §3.2.2 の係数制限の関手性に必要な、厳密なテンソル比較を与える。

## 方針
単位は 1 上、tensorator は斉次純粋テンソル上、係数写像は非退化生成元上で照合する。

## 規約
係数の制限を複体の項ごとに取り、すべての整数次数を許す。

## 使われ方
M13 の係数制限の恒等と合成。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open Functor.LaxMonoidal
open scoped Simplicial TensorProduct

variable {S T W : Type u} [CommRing S] [CommRing T] [CommRing W]
  (f : S →+* T) (g : T →+* W)

local notation "R" => ScalarExtension.restriction

/-- 恒等環準同型での単位対象の係数制限は恒等射。 -/
lemma restrictionUnit_id : ε (R (RingHom.id S)) = 𝟙 (𝟙_ (Complex S)) := by
  apply from_single_hom_ext
  apply (cancel_epi (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat S))).inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact ScalarExtension.restriction_ε_one (RingHom.id S)

/-- 合成による単位対象の係数制限は二つの比較の合成。 -/
lemma restrictionUnit_comp :
    ε (R (g.comp f)) = ε (R f) ≫ (R f).map (ε (R g)) := by
  apply from_single_hom_ext
  apply (cancel_epi (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat S))).inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  let s (A : Type u) [CommRing A] :=
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)
  change (ε (R (g.comp f))).f 0 (s S) = (ε (R g)).f 0 ((ε (R f)).f 0 (s S))
  rw [ScalarExtension.restriction_ε_one, ScalarExtension.restriction_ε_one,
    ScalarExtension.restriction_ε_one]

/-- 恒等環準同型でのテンソル比較は恒等射。 -/
lemma restrictionTensor_id (X Y : Complex S) :
    μ (R (RingHom.id S)) X Y = 𝟙 (X ⊗ Y) := by
  apply HomologicalComplex.hom_ext
  intro t
  apply mapBifunctor.hom_ext
  intro r s h
  change r + s = t at h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact ScalarExtension.restriction_μ_apply (RingHom.id S) X Y r s t h x y

/-- 合成によるテンソル比較は二つの比較の合成。 -/
lemma restrictionTensor_comp (X Y : Complex W) :
    μ (R (g.comp f)) X Y = μ (R f) ((R g).obj X) ((R g).obj Y) ≫
      (R f).map (μ (R g) X Y) := by
  apply HomologicalComplex.hom_ext
  intro t
  apply mapBifunctor.hom_ext
  intro r s h
  change r + s = t at h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (μ (R (g.comp f)) X Y).f t
      (ιTensorObj ((R (g.comp f)).obj X) ((R (g.comp f)).obj Y) r s t h (x ⊗ₜ[S] y)) =
    (μ (R g) X Y).f t ((μ (R f) ((R g).obj X) ((R g).obj Y)).f t
      (ιTensorObj ((R (g.comp f)).obj X) ((R (g.comp f)).obj Y) r s t h (x ⊗ₜ[S] y)))
  exact (ScalarExtension.restriction_μ_apply (g.comp f) X Y r s t h x y).trans
    ((congrArg (fun a => (μ (R g) X Y).f t a)
      (ScalarExtension.restriction_μ_apply f ((R g).obj X) ((R g).obj Y) r s t h x y)).trans
        (ScalarExtension.restriction_μ_apply g X Y r s t h x y)).symm

private lemma complex_generator_hom_ext (n : ℕ) {K : Complex S}
    {a b : complex S n ⟶ K}
    (h : ∀ q (x : (simplicial n) _⦋q⦌),
      a.f (-(q : ℤ)) ((complexXIso S n q).inv (normalizedGenerator S n q x)) =
      b.f (-(q : ℤ)) ((complexXIso S n q).inv (normalizedGenerator S n q x))) : a = b := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : 0 < i
  · exact (complex_isZero_positive S n i hi).eq_of_src _ _
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(q : ℤ) := ⟨(-i).toNat, by omega⟩
  apply (cancel_epi (complexXIso S n q).inv).mp
  apply normalizedGenerator_hom_ext S
  exact h q

/-- 恒等環準同型での演算の係数写像は恒等射。 -/
lemma coefficientComplexMap_id (n : ℕ) :
    coefficientComplexMap (RingHom.id S) n = 𝟙 (complex S n) := by
  apply complex_generator_hom_ext n
  intro q x
  exact coefficientComplexMap_generator (RingHom.id S) n q x

/-- 演算の係数写像は生成元を保ち、合成と可換。 -/
lemma coefficientComplexMap_comp (n : ℕ) :
    coefficientComplexMap (g.comp f) n =
      coefficientComplexMap f n ≫ (R f).map (coefficientComplexMap g n) := by
  apply complex_generator_hom_ext n
  intro q x
  change (coefficientComplexMap (g.comp f) n).f (-(q : ℤ))
      ((complexXIso S n q).inv (normalizedGenerator S n q x)) =
    (coefficientComplexMap g n).f (-(q : ℤ)) ((coefficientComplexMap f n).f (-(q : ℤ))
      ((complexXIso S n q).inv (normalizedGenerator S n q x)))
  rw [coefficientComplexMap_generator, coefficientComplexMap_generator,
    coefficientComplexMap_generator]

end SerrePositivity.EInfinity.BarrattEccles
