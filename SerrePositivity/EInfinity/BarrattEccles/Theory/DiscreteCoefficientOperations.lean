module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteCoefficientCarrier

/-!
# 離散代数の比較が保つ単位と積

## 概要
HA §3.2.2 の係数制限の零次比較は、元の単位と積を保つ。

## 方針
単位は 1 上、積は零次の純粋テンソル上で計算する。

## 規約
通常の代数を `RingAlgebra` の下圏表示で取る。

## 使われ方
M13 の `discrete_restrict` 欄。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded
open Functor.LaxMonoidal (ε left_unitality)
open scoped MonObj
open scoped TensorProduct

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

local notation "R" => ScalarExtension.restriction

/-- 元の通常代数の零次モノイド複体。 -/
abbrev discreteCoefficientMonoid (A : Type u) [CommRing A] (B : RingAlgebra A) :
    CommMon (Complex A) :=
  (CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A ((underAlgFunctor A).obj B))

/-- 零次モノイドの単位は、元の通常代数の 1 を表す。 -/
lemma discreteCoefficientMonoid_unit_zero (A : Type u) [CommRing A] (B : RingAlgebra A) :
    (η[(discreteCoefficientMonoid A B).X]).f 0
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
      (singleObjXSelf (.up ℤ) 0 (ModuleCat.of A ((underAlgFunctor A).obj B))).inv
        (1 : (underAlgFunctor A).obj B) := by
  let M := ModuleCat.of A ((underAlgFunctor A).obj B)
  let s := singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))
  let h : 𝟙_ (ModuleCat A) ⟶ M := ModuleCat.ofHom (Algebra.linearMap A ((underAlgFunctor A).obj B))
  change ((𝟙 _ ≫ (single (ModuleCat A) (.up ℤ) 0).map h).f 0) (s.inv 1) = _
  rw [Category.id_comp, single_map_f_self]
  simp only [ModuleCat.comp_apply]
  exact congrArg ((singleObjXSelf (.up ℤ) 0 M).inv ·)
    (map_one (algebraMap A ((underAlgFunctor A).obj B)))

/-- 零次モノイドの積は、純粋テンソル上で元の通常代数の積。 -/
lemma discreteCoefficientMonoid_mul_zero (A : Type u) [CommRing A] (B : RingAlgebra A)
    (x y : (underAlgFunctor A).obj B) :
    let M := ModuleCat.of A ((underAlgFunctor A).obj B)
    let K := (discreteCoefficientMonoid A B).X
    let e := singleObjXSelf (.up ℤ) 0 M
    (μ[K]).f 0 (ιTensorObj K K 0 0 0 rfl (e.inv x ⊗ₜ[A] e.inv y)) = e.inv (x * y) := by
  dsimp only
  let M := ModuleCat.of A ((underAlgFunctor A).obj B)
  let K := (discreteCoefficientMonoid A B).X
  let e := singleObjXSelf (.up ℤ) 0 M
  let h : M ⊗ M ⟶ M := ModuleCat.ofHom (LinearMap.mul' A ((underAlgFunctor A).obj B))
  change ((cochainSingleTensorIso M M).hom ≫ (single (ModuleCat A) (.up ℤ) 0).map h).f 0
    (ιTensorObj K K 0 0 0 rfl (e.inv x ⊗ₜ[A] e.inv y)) = _
  have hi : (cochainSingleTensorIso M M).hom.f 0
      (ιTensorObj K K 0 0 0 rfl (e.inv x ⊗ₜ[A] e.inv y)) =
        (singleObjXSelf (.up ℤ) 0 (M ⊗ M)).inv (x ⊗ₜ[A] y) := by
    have he := cochainSingleTensorIso_hom_apply_ι M M (e.inv x) (e.inv y)
    simp only [e, Iso.inv_hom_id_apply] at he
    exact he
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, single_map_f_self]
  rw [hi, Iso.inv_hom_id_apply]
  rfl

/-- 零次の比較と係数制限は、単位について可換。 -/
lemma discreteRestrictionMonoid_unit (B : RingAlgebra T) :
    LaxComparisonSquare (R f) (ε (R f)) (discreteRestrictionCarrierIso f B).hom
      η[(discreteCoefficientMonoid S ((restrictRingAlgebra f).obj B)).X]
      η[(discreteCoefficientMonoid T B).X] := by
  unfold LaxComparisonSquare
  apply from_single_hom_ext
  let s := singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat S))
  apply (cancel_epi s.inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (discreteRestrictionCarrierIso f B).hom.f 0
      ((η[(discreteCoefficientMonoid S ((restrictRingAlgebra f).obj B)).X]).f 0 (s.inv 1)) =
    (η[(discreteCoefficientMonoid T B).X]).f 0 ((ε (R f)).f 0 (s.inv 1))
  rw [discreteCoefficientMonoid_unit_zero, ScalarExtension.restriction_ε_one,
    discreteCoefficientMonoid_unit_zero, discreteRestrictionCarrierIso_zero]

/-- 零次の比較と係数制限は、積について可換。 -/
lemma discreteRestrictionMonoid_mul (B : RingAlgebra T) :
    LaxComparisonSquare (R f)
      (laxTensorComparison (R f) (discreteRestrictionCarrierIso f B).hom
        (discreteRestrictionCarrierIso f B).hom)
      (discreteRestrictionCarrierIso f B).hom
      μ[(discreteCoefficientMonoid S ((restrictRingAlgebra f).obj B)).X]
      μ[(discreteCoefficientMonoid T B).X] := by
  unfold LaxComparisonSquare
  let K := (discreteCoefficientMonoid S ((restrictRingAlgebra f).obj B)).X
  let L := (discreteCoefficientMonoid T B).X
  let e := (discreteRestrictionCarrierIso f B).hom
  change μ[K] ≫ e = (e ⊗ₘ e) ≫ Functor.LaxMonoidal.μ (R f) L L ≫ (R f).map μ[L]
  apply HomologicalComplex.hom_ext
  intro t
  apply mapBifunctor.hom_ext
  intro r s h
  change r + s = t at h
  by_cases hr : r = 0
  · subst r
    by_cases hs : s = 0
    · subst s
      have ht : t = 0 := by omega
      subst t
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      let M := ModuleCat.of S ((underAlgFunctor S).obj ((restrictRingAlgebra f).obj B))
      let v := singleObjXSelf (.up ℤ) 0 M
      obtain ⟨a, rfl⟩ := v.symm.toLinearEquiv.surjective x
      obtain ⟨b, rfl⟩ := v.symm.toLinearEquiv.surjective y
      change e.f 0 ((μ[K]).f 0 (ιTensorObj K K 0 0 0 rfl (v.inv a ⊗ₜ[S] v.inv b))) =
        (μ[L]).f 0 ((Functor.LaxMonoidal.μ (R f) L L).f 0
          ((e ⊗ₘ e).f 0 (ιTensorObj K K 0 0 0 rfl (v.inv a ⊗ₜ[S] v.inv b))))
      have ht : ((e ⊗ₘ e).f 0)
          (ιTensorObj K K 0 0 0 rfl (v.inv a ⊗ₜ[S] v.inv b)) =
        ιTensorObj ((R f).obj L) ((R f).obj L) 0 0 0 rfl
          (e.f 0 (v.inv a) ⊗ₜ[S] e.f 0 (v.inv b)) :=
        tensorMap_apply e e 0 0 0 rfl (v.inv a) (v.inv b)
      rw [discreteCoefficientMonoid_mul_zero, ht, ScalarExtension.restriction_μ_apply]
      let N := ModuleCat.of T ((underAlgFunctor T).obj B)
      let w := singleObjXSelf (.up ℤ) 0 N
      have ha : e.f 0 (v.inv a) = w.inv a := discreteRestrictionCarrierIso_zero f B a
      have hb : e.f 0 (v.inv b) = w.inv b := discreteRestrictionCarrierIso_zero f B b
      rw [ha, hb]
      exact (discreteRestrictionCarrierIso_zero f B (a * b)).trans
        (discreteCoefficientMonoid_mul_zero T B a b).symm
    · exact ((tensorLeft (K.X 0)).map_isZero
        (isZero_single_obj_X (.up ℤ) 0
          (ModuleCat.of S ((underAlgFunctor S).obj ((restrictRingAlgebra f).obj B)))
          s hs)).eq_of_src _ _
  · exact ((tensorRight (K.X s)).map_isZero
      (isZero_single_obj_X (.up ℤ) 0
        (ModuleCat.of S ((underAlgFunctor S).obj ((restrictRingAlgebra f).obj B)))
        r hr)).eq_of_src _ _

end SerrePositivity.EInfinity.BarrattEccles
