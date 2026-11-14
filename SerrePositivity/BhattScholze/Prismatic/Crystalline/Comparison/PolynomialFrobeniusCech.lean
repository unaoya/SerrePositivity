module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import SerrePositivity.BhattScholze.Delta.Free.PolynomialExpand
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# 多項式 Čech 余脈体と相対 Frobenius

## 概要
各頂点の変数を持つ余単体的多項式環と、変数を p 乗する相対 Frobenius を定める。

## 方針
頂点の写像を変数の添字変更に使う。相対 Frobenius は係数を保つ代入とする。
Frobenius に沿う基底の添字を頂点別に分け、余面に沿って零指数を挿入する。

## 使われ方
Frobenius に沿う押し出しのコホモロジー比較（BS 著者版 Lemma 5.4）。
-/

public noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

/-- 多項式代数の Čech 余脈体は、各頂点に変数の copy を持つ。 -/
def polynomialCech (k : Type u) [CommRing k] (σ : Type) :
    CosimplicialObject CommRingCat.{u} where
  obj n := CommRingCat.of (MvPolynomial (σ × Fin (n.len + 1)) k)
  map θ := CommRingCat.ofHom (MvPolynomial.rename
    (fun x => (x.1, θ.toOrderHom x.2))).toRingHom
  map_id n := by
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext'
    · ext a
      simp
    · intro x
      simp
  map_comp θ ψ := by
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext'
    · ext a
      simp
    · intro x
      simp

/-- 係数を保ち、各 copy の変数を p 乗へ送る相対 Frobenius。 -/
def relativeFrobeniusCech (p : ℕ) (k : Type u) [CommRing k] (σ : Type) :
    polynomialCech k σ ⟶ polynomialCech k σ where
  app _ := CommRingCat.ofHom (MvPolynomial.expand p).toRingHom
  naturality i j θ := by
    let ρ : σ × Fin (i.len + 1) → σ × Fin (j.len + 1) :=
      fun x => (x.1, θ.toOrderHom x.2)
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    change MvPolynomial.expand p (MvPolynomial.rename ρ f) =
      MvPolynomial.rename ρ (MvPolynomial.expand p f)
    exact (MvPolynomial.rename_expand p ρ f).symm

private def vertexExponentEquiv (σ : Type*) (t : Type*) [Finite t] :
    (σ × t →₀ ℕ) ≃ (t → σ →₀ ℕ) :=
  (Finsupp.domCongr (Equiv.prodComm σ t)).toEquiv.trans
    (Finsupp.curryEquiv.trans Finsupp.equivFunOnFinite)

private theorem vertexExponentEquiv_apply {σ t : Type*} [Finite t]
    (d : σ × t →₀ ℕ) (j : t) (s : σ) :
    vertexExponentEquiv σ t d j s = d (s, j) := by
  change (Finsupp.equivMapDomain (Equiv.prodComm σ t) d).curry j s = _
  rw [Finsupp.curry_apply, Finsupp.equivMapDomain_apply]
  rfl

/-- 指数の余りを頂点ごとの有限台指数に分ける。 -/
def vertexRemainderEquiv (p : ℕ) (σ t : Type*) [Finite t] :
    PolynomialExponentRemainder p (σ × t) ≃ (t → PolynomialExponentRemainder p σ) :=
  ((vertexExponentEquiv σ t).subtypeEquiv
    (q := fun f => ∀ j s, f j s < p) (fun d => by
      simp only [vertexExponentEquiv_apply]
      exact ⟨fun h j s => h (s, j), fun h x => h x.2 x.1⟩)).trans
    { toFun f j := ⟨f.val j, f.property j⟩
      invFun f := ⟨fun j => (f j).val, fun j => (f j).property⟩
      left_inv _ := rfl
      right_inv _ := rfl }

@[simp] theorem vertexRemainderEquiv_apply {p : ℕ} {σ t : Type*} [Finite t]
    (d : PolynomialExponentRemainder p (σ × t)) (j : t) (s : σ) :
    (vertexRemainderEquiv p σ t d j).val s = d.val (s, j) :=
  vertexExponentEquiv_apply d.val j s

private def vertexEmbed {σ t t' : Type*} (e : t ↪ t') : σ × t ↪ σ × t' :=
  (Function.Embedding.refl σ).prodMap e

/-- 頂点の単射に沿って余り指数を移し、像に入らない頂点の指数を零とする。 -/
def vertexRemainderEmbed {p : ℕ} (hp : 0 < p) {σ t t' : Type*} (e : t ↪ t')
    (d : PolynomialExponentRemainder p (σ × t)) :
    PolynomialExponentRemainder p (σ × t') :=
  ⟨d.val.embDomain (vertexEmbed e), fun x => by
    by_cases hx : x ∈ Set.range (vertexEmbed (σ := σ) e)
    · obtain ⟨y, rfl⟩ := hx
      rw [Finsupp.embDomain_apply_self]
      exact d.property y
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ hx]
      exact hp⟩

@[simp] theorem vertexRemainderEmbed_apply_image {p : ℕ} (hp : 0 < p)
    {σ t t' : Type*} (e : t ↪ t') (d : PolynomialExponentRemainder p (σ × t))
    (s : σ) (j : t) :
    (vertexRemainderEmbed hp e d).val (s, e j) = d.val (s, j) :=
  Finsupp.embDomain_apply_self (vertexEmbed e) d.val (s, j)

@[simp] theorem vertexRemainderEmbed_apply_of_notMem {p : ℕ} (hp : 0 < p)
    {σ t t' : Type*} (e : t ↪ t') (d : PolynomialExponentRemainder p (σ × t))
    (s : σ) (j : t') (hj : j ∉ Set.range e) :
    (vertexRemainderEmbed hp e d).val (s, j) = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨⟨s', j'⟩, h⟩
  exact hj ⟨j', congrArg Prod.snd h⟩

/-- 余面で余り指数の単項式を移すと、新しい頂点の指数は零になる。 -/
theorem rename_monomial_vertexRemainderEmbed {p : ℕ} (hp : 0 < p)
    {σ t t' : Type*} {k : Type*} [CommRing k] (e : t ↪ t')
    (d : PolynomialExponentRemainder p (σ × t)) (a : k) :
    MvPolynomial.rename (fun x => (x.1, e x.2)) (MvPolynomial.monomial d.val a) =
      MvPolynomial.monomial (vertexRemainderEmbed hp e d).val a := by
  rw [MvPolynomial.rename_monomial]
  exact congrArg (fun f => MvPolynomial.monomial f a)
    (Finsupp.embDomain_eq_mapDomain (vertexEmbed e) d.val).symm

/-- 余面に沿う指数の付け替えは、新しい頂点に零指数を挿入する。 -/
theorem vertexRemainderEquiv_succAbove {p : ℕ} (hp : 0 < p) {σ : Type*} {n : ℕ}
    (i : Fin (n + 1)) (d : PolynomialExponentRemainder p (σ × Fin n)) :
    vertexRemainderEquiv p σ (Fin (n + 1))
        (vertexRemainderEmbed hp ⟨i.succAbove, Fin.succAbove_right_injective⟩ d) =
      i.insertNth ⟨0, fun _ => hp⟩ (vertexRemainderEquiv p σ (Fin n) d) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun j => ?_) j
  · rw [Fin.insertNth_apply_same]
    apply Subtype.ext
    ext s
    rw [vertexRemainderEquiv_apply, vertexRemainderEmbed_apply_of_notMem]
    · rfl
    · rintro ⟨j, hj⟩
      exact i.succAbove_ne j hj
  · rw [Fin.insertNth_apply_succAbove]
    apply Subtype.ext
    ext s
    rw [vertexRemainderEquiv_apply, vertexRemainderEquiv_apply]
    exact vertexRemainderEmbed_apply_image hp ⟨i.succAbove, Fin.succAbove_right_injective⟩ d s j

section Pushout

open CategoryTheory.Limits
open scoped TensorProduct

variable (p : ℕ) {k : Type u} [CommRing k] {σ : Type}
    {N : CosimplicialObject CommRingCat.{u}} (ι : polynomialCech k σ ⟶ N)

private abbrev P (n : SimplexCategory) := MvPolynomial (σ × Fin (n.len + 1)) k

private abbrev FrobTarget (n : SimplexCategory) :=
  PolynomialExpandTarget p (σ × Fin (n.len + 1)) k

private abbrev FrobPushout := pushout ι (relativeFrobeniusCech p k σ)

private def LeftTarget (n : SimplexCategory) : Type u :=
  let _ := ι
  N.obj n

private instance leftTargetCommRing (n : SimplexCategory) : CommRing (LeftTarget ι n) :=
  inferInstanceAs (CommRing (N.obj n))

private instance leftAlgebra (n : SimplexCategory) :
    Algebra (P (k := k) (σ := σ) n) (LeftTarget ι n) :=
  (ι.app n).hom.toAlgebra

attribute [local instance] polynomialExpandAlgebra

private abbrev PushoutTensor (n : SimplexCategory) :=
  LeftTarget ι n ⊗[P (k := k) (σ := σ) n] FrobTarget p (k := k) (σ := σ) n

private def frobTargetIso (n : SimplexCategory) :
    (polynomialCech k σ).obj n ≅ CommRingCat.of (FrobTarget p (k := k) (σ := σ) n) :=
  (ULift.ringEquiv.symm :
    P (k := k) (σ := σ) n ≃+* FrobTarget p (k := k) (σ := σ) n).toCommRingCatIso

private theorem frobTargetIso_fac (n : SimplexCategory) :
    (relativeFrobeniusCech p k σ).app n ≫ (frobTargetIso p (k := k) (σ := σ) n).hom =
      CommRingCat.ofHom
        (algebraMap (P (k := k) (σ := σ) n) (FrobTarget p (k := k) (σ := σ) n)) := rfl

private def tensorPushoutCocone (n : SimplexCategory) :
    PushoutCocone (ι.app n) ((relativeFrobeniusCech p k σ).app n) :=
  PushoutCocone.mk
    (CommRingCat.pushoutCocone (P (k := k) (σ := σ) n) (LeftTarget ι n)
      (FrobTarget p (k := k) (σ := σ) n)).inl
    ((frobTargetIso p (k := k) (σ := σ) n).hom ≫
      (CommRingCat.pushoutCocone (P (k := k) (σ := σ) n) (LeftTarget ι n)
        (FrobTarget p (k := k) (σ := σ) n)).inr) (by
      rw [← Category.assoc, frobTargetIso_fac]
      exact (CommRingCat.pushoutCocone (P (k := k) (σ := σ) n) (LeftTarget ι n)
        (FrobTarget p (k := k) (σ := σ) n)).condition)

private theorem tensorPushoutIsPushout (n : SimplexCategory) :
    IsPushout (ι.app n) ((relativeFrobeniusCech p k σ).app n)
      (tensorPushoutCocone p ι n).inl (tensorPushoutCocone p ι n).inr := by
  have h := CommRingCat.isPushout_tensorProduct (P (k := k) (σ := σ) n)
    (LeftTarget ι n) (FrobTarget p (k := k) (σ := σ) n)
  apply h.of_iso (Iso.refl _) (Iso.refl _) (frobTargetIso p n).symm (Iso.refl _)
  all_goals rfl

private theorem evaluatedIsPushout (n : SimplexCategory) :
    IsPushout (ι.app n) ((relativeFrobeniusCech p k σ).app n)
      ((pushout.inl ι (relativeFrobeniusCech p k σ)).app n)
      ((pushout.inr ι (relativeFrobeniusCech p k σ)).app n) :=
  ((evaluation SimplexCategory CommRingCat).obj n).map_isPushout
    (IsPushout.of_hasPushout ι (relativeFrobeniusCech p k σ))

private def pushoutTensorIso (n : SimplexCategory) :
    (FrobPushout p ι).obj n ≅ CommRingCat.of (PushoutTensor p ι n) :=
  (evaluatedIsPushout p ι n).isoPushout ≪≫ (tensorPushoutIsPushout p ι n).isoPushout.symm

private theorem expandBasis_apply (hp : 0 < p) (n : SimplexCategory)
    (d : PolynomialExponentRemainder p (σ × Fin (n.len + 1))) :
    polynomialExpandBasis p (σ × Fin (n.len + 1)) k hp d =
      ULift.up (MvPolynomial.monomial d.val 1) := by
  change polynomialExpandCombination p (σ × Fin (n.len + 1)) k (Finsupp.single d 1) = _
  have h := polynomialExpandCombination_single_monomial p (σ × Fin (n.len + 1)) k d 0 1
  simpa only [MvPolynomial.monomial_zero', smul_zero, zero_add, MvPolynomial.C_1] using h

private def frobeniusTensorBasis (hp : 0 < p) (n : SimplexCategory) :
    Module.Basis (Fin (n.len + 1) → PolynomialExponentRemainder p σ) (LeftTarget ι n)
      (PushoutTensor p ι n) :=
  ((polynomialExpandBasis p (σ × Fin (n.len + 1)) k hp).baseChange (LeftTarget ι n)).reindex
    (vertexRemainderEquiv p σ (Fin (n.len + 1)))

private theorem pushoutTensorIso_inl (n : SimplexCategory) :
    (pushout.inl ι (relativeFrobeniusCech p k σ)).app n ≫ (pushoutTensorIso p ι n).hom =
      (tensorPushoutCocone p ι n).inl := by
  change _ ≫ ((evaluatedIsPushout p ι n).isoPushout.hom ≫
    (tensorPushoutIsPushout p ι n).isoPushout.inv) = _
  rw [← Category.assoc, IsPushout.inl_isoPushout_hom, IsPushout.inl_isoPushout_inv]

private theorem pushoutTensorIso_inr (n : SimplexCategory) :
    (pushout.inr ι (relativeFrobeniusCech p k σ)).app n ≫ (pushoutTensorIso p ι n).hom =
      (tensorPushoutCocone p ι n).inr := by
  change _ ≫ ((evaluatedIsPushout p ι n).isoPushout.hom ≫
    (tensorPushoutIsPushout p ι n).isoPushout.inv) = _
  rw [← Category.assoc, IsPushout.inr_isoPushout_hom, IsPushout.inr_isoPushout_inv]

private def frobPushoutBasisTerm (n : SimplexCategory) (a : N.obj n)
    (d : PolynomialExponentRemainder p (σ × Fin (n.len + 1))) :
    (FrobPushout p ι).obj n :=
  (pushout.inl ι (relativeFrobeniusCech p k σ)).app n a *
    (pushout.inr ι (relativeFrobeniusCech p k σ)).app n (MvPolynomial.monomial d.val 1)

private theorem pushoutTensorIso_basisTerm (hp : 0 < p) (n : SimplexCategory) (a : N.obj n)
    (d : PolynomialExponentRemainder p (σ × Fin (n.len + 1))) :
    (pushoutTensorIso p ι n).hom (frobPushoutBasisTerm p ι n a d) =
      (show LeftTarget ι n from a) •
        frobeniusTensorBasis p ι hp n (vertexRemainderEquiv p σ (Fin (n.len + 1)) d) := by
  have hl := ConcreteCategory.congr_hom (pushoutTensorIso_inl p ι n) a
  have hr := ConcreteCategory.congr_hom (pushoutTensorIso_inr p ι n)
    (MvPolynomial.monomial d.val (1 : k))
  change (pushoutTensorIso p ι n).hom
      ((pushout.inl ι (relativeFrobeniusCech p k σ)).app n a) =
    Algebra.TensorProduct.includeLeftRingHom
    (R := P (k := k) (σ := σ) n) (B := FrobTarget p (k := k) (σ := σ) n)
    (show LeftTarget ι n from a) at hl
  change (pushoutTensorIso p ι n).hom
      ((pushout.inr ι (relativeFrobeniusCech p k σ)).app n (MvPolynomial.monomial d.val 1)) =
    Algebra.TensorProduct.includeRight (R := P (k := k) (σ := σ) n)
      (A := LeftTarget ι n) (B := FrobTarget p (k := k) (σ := σ) n)
      (ULift.up (MvPolynomial.monomial d.val 1)) at hr
  simp only [frobPushoutBasisTerm, map_mul, frobeniusTensorBasis, Module.Basis.reindex_apply,
    Equiv.symm_apply_apply, Module.Basis.baseChange_apply, expandBasis_apply]
  change ((pushoutTensorIso p ι n).hom _ * (pushoutTensorIso p ι n).hom _) = _
  rw [hl, hr]
  exact (Algebra.smul_def _ _).symm

private theorem frobPushoutBasisTerm_coface (hp : 0 < p) (n : ℕ) (i : Fin (n + 2))
    (a : N.obj ⦋n⦌) (d : PolynomialExponentRemainder p (σ × Fin (n + 1))) :
    (FrobPushout p ι).map (SimplexCategory.δ i) (frobPushoutBasisTerm p ι ⦋n⦌ a d) =
      frobPushoutBasisTerm p ι ⦋n + 1⦌ (N.map (SimplexCategory.δ i) a)
        (vertexRemainderEmbed hp ⟨i.succAbove, Fin.succAbove_right_injective⟩ d) := by
  let fr := relativeFrobeniusCech p k σ
  let θ : ⦋n⦌ ⟶ ⦋n + 1⦌ := SimplexCategory.δ i
  have hl := ConcreteCategory.congr_hom ((pushout.inl ι fr).naturality θ).symm a
  have hr := ConcreteCategory.congr_hom ((pushout.inr ι fr).naturality θ).symm
    (MvPolynomial.monomial d.val (1 : k))
  simp only [frobPushoutBasisTerm, map_mul]
  change (_ : (FrobPushout p ι).obj _) = _
  rw [show (FrobPushout p ι).map θ ((pushout.inl ι fr).app _ a) = _ from hl]
  rw [show (FrobPushout p ι).map θ ((pushout.inr ι fr).app _ (MvPolynomial.monomial d.val 1))
      = _ from hr]
  congr 1
  exact congrArg ((pushout.inr ι fr).app ⦋n + 1⦌)
    (rename_monomial_vertexRemainderEmbed hp ⟨i.succAbove, Fin.succAbove_right_injective⟩ d 1)

/-- 相対 Frobenius に沿う押し出しを、各頂点の余り指数で添字づけた自由和に分解する。 -/
def frobeniusPushoutRepr (hp : 0 < p) (n : SimplexCategory) :
    ((pushout ι (relativeFrobeniusCech p k σ)).obj n) ≃+
      ((Fin (n.len + 1) → PolynomialExponentRemainder p σ) →₀ N.obj n) :=
  (pushoutTensorIso p ι n).commRingCatIsoToRingEquiv.toAddEquiv.trans
    (frobeniusTensorBasis p ι hp n).repr.toAddEquiv

private theorem frobeniusPushoutRepr_basisTerm (hp : 0 < p) (n : SimplexCategory)
    (a : N.obj n) (d : PolynomialExponentRemainder p (σ × Fin (n.len + 1))) :
    frobeniusPushoutRepr p ι hp n (frobPushoutBasisTerm p ι n a d) =
      Finsupp.single (vertexRemainderEquiv p σ (Fin (n.len + 1)) d) a := by
  let e := vertexRemainderEquiv p σ (Fin (n.len + 1)) d
  let b := frobeniusTensorBasis p ι hp n
  change b.repr ((pushoutTensorIso p ι n).hom _) =
    (Finsupp.single e a : _ →₀ LeftTarget ι n)
  rw [pushoutTensorIso_basisTerm p ι hp, map_smul]
  change (show LeftTarget ι n from a) • b.repr (b e) = _
  rw [b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- 分解のもとで、左からの包含はすべての頂点の余り指数が零である成分への包含。 -/
theorem frobeniusPushoutRepr_inl (hp : 0 < p) (n : SimplexCategory) (a : N.obj n) :
    frobeniusPushoutRepr p ι hp n ((pushout.inl ι (relativeFrobeniusCech p k σ)).app n a) =
      Finsupp.single (fun _ => ⟨0, fun _ => hp⟩) a := by
  let z : PolynomialExponentRemainder p (σ × Fin (n.len + 1)) := ⟨0, fun _ => hp⟩
  have hz : vertexRemainderEquiv p σ (Fin (n.len + 1)) z = fun _ => ⟨0, fun _ => hp⟩ := by
    funext j
    apply Subtype.ext
    ext s
    rw [vertexRemainderEquiv_apply]
    rfl
  have h := frobeniusPushoutRepr_basisTerm p ι hp n a z
  rw [hz] at h
  have hmon : MvPolynomial.monomial z.val (1 : k) = 1 := by simp [z]
  unfold frobPushoutBasisTerm at h
  rw [hmon] at h
  change frobeniusPushoutRepr p ι hp n
    (((pushout.inl ι (relativeFrobeniusCech p k σ)).app n).hom a *
      ((pushout.inr ι (relativeFrobeniusCech p k σ)).app n).hom 1) = _ at h
  rw [map_one, mul_one] at h
  exact h

/-- 余面は係数に `N` の余面を施し、新しい頂点に零指数を挿入する。 -/
theorem frobeniusPushoutRepr_coface_single (hp : 0 < p) (n : ℕ) (i : Fin (n + 2))
    (a : N.obj ⦋n⦌) (t : Fin (n + 1) → PolynomialExponentRemainder p σ) :
    frobeniusPushoutRepr p ι hp ⦋n + 1⦌
      ((pushout ι (relativeFrobeniusCech p k σ)).map (SimplexCategory.δ i)
        ((frobeniusPushoutRepr p ι hp ⦋n⦌).symm (Finsupp.single t a))) =
      Finsupp.single (i.insertNth ⟨0, fun _ => hp⟩ t) (N.map (SimplexCategory.δ i) a) := by
  let e := vertexRemainderEquiv p σ (Fin (n + 1))
  obtain ⟨d, rfl⟩ := e.surjective t
  rw [← frobeniusPushoutRepr_basisTerm p ι hp ⦋n⦌ a d,
    AddEquiv.symm_apply_apply, frobPushoutBasisTerm_coface p ι hp,
    frobeniusPushoutRepr_basisTerm p ι hp, vertexRemainderEquiv_succAbove]

end Pushout

end SerrePositivity.BhattScholze.Prismatic
