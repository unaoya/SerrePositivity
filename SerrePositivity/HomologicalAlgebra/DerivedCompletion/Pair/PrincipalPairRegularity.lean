module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Reflection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.Koszul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.Iteration
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Milnor
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Order.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Defs
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.RegularSwap

public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-!
# 主完備化による正則対の保存

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v

/-! ## André E1・E2：三元正則性の関係追加による保存（旧 Andre/Remark715/RegularTripleQuotientStep.lean）

## 概要

a が正則で、mod a の c と g、および mod(a,c) の g が正則なら、
g を課した後も a と mod a の c は正則。
BS 著者版 Remark 7.15（著者版 p.62）の有限 δ 関係商の同時帰納法に使う。

## 方針

正則対の順序交換を二度使い、二重主イデアル商の順序を交換する。

## 規約

任意の可換環を扱い、完備性・局所性・非零性を要求しない。

## 使われ方

a=p、c=d、g=次の δ 関係として有限段へ適用する。
-/

@[expose] public noncomputable section RegularTripleQuotientStep

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- 概要：環同型は指定元の正則性を保存・反映する。
方針：積の等式を順射と逆射で移して消去する。
規約：両側の自然な自己加群作用を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実商同型による正則性の移送。 -/
theorem ringEquiv_isSMulRegular (e : R ≃+* S) (r : R) :
    IsSMulRegular R r ↔ IsSMulRegular S (e r) := by
  constructor
  · intro hr x y hxy
    apply e.symm.injective
    apply hr
    simpa only [smul_eq_mul, map_mul, RingEquiv.symm_apply_apply] using congrArg e.symm hxy
  · intro hr x y hxy
    apply e.injective
    apply hr
    simpa only [smul_eq_mul, map_mul] using congrArg e hxy

end SerrePositivity.BhattScholze.Andre

end RegularTripleQuotientStep

/-! ## André E1・E2：正則対の主冪商と第一完備化（旧 Andre/Remark715/PrincipalPairPowerRegular.lean）

## 概要

b が正則で c が mod b で正則なら、c は全ての mod bⁿ と b 完備化で正則。
BS 著者版 Remark 7.15（著者版 p.62）の正則対を完備化へ移すための一般環計算。

## 方針

c 倍が bⁿ で割り切れることから元の bⁿ 可除性を帰納し、完備化の各座標へ適用する。

## 規約

Noether 性・平坦性・b 完備性は要求しない。導来二座標完備化との比較は別工程。

## 使われ方

一元 raw 包の正則対から、その p 完備化における分母正則性を得る。
-/

@[expose] public noncomputable section PrincipalPairPowerRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (b c : R) (hb : IsSMulRegular R b)
variable (hc : IsSMulRegular (R ⧸ Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) c))
include hb hc

/-- 概要：正則対の第一元の冪イデアルは第二元で飽和している。
方針：mod b で一度消去し、第一元の正則性で b を消して帰納する。
規約：零乗も含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全主冪商での分母正則性。 -/
theorem principalPairPower_saturated (n : ℕ) (x : R)
    (hx : c * x ∈ Ideal.span {b ^ n}) : x ∈ Ideal.span {b ^ n} := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hmod : Ideal.Quotient.mk (Ideal.span {b}) x = 0 := by
      apply hc
      change Ideal.Quotient.mk (Ideal.span {b}) c *
        Ideal.Quotient.mk (Ideal.span {b}) x = _ * 0
      rw [mul_zero, ← map_mul]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hx' : b ∣ c * x := by
        exact (dvd_pow_self b (by omega : n + 1 ≠ 0)).trans
          (Ideal.mem_span_singleton.mp hx)
      exact Ideal.mem_span_singleton.mpr hx'
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hmod)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hx
    have hcy : c * y = b ^ n * z := by
      apply hb
      change b * (c * y) = b * (b ^ n * z)
      simpa only [hy, pow_succ', mul_assoc, mul_left_comm] using hz
    have hym : y ∈ Ideal.span {b ^ n} := ih y (by
      rw [hcy]
      exact Ideal.mem_span_singleton.mpr ⟨z, rfl⟩)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hym
    apply Ideal.mem_span_singleton.mpr
    refine ⟨w, ?_⟩
    simp only [hy, hw, pow_succ', mul_assoc]

/-- 概要：正則対の第二元は第一元の任意の主冪商で正則。
方針：第一元の冪イデアルの飽和性を代表元に適用する。
規約：商上の第二元の像をスカラーとする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の古典的主完備化の座標計算。 -/
theorem principalPairPower_quotient_regular (n : ℕ) :
    IsSMulRegular (R ⧸ Ideal.span {b ^ n}) (Ideal.Quotient.mk (Ideal.span {b ^ n}) c) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply principalPairPower_saturated b c hb hc n t
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul, smul_eq_mul] using hx

/-- 概要：正則対の第二元は第一元の古典的完備化でも正則。
方針：全ての主冪商で消去し、完備化の座標の単射性を使う。
規約：元の環の完備性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の反復完備化の第一段。 -/
theorem principalPair_adicCompletion_second_regular :
    IsSMulRegular (AdicCompletion (Ideal.span {b}) R)
      (algebraMap R (AdicCompletion (Ideal.span {b}) R) c) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  apply AdicCompletion.ext_evalₐ
  intro n
  have hreg : IsSMulRegular (R ⧸ (Ideal.span {b}) ^ n)
      (Ideal.Quotient.mk ((Ideal.span {b}) ^ n) c) := by
    rw [Ideal.span_singleton_pow]
    exact principalPairPower_quotient_regular b c hb hc n
  apply hreg
  change Ideal.Quotient.mk ((Ideal.span {b}) ^ n) c *
    AdicCompletion.evalₐ (Ideal.span {b}) n x = _ * _
  simpa only [map_zero, map_mul, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AdicCompletion.evalₐ_of, smul_eq_mul, mul_zero] using
    congrArg (AdicCompletion.evalₐ (Ideal.span {b}) n) hx

end SerrePositivity.BhattScholze.Andre

end PrincipalPairPowerRegular

/-! ## André E1・E2：実二座標完備化での第二元の正則性（旧 Andre/Remark715/PrincipalPairCompletionRegular.lean）

## 概要

正則対 b,c の第二元は、実二座標導来完備化の H⁰ でも正則。
BS 著者版 Remark 7.15（著者版 p.62）の分母の新しいねじれの排除。

## 方針

第一主完備化を古典的完備化へ移して c の正則性を示す。
その実 H⁰ を c で再び完備化し、標準写像を保つ反復比較で戻す。

## 規約

実 Koszul 完備化の H⁰ と標準射を使う。第一元の正則性の保存は別の主張。

## 使われ方

無限根モニック raw 包の実完備化の分母正則性。
-/

@[expose] public noncomputable section PrincipalPairCompletionRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] (b c : R) (hb : IsSMulRegular R b)
variable (hc : IsSMulRegular (R ⧸ Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) c))
include hb hc

/-- 概要：第二元は第一元の実主完備化 H⁰ で正則。
方針：標準射を保つ古典的完備化比較で主冪商の計算を移す。
規約：元の実 H⁰ を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の反復完備化の入力。 -/
theorem principalPair_principalCompletion_second_regular :
    let := principalCompletionCommRing R b
    IsSMulRegular (PrincipalCompletionH0 R b) (principalCompletionUnitRingHom R b c) := by
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  let e := principalCompletionAdicAlgEquiv R b hb
  apply (ringEquiv_isSMulRegular e.toRingEquiv _).mpr
  change IsSMulRegular (AdicCompletion (Ideal.span {b}) R)
    (e (principalCompletionUnitRingHom R b c))
  rw [principalCompletionAdicAlgEquiv_unit]
  exact principalPair_adicCompletion_second_regular b c hb hc

/-- 概要：第二元は実二座標導来完備化 H⁰ で正則。
方針：第一主完備化での正則性から第二主完備化で消去し、実反復同型で戻す。
規約：標準射の第二元の像を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化の分母正則性。 -/
theorem principalPair_pairCompletion_second_regular :
    let := pairCompletionCommRing R b c
    IsSMulRegular (PairCompletionH0 R b c) (pairCompletionUnitRingHom R b c c) := by
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  let B := PrincipalCompletionH0 R b
  let cb := principalCompletionUnitRingHom R b c
  have hcb : IsSMulRegular B cb := principalPair_principalCompletion_second_regular b c hb hc
  let := iteratedCompletionCommRing R b c
  let := principalCompletionAlgebra B cb
  have hi : IsSMulRegular (IteratedCompletionH0 R b c)
      (iteratedCompletionUnitRingHom R b c c) := by
    have hs := principalCompletionH0_smul_injective_of_regular B cb hcb
    intro x y hxy
    apply hs
    change cb • x = cb • y
    change principalCompletionUnitRingHom B cb cb * x =
      principalCompletionUnitRingHom B cb cb * y at hxy
    change (principalCompletionH0_isCompleteModuleReflection B cb).mul
      ((principalCompletionH0_isCompleteModuleReflection B cb).unitRingHom cb) x =
      (principalCompletionH0_isCompleteModuleReflection B cb).mul
        ((principalCompletionH0_isCompleteModuleReflection B cb).unitRingHom cb) y at hxy
    simpa only [IsCompleteModuleReflection.unitRingHom_apply,
      IsCompleteModuleReflection.mul_scalar_unit] using hxy
  let := pairCompletionCommRing R b c
  let e := pairCompletionIteratedEquiv R b c
  apply (ringEquiv_isSMulRegular e _).mpr
  simpa only [e, pairCompletionIteratedEquiv_unit] using hi

end SerrePositivity.BhattScholze.Andre

end PrincipalPairCompletionRegular

/-! ## André E1・E2：実主完備化の第一剰余（旧 Andre/Remark715/PrincipalCompletionResidue.lean）

## 概要

実主完備化の H⁰ を標準像の主イデアルで割ると、元の主剰余環と同型になる。
BS 著者版 Remark 7.15（著者版 p.62）の正則対を完備化へ移す比較。

## 方針

座標を殺す環への実 H⁰ の一意延長から互いに逆の射を作る。

## 規約

正則性・Noether 性を仮定せず、元の標準射を保持する。

## 使われ方

第一完備化の mod p における分母正則性を元の raw 包から移す。
-/

@[expose] public noncomputable section PrincipalCompletionResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion

/-- 概要：座標の像が零の環は制限スカラー作用でその座標について導来完備。
方針：一乗のスカラー作用が零であることを使う。
規約：零環も含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実主完備化の剰余普遍性。 -/
theorem moduleComplete_of_ringHom_scalar_zero {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (b : R) (hb : g b = 0) :
    let := g.toAlgebra
    IsModuleComplete R b (ModuleCat.of R S) := by
  let := g.toAlgebra
  apply isModuleComplete_of_pow_smul_zero R b (ModuleCat.of R S) 1
  intro x
  change g (b ^ 1) * x = 0
  rw [pow_one, hb, zero_mul]

variable {R : Type u} [CommRing R] (b : R)

/-- 概要：実主完備化 H⁰ の標準座標の主剰余は元の主剰余と環同型。
方針：両剰余で座標が零となることを一意延長へ渡して逆合成を確認する。
規約：正則性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の第一完備化の正則対。 -/
def principalCompletionResidueEquiv :
    letI := principalCompletionCommRing R b
    (PrincipalCompletionH0 R b ⧸ Ideal.span {principalCompletionUnitRingHom R b b}) ≃+*
      R ⧸ Ideal.span {b} := by
  let := principalCompletionCommRing R b
  let H := PrincipalCompletionH0 R b
  let j := principalCompletionUnitRingHom R b
  let I := Ideal.span {b}
  let J := Ideal.span {j b}
  let q := Ideal.Quotient.mk I
  let qH := Ideal.Quotient.mk J
  have hq : q b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b)
  have hqH : qH (j b) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (j b))
  let k := (principalCompletion_existsUnique_ringHom R b (R ⧸ I) q
    (moduleComplete_of_ringHom_scalar_zero q b hq)).choose
  have hk : k.comp j = q := (principalCompletion_existsUnique_ringHom R b (R ⧸ I) q
    (moduleComplete_of_ringHom_scalar_zero q b hq)).choose_spec.1
  let F : R ⧸ I →+* H ⧸ J := Ideal.Quotient.lift I (qH.comp j) (by
    change I ≤ RingHom.ker (qH.comp j)
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    exact hqH)
  let G : H ⧸ J →+* R ⧸ I := Ideal.Quotient.lift J k (by
    change J ≤ RingHom.ker k
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    change k (j b) = 0
    rw [← RingHom.comp_apply, hk]
    exact hq)
  have hGF : G.comp F = RingHom.id (R ⧸ I) := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    change k (j r) = q r
    exact RingHom.congr_fun hk r
  have hFG : F.comp G = RingHom.id (H ⧸ J) := by
    apply Ideal.Quotient.ringHom_ext
    change F.comp k = qH
    have he : (F.comp k).comp j = qH.comp j := by
      rw [RingHom.comp_assoc, hk]
      rfl
    obtain ⟨l, hl, hlu⟩ := principalCompletion_existsUnique_ringHom R b (H ⧸ J) (qH.comp j)
      (moduleComplete_of_ringHom_scalar_zero (qH.comp j) b hqH)
    exact (hlu _ he).trans (hlu _ rfl).symm
  exact RingEquiv.ofRingHom G F hGF hFG

/-- 概要：実主完備化の剰余比較は係数の標準像を元の代表元へ送る。
方針：選択した一意延長の合成仕様を評価する。
規約：任意の元 r を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の第二元正則性の移送。 -/
theorem principalCompletionResidueEquiv_unit (r : R) :
    letI := principalCompletionCommRing R b
    principalCompletionResidueEquiv b
      (Ideal.Quotient.mk _ (principalCompletionUnitRingHom R b r)) =
        Ideal.Quotient.mk (Ideal.span {b}) r := by
  let := principalCompletionCommRing R b
  exact RingHom.congr_fun
    (principalCompletion_existsUnique_ringHom R b (R ⧸ Ideal.span {b})
      (Ideal.Quotient.mk (Ideal.span {b}))
      (moduleComplete_of_ringHom_scalar_zero _ b
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))))).choose_spec.1 r

end SerrePositivity.BhattScholze.Andre

end PrincipalCompletionResidue

/-! ## André E1・E2：実二座標完備化と第二元商での第一元正則性（旧 Andre/Remark715/PrincipalPairCompletionFirstRegular.lean）

## 概要

正則対 b,c に対し、実二座標完備化 H⁰ およびその c 商で b は正則。
BS 著者版 Remark 7.15（著者版 p.62）の p ねじれなしの場合の完備化計算。

## 方針

第一主完備化の mod b 比較で正則対を保ち、順序交換してから第二主完備化を行う。
第二主完備化の主剰余比較も使い、元の実二座標 H⁰ へ反復比較で戻す。

## 規約

元の Koszul 完備化と標準射を保持する。Noether 性は要求しない。

## 使われ方

無限根モニック raw 包の実完備化と Hodge–Tate 商の p 正則性。
-/

@[expose] public noncomputable section PrincipalPairCompletionFirstRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] (b c : R) (hb : IsSMulRegular R b)
variable (hc : IsSMulRegular (R ⧸ Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) c))
include hb hc

/-- 概要：第一主完備化でも元の正則対は正則対。
方針：第一元の正則性を古典的比較で、第二元の mod 第一元正則性を剰余比較で移す。
規約：主完備化の元の標準射を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の反復完備化前の順序交換。 -/
theorem principalPair_principalCompletion_pair_regular :
    let := principalCompletionCommRing R b
    let j := principalCompletionUnitRingHom R b
    IsSMulRegular (PrincipalCompletionH0 R b) (j b) ∧
      IsSMulRegular (PrincipalCompletionH0 R b ⧸ Ideal.span {j b})
        (Ideal.Quotient.mk (Ideal.span {j b}) (j c)) := by
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  constructor
  · let e := principalCompletionAdicAlgEquiv R b hb
    apply (ringEquiv_isSMulRegular e.toRingEquiv _).mpr
    change IsSMulRegular (AdicCompletion (Ideal.span {b}) R)
      (e (principalCompletionUnitRingHom R b b))
    rw [principalCompletionAdicAlgEquiv_unit]
    exact isSMulRegular_adicCompletion_span_singleton R b hb
  · apply (ringEquiv_isSMulRegular (principalCompletionResidueEquiv b) _).mpr
    rw [principalCompletionResidueEquiv_unit]
    exact hc

/-- 概要：第一元は実二座標完備化 H⁰ で正則。
方針：第一主完備化で正則対を交換し、第二主完備化での第二元正則性を使う。
規約：元の二座標 H⁰ と標準射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化の p 正則性。 -/
theorem principalPair_pairCompletion_first_regular :
    let := pairCompletionCommRing R b c
    IsSMulRegular (PairCompletionH0 R b c) (pairCompletionUnitRingHom R b c b) := by
  let := principalCompletionCommRing R b
  let B := PrincipalCompletionH0 R b
  let j := principalCompletionUnitRingHom R b
  have hB := principalPair_principalCompletion_pair_regular b c hb hc
  have hcB := principalPair_principalCompletion_second_regular b c hb hc
  have hbBc := principal_regular_swap (j b) (j c) hB.1 hB.2
  have hi := principalPair_principalCompletion_second_regular (j c) (j b) hcB hbBc
  let := iteratedCompletionCommRing R b c
  let := pairCompletionCommRing R b c
  apply (ringEquiv_isSMulRegular (pairCompletionIteratedEquiv R b c) _).mpr
  rw [pairCompletionIteratedEquiv_unit]
  exact hi

/-- 概要：第二元で割った実二座標完備化でも第一元は正則。
方針：第一主完備化で正則対を交換し、第二主完備化の主剰余比較で戻す。
規約：両方の元は元の環の標準完備化像。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Hodge–Tate 商の p 正則性。 -/
theorem principalPair_pairCompletion_mod_second_first_regular :
    let := pairCompletionCommRing R b c
    let j := pairCompletionUnitRingHom R b c
    IsSMulRegular (PairCompletionH0 R b c ⧸ Ideal.span {j c})
      (Ideal.Quotient.mk (Ideal.span {j c}) (j b)) := by
  let := principalCompletionCommRing R b
  let B := PrincipalCompletionH0 R b
  let j := principalCompletionUnitRingHom R b
  have hB := principalPair_principalCompletion_pair_regular b c hb hc
  have hbBc := principal_regular_swap (j b) (j c) hB.1 hB.2
  let := iteratedCompletionCommRing R b c
  have hi : IsSMulRegular (IteratedCompletionH0 R b c ⧸
      Ideal.span {iteratedCompletionUnitRingHom R b c c})
      (Ideal.Quotient.mk (Ideal.span {iteratedCompletionUnitRingHom R b c c})
        (iteratedCompletionUnitRingHom R b c b)) := by
    apply (ringEquiv_isSMulRegular (principalCompletionResidueEquiv (j c)) _).mpr
    change IsSMulRegular (B ⧸ Ideal.span {j c})
      (principalCompletionResidueEquiv (j c)
        (Ideal.Quotient.mk _ (principalCompletionUnitRingHom B (j c) (j b))))
    rw [principalCompletionResidueEquiv_unit]
    exact hbBc
  let := pairCompletionCommRing R b c
  let e := pairCompletionIteratedEquiv R b c
  let eQ := Ideal.quotientEquiv (Ideal.span {pairCompletionUnitRingHom R b c c})
    (Ideal.span {iteratedCompletionUnitRingHom R b c c}) e (by
      rw [Ideal.map_span, Set.image_singleton]
      simp only [e, RingEquiv.coe_toRingHom,
        pairCompletionIteratedEquiv_unit])
  apply (ringEquiv_isSMulRegular eQ _).mpr
  simpa only [eQ, e, Ideal.quotientEquiv_mk, pairCompletionIteratedEquiv_unit] using hi

end SerrePositivity.BhattScholze.Andre

end PrincipalPairCompletionFirstRegular
