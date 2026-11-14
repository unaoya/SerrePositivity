module

public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.CommutativeAlgebra.Adic.RingRetract
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Logic.Equiv.Set

/-!
# 濃度を制限した prismatic site の本質的小ささ

BS 著者版 Definition 4.1 の affine site を、小さい圏へ置き換えるための補題。
κ の代表型の部分集合へ対象の構造を同型で移し、その全体からの本質的全射な
充満忠実関手を作る。濃度の下限は不要で、濃度制限 κ 自体は変更しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze
namespace OrientedPrism
variable {p : ℕ} [Fact p.Prime] {B C : Type u} [CommRing B] [CommRing C]

/-- 環同型に沿って向き付き prism の構造を移す。
生成元はその像、δ 構造は同型の逆による引き戻し。完備性は分裂環射の既存の補題で移す。
site の小さい模型で使い、生成元の選び直しはしない。 -/
def transport (Q : OrientedPrism p B) (e : B ≃+* C) : OrientedPrism p C :=
  ofDistinguished (Q.deltaStructure.comapEquiv e.symm) (e Q.generator)
    ((Q.deltaStructure.comapEquiv_symm_isDeltaHom e.symm).map_isDistinguished
      Q.isDistinguished_generator)
    (by
      intro x y h
      apply e.symm.injective
      apply Q.generator_regular
      simpa only [map_mul, RingEquiv.symm_apply_apply] using congrArg e.symm h)
    (by
      apply DerivedCompletion.isModuleComplete_of_ring_retract e.symm.toRingHom
        e.toRingHom e.apply_symm_apply (p : C)
      simpa only [map_natCast] using Q.complete_p)
    (by
      apply DerivedCompletion.isModuleComplete_of_ring_retract e.symm.toRingHom
        e.toRingHom e.apply_symm_apply (e Q.generator)
      simpa using Q.complete_generator)

/-- 移送に使った環同型は prism の射になる。 -/
def transportHom (Q : OrientedPrism p B) (e : B ≃+* C) : Hom Q (Q.transport e) where
  toRingHom := e.toRingHom
  map_delta := Q.deltaStructure.comapEquiv_symm_isDeltaHom e.symm
  ideal_le := by
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change e Q.generator ∈ Ideal.span {e Q.generator}
    exact Ideal.mem_span_singleton_self _

/-- 移送の逆の環同型も prism の射になる。 -/
def transportInv (Q : OrientedPrism p B) (e : B ≃+* C) : Hom (Q.transport e) Q where
  toRingHom := e.symm.toRingHom
  map_delta := Q.deltaStructure.comapEquiv_isDeltaHom e.symm
  ideal_le := by
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change e.symm (e Q.generator) ∈ Q.ideal
    rw [e.symm_apply_apply]
    exact Ideal.mem_span_singleton_self _

/-- 移送の往復は元の prism の恒等射。 -/
@[simp] theorem transportInv_comp_transportHom (Q : OrientedPrism p B) (e : B ≃+* C) :
    (Q.transportInv e).comp (Q.transportHom e) = Hom.id Q := by
  apply Hom.ext
  ext x
  exact e.symm_apply_apply x

/-- 移送の逆の往復も恒等射。 -/
@[simp] theorem transportHom_comp_transportInv (Q : OrientedPrism p B) (e : B ≃+* C) :
    (Q.transportHom e).comp (Q.transportInv e) = Hom.id (Q.transport e) := by
  apply Hom.ext
  ext x
  exact e.apply_symm_apply x

/-- 同型による移送は prism の有界性を保つ。
剰余環の同型でねじれ指数をそのまま移す。 -/
theorem transport_bounded (Q : OrientedPrism p B) (e : B ≃+* C)
    (hQ : Prismatic.IsBoundedPrism Q) : Prismatic.IsBoundedPrism (Q.transport e) := by
  let q := (Q.transportHom e).quotientEquiv e.bijective
  obtain ⟨N, hN⟩ := hQ
  refine ⟨N, fun n x hx => ?_⟩
  apply q.symm.injective
  simpa only [map_zero, map_mul, map_pow, map_natCast] using
    hN n (q.symm x) (by simpa only [map_zero, map_mul, map_pow, map_natCast] using congrArg q.symm hx)

end OrientedPrism
namespace Prismatic.PrismOver
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}
variable (X : PrismOver P R κ) {D : Type u} [CommRing D] (e : X.B ≃+* D)
variable (hs : Cardinal.mk D ≤ κ)

/-- prismatic site の対象を同型の台へ移す。
基底脚と剰余環への脚も移送するので、元のRとcutoffを保つ。 -/
def transport : PrismOver P R κ where
  B := D
  Q := X.Q.transport e
  bounded := X.Q.transport_bounded e X.bounded
  toHom := (X.Q.transportHom e).comp X.toHom
  sec := (X.Q.transportHom e).quotientMap.comp X.sec
  sec_comp := by
    rw [RingHom.comp_assoc, X.sec_comp, OrientedPrism.Hom.quotientMap_comp]
  small := hs

/-- 移送先への site の射。二つの脚の可換性は移送の定義そのもの。 -/
def transportHom : X ⟶ X.transport e hs where
  toHom := X.Q.transportHom e
  comm_base := rfl
  comm_sec := rfl

/-- 移送元への site の逆射。prism 射の往復の恒等性を剰余環にも適用する。 -/
def transportInv : X.transport e hs ⟶ X where
  toHom := X.Q.transportInv e
  comm_base := by
    change (X.Q.transportInv e).comp ((X.Q.transportHom e).comp X.toHom) = X.toHom
    rw [← OrientedPrism.Hom.comp_assoc, OrientedPrism.transportInv_comp_transportHom,
      OrientedPrism.Hom.id_comp]
  comm_sec := by
    change (X.Q.transportInv e).quotientMap.comp ((X.Q.transportHom e).quotientMap.comp X.sec) = X.sec
    rw [← RingHom.comp_assoc, ← OrientedPrism.Hom.quotientMap_comp,
      OrientedPrism.transportInv_comp_transportHom, OrientedPrism.Hom.quotientMap_id,
      RingHom.id_comp]

/-- 環同型による移送は prismatic site で同型を与える。 -/
def transportIso : X ≅ X.transport e hs where
  hom := X.transportHom e hs
  inv := X.transportInv e hs
  hom_inv_id := by
    apply Hom.ext
    exact X.Q.transportInv_comp_transportHom e
  inv_hom_id := by
    apply Hom.ext
    exact X.Q.transportHom_comp_transportInv e

/-- κ の代表型の部分集合を台とする site の対象のデータ。
環・δ・剰余への脚をすべて保持し、Homの条件を弱めない。 -/
structure CarrierModel (P : OrientedPrism p A) (R : Type u) [CommRing R]
    [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u}) where
  /-- 固定した型の部分集合。 -/
  support : Set κ.out
  /-- 部分集合上の可換環。 -/
  [ring : CommRing support]
  /-- 向き付き prism 構造。 -/
  Q : OrientedPrism p support
  /-- 有界性。 -/
  bounded : IsBoundedPrism Q
  /-- 基底からの prism 射。 -/
  toHom : OrientedPrism.Hom P Q
  /-- 剰余への構造射。 -/
  sec : R →+* support ⧸ Q.ideal
  /-- 剰余の構造射が基底と可換する法則。 -/
  sec_comp : sec.comp (algebraMap (A ⧸ P.ideal) R) = toHom.quotientMap

attribute [instance] CarrierModel.ring

/-- 固定した台のデータを元のsiteの対象に戻す。濃度条件は部分集合から従う。 -/
def CarrierModel.toOver (X : CarrierModel P R κ) : PrismOver P R κ where
  B := X.support
  Q := X.Q
  bounded := X.bounded
  toHom := X.toHom
  sec := X.sec
  sec_comp := X.sec_comp
  small := (Cardinal.mk_subtype_le _).trans (Cardinal.mk_out κ).le

/-- 小さい台のデータに元のsiteから射を誘導した圏。 -/
abbrev CarrierCategory := InducedCategory (PrismOver P R κ) (CarrierModel.toOver (P := P) (R := R) (κ := κ))

/-- 小さい台のデータからの充満忠実な関手。 -/
abbrev carrierFunctor : CarrierCategory (P := P) (R := R) (κ := κ) ⥤ PrismOver P R κ :=
  inducedFunctor (CarrierModel.toOver (P := P) (R := R) (κ := κ))

instance : (carrierFunctor (P := P) (R := R) (κ := κ)).EssSurj where
  mem_essImage X := by
    have h : Cardinal.mk X.B ≤ Cardinal.mk κ.out := by
      simpa only [Cardinal.mk_out] using X.small
    obtain ⟨i⟩ := (Cardinal.le_def X.B κ.out).mp h
    let e0 : Set.range i ≃ X.B := (Equiv.ofInjective i i.injective).symm
    letI : CommRing (Set.range i) := e0.commRing
    let e : X.B ≃+* Set.range i := e0.ringEquiv.symm
    have hs : Cardinal.mk (Set.range i) ≤ κ :=
      (Cardinal.mk_subtype_le _).trans (Cardinal.mk_out κ).le
    let Y := X.transport e hs
    let Z : CarrierModel P R κ := {
      support := Set.range i
      ring := Y.ring
      Q := Y.Q
      bounded := Y.bounded
      toHom := Y.toHom
      sec := Y.sec
      sec_comp := Y.sec_comp }
    exact ⟨Z, ⟨(X.transportIso e hs).symm⟩⟩

/-- 濃度≤κの向き付き prismatic site は元の宇宙で本質的に小さい。
小さい台の誘導圏からの充満忠実かつ本質的全射な関手を同値にする。
κの下限や追加の完備性は仮定しない。 -/
theorem essentiallySmall : EssentiallySmall.{u} (PrismOver P R κ) := by
  let : (carrierFunctor (P := P) (R := R) (κ := κ)).IsEquivalence := {}
  exact EssentiallySmall.mk' (carrierFunctor (P := P) (R := R) (κ := κ)).asEquivalence.symm

end Prismatic.PrismOver
namespace Prismatic
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u})

instance : EssentiallySmall.{u} (PrismOver P R κ) := PrismOver.essentiallySmall

end Prismatic
end SerrePositivity.BhattScholze
