module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import Mathlib.NumberTheory.Padics.RingHoms
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# 結晶基底の向き付き prism

## 概要
標準の δ 構造と生成元 p を持つ `(ℤ_p, (p))` を構成し、剰余体を `ZMod p` と同一視する。

## 方針
Frobenius の持ち上げを恒等射として δ 構造を構成する。

## 規約
宇宙を多項式とそろえるため `ULift` を使う。

## 使われ方
多項式の結晶比較。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime]

/-- 結晶基底の台環。 -/
abbrev crystallineBase := ULift.{u} (PadicInt p)

private def padicLiftEquiv : crystallineBase.{u} p ≃+* PadicInt p := ULift.ringEquiv

private theorem padicLiftIdeal :
    (Ideal.span {(p : crystallineBase.{u} p)}).map (padicLiftEquiv p).toRingHom =
      IsLocalRing.maximalIdeal (PadicInt p) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, RingEquiv.toRingHom_eq_coe,
    map_natCast]

private theorem crystallineBase_regular :
    Function.Injective (fun x : crystallineBase.{u} p => (p : crystallineBase.{u} p) * x) := by
  intro x y h
  apply (padicLiftEquiv p).injective
  have hh := congrArg (padicLiftEquiv p) h
  simp only [map_mul, map_natCast] at hh
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero) hh

private theorem crystallineBase_complete :
    IsAdicComplete (Ideal.span {(p : crystallineBase.{u} p)}) (crystallineBase.{u} p) := by
  apply (IsAdicComplete.congr_ringEquiv (Ideal.span {(p : crystallineBase.{u} p)})
    (padicLiftEquiv p)).mp
  change IsAdicComplete
    ((Ideal.span {(p : crystallineBase.{u} p)}).map (padicLiftEquiv p).toRingHom) (PadicInt p)
  rw [padicLiftIdeal]
  infer_instance

private def crystallineQuotient :
    (crystallineBase.{u} p ⧸ Ideal.span {(p : crystallineBase.{u} p)}) ≃+* ZMod p :=
  (Ideal.quotientEquiv _ _ (padicLiftEquiv p) (padicLiftIdeal p).symm).trans
    PadicInt.residueField

private theorem existsUnique_crystallineBaseDelta :
    ∃! D : DeltaStructure p (crystallineBase.{u} p), D.frobeniusLift = RingHom.id _ :=
  DeltaStructure.existsUnique_of_mod_p (crystallineBase_regular p) (RingHom.id _) (by
    intro x
    apply (crystallineQuotient p).injective
    simp only [RingHom.id_apply, map_pow]
    exact (ZMod.pow_card _).symm)

/-- `ℤ_p` の δ 構造。Frobenius の持ち上げは恒等射。 -/
def crystallineBaseDelta : DeltaStructure p (crystallineBase.{u} p) :=
  (existsUnique_crystallineBaseDelta p).exists.choose

theorem crystallineBaseDelta_frobenius :
    (crystallineBaseDelta.{u} p).frobeniusLift = RingHom.id _ :=
  (existsUnique_crystallineBaseDelta p).exists.choose_spec

/-- 生成元 p を選んだ結晶 prism（BS 著者版 Example 3.3）。 -/
def crystallineBasePrism : OrientedPrism p (crystallineBase.{u} p) := by
  letI := crystallineBase_complete.{u} p
  exact OrientedPrism.crystalline (crystallineBaseDelta p) (crystallineBase_regular p)

theorem crystallineBase_generator : (crystallineBasePrism.{u} p).generator = p := by
  simp [crystallineBasePrism]

/-- 生成元が p の prism の剰余は p で零になるため有界。 -/
theorem crystallineBounded {A : Type u} [CommRing A] (P : OrientedPrism p A)
    (h : P.generator = p) : IsBoundedPrism P := by
  have hp : (p : A ⧸ P.ideal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P.ideal), Ideal.Quotient.eq_zero_iff_mem, ← h]
    exact Ideal.subset_span rfl
  exact ⟨1, fun n x hx => by simp [hp]⟩

abbrev crystallineBaseBounded :=
  crystallineBounded p (crystallineBasePrism.{u} p) (crystallineBase_generator p)

/-- 結晶基底の剰余体。 -/
abbrev cartierBase := crystallineBase.{u} p ⧸ (crystallineBasePrism p).ideal

/-- 結晶基底の剰余体と素数体の標準同型。 -/
def cartierBaseEquiv : cartierBase.{u} p ≃+* ZMod p :=
  crystallineQuotient p

theorem cartierBase_natCast : (p : cartierBase.{u} p) = 0 := by
  apply (cartierBaseEquiv p).injective
  rw [map_natCast, map_zero, ZMod.natCast_self]

open CategoryTheory SerrePositivity.Cosimplicial

/-- 余単体的可換環の p による項ごとの商。 -/
abbrev modPrimeCosimplicial (p : ℕ) (X : CosimplicialObject CommRingCat.{u}) :
    CosimplicialObject CommRingCat.{u} :=
  quotPow X (fun n => (p : X.obj n)) (fun θ => map_natCast (X.map θ).hom p) 1

/-- 余単体的環射を p による項ごとの商に降ろす。 -/
abbrev modPrimeMap (p : ℕ) {X Y : CosimplicialObject CommRingCat.{u}} (f : X ⟶ Y) :
    modPrimeCosimplicial p X ⟶ modPrimeCosimplicial p Y :=
  quotPowMap X (fun n => (p : X.obj n)) (fun θ => map_natCast (X.map θ).hom p)
    (fun n => (p : Y.obj n)) (fun θ => map_natCast (Y.map θ).hom p) f
    (fun n => map_natCast (f.app n).hom p) 1

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Notation 5.1" (partial := component) "BS-D69 P3（11-12）：結晶サイトの古典的な部分（big affine site の対象と射、Zariski 位相、構造環の層性、Čech の塔と pro 弱終性）は本体。pd イデアル I ∋ p の一般形と Frobenius の捻り R^(1) は本体にない（drafts の crystallineComparison_polynomial は一般の結晶 prism と I ∋ p の多項式を扱う） ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.crystallineBasePrism
