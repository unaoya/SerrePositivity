module

public import SerrePositivity.KST.SchemeLemmas.PureTransformScalarRestriction
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# 有限代数の純変換を実際の商代数として構成する

## 概要
境界ねじれを除く加群の純変換に、局所化写像の核による商代数の構造を与える。

## 方針
拡大環自身上の境界ねじれをイデアルとして取り、スカラー制限の既存の線形同型を使う。

## 規約
局所化全体との同型は主張しない。純変換は元の代数の局所化内の像に相当する。

## 使われ方
論文 補題 3.3、公理 (6) の加群平坦化から strict transform のアフィン環への接続。
-/

@[expose] public section

universe u v

open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B] (f : R)

/-- 概要：有限代数の境界ねじれを定める実際のイデアル（論文 補題 3.3）。
方針：拡大環 B 自身上で境界元の像による局所化写像の核を取る。
規約：有限性や Noether 性は定義には不要。
使われ方：スキームの閉部分を与える商環。 -/
noncomputable def boundaryTorsionIdeal : Ideal B := boundaryTorsion (algebraMap R B f) B

/-- 概要：有限代数の境界ねじれを除く実際の商代数（論文 補題 3.3）。
方針：拡大環自身上の境界ねじれイデアルで商を取る。
規約：局所化全体でなく、境界に台を持つねじれだけを除く。
使われ方：加群の平坦性を実際の Spec の平坦性へ移す。 -/
abbrev algebraPureTransform := B ⧸ boundaryTorsionIdeal R B f

/-- 概要：商代数の加群は元の加群の純変換と線形同型（論文 補題 3.3）。
方針：拡大環の商と基礎環の商のスカラー制限の同型を使う。
規約：同型は元の代数の代表元を保つ。
使われ方：実際のチャート純変換の平坦性を商代数へ移す。 -/
noncomputable def algebraPureTransformModuleEquiv :
    modulePureTransform f B ≃ₗ[R] algebraPureTransform R B f :=
  modulePureTransformScalarRestrictionEquiv (B := B) (M := B) f

/-- 概要：商代数との線形同型は元の代表元を保つ（論文 補題 3.3）。
方針：商のスカラー制限の同型の代表元公式を使う。
規約：基礎環 R に関する線形同型。
使われ方：環の商写像と加群の商写像の一致。 -/
theorem algebraPureTransformModuleEquiv_mk (b : B) :
    algebraPureTransformModuleEquiv R B f (Submodule.Quotient.mk b) =
      Ideal.Quotient.mk (boundaryTorsionIdeal R B f) b := rfl

/-- 概要：境界ねじれイデアルは一元局所化の環準同型の核（論文 補題 3.3）。
方針：加群と環の局所化の両方で冪消滅条件に帰着する。
規約：この同定は有限性や正則性を仮定しない。
使われ方：strict transform のスキーム論的像のイデアルとの比較。 -/
theorem boundaryTorsionIdeal_eq_ker :
    boundaryTorsionIdeal R B f =
      RingHom.ker (algebraMap B (Localization.Away (algebraMap R B f))) := by
  ext b
  rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R B f))]
  change b ∈ boundaryTorsion (algebraMap R B f) B ↔ _
  rw [mem_boundaryTorsion_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨(algebraMap R B f) ^ n, ⟨n, rfl⟩⟩, hn⟩
  · rintro ⟨⟨s, ⟨n, rfl⟩⟩, hn⟩
    exact ⟨n, hn⟩

/-- 概要：商代数から一元局所化への実際の環準同型（論文 補題 3.3）。
方針：局所化写像をその核による商へ降ろす。
規約：この射の全射性は主張しない。
使われ方：元の代数の局所化内の像としての純変換。 -/
noncomputable def algebraPureTransformToLocalization :
    algebraPureTransform R B f →+* Localization.Away (algebraMap R B f) :=
  Ideal.Quotient.lift (boundaryTorsionIdeal R B f)
    (algebraMap B (Localization.Away (algebraMap R B f)))
    (fun b hb ↦ (boundaryTorsionIdeal_eq_ker R B f ▸ hb :
      b ∈ RingHom.ker (algebraMap B (Localization.Away (algebraMap R B f)))))

/-- 概要：商代数から一元局所化への写像は単射（論文 補題 3.3）。
方針：商イデアルが実際の局所化写像の核であることを使う。
規約：局所化の像と同一視し、局所化全体とは同一視しない。
使われ方：境界ねじれを除いたアフィン環の検証。 -/
theorem algebraPureTransformToLocalization_injective :
    Function.Injective (algebraPureTransformToLocalization R B f) := by
  apply (Ideal.injective_lift_iff _).mpr
  exact (boundaryTorsionIdeal_eq_ker R B f).symm

/-- 概要：加群純変換の平坦性は実際の商代数の平坦性へ移る（論文 補題 3.3）。
方針：代表元を保つ実際の線形同型で平坦性を移す。
規約：ここでは基礎環 R 上の平坦性を主張する。
使われ方：全 blowup チャートの平坦化を Spec の射に接続する。 -/
theorem algebraPureTransform_flat [Module.Flat R (modulePureTransform f B)] :
    Module.Flat R (algebraPureTransform R B f) :=
  Module.Flat.of_linearEquiv (algebraPureTransformModuleEquiv R B f).symm

/-- 概要：基礎環上有限な代数の純変換商も有限（論文 補題 3.3）。
方針：有限加群の純変換の有限性と線形同型を使う。
規約：代数の有限型性だけでなく加群としての有限性を要求する。
使われ方：実際のアフィン純変換の有限射としての性質。 -/
theorem algebraPureTransform_finite [Module.Finite R B] :
    Module.Finite R (algebraPureTransform R B f) :=
  Module.Finite.of_surjective (algebraPureTransformModuleEquiv R B f).toLinearMap
    (algebraPureTransformModuleEquiv R B f).surjective

end SerrePositivity.KST.Descent
