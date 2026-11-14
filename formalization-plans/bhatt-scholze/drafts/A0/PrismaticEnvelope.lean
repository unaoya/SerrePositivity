-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Envelope（仮。原典 Prop 3.13・Ex 3.14・Def 2.42）
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.5、単位 A0-3a・A0-3c（定義と、変数の場合の存在の主張）。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Delta.CompleteRegularity.RelativeCompleteRegularity

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaFlat
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.Envelope
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
-- 本ファイルは drafts/A0/PrismaticSite.lean の `IsBoundedPrism` を使う。

/-!
# prismatic envelope（BS 著者版 Prop 3.13 の普遍性による定義と、Ex 3.14 の場合の存在）

## 概要
有界 prism (A,(d)) 上の δ-A 代数 B とイデアル J ⊇ dB（δ 対 (B, J)）について、prism (C, dC) への普遍射 (B, J) → (C, dC)
を `IsPrismaticEnvelope` として定義する（原典の「B{J/I}^∧」はこの普遍対象）。存在と性質 (1)〜(3) は Prop 3.13 の定理で、
E3 に要る Ex 3.14 の場合（多項式代数からの全射の核。変数変換後は「変数の部分集合 ＋ (d)」）だけを主張する。
相対的な (p,d) 完全正則列（Def 2.42）も定義する。

## 方針
定義は普遍性のみ（計算用の模型は証明の中だけ）。存在の証明の筋：J = (d, Z)（Z は自由 δ 環の変数の部分集合）のとき、
Z = d·Y とおいた完備化した自由 δ 環 A{(S∖Z), Y}^∧ が普遍性を満たす（d の正則性で商が一意、`existsUnique_deltaAdjoinDivisionHom_of_regular`
と `existsUnique_deltaPDCompletionHom`）。平坦性・離散性は Lemma 3.7(2)（多項式環は自由加群）。

## 規約
普遍性の標的 (D, dD) は prism（有界性は要求しない。原典どおり）。基底は向き付き（ノート D5）。一般の Prop 3.13（Zariski 局所的な
正則列）は述べない（設計書 D21）。Def 2.42 は Koszul 複体のホモロジーで述べる（D20）。

## 使われ方
Constr 4.17（Čech–Alexander の対象）、Ex 7.9・Prop 7.10（A3。別の場合の存在が要る）、Thm 5.2（A1、pd 包との比較は普遍性で）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped TensorProduct

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-! ## 相対的な完全正則列（Def 2.42） -/

/-- A′⊗_A T を A′ の (p,d′) で完備化した H⁰。 -/
def envelopeBaseChangeRing {A' T : Type u} [CommRing A'] [CommRing T] [Algebra A A'] [Algebra A T]
    (P' : OrientedPrism p A') : CommRingCat.{u} := by
  let U := A' ⊗[A] T
  let d := (Algebra.TensorProduct.includeLeftRingHom : A' →+* U) P'.generator
  letI := pdCompletionCommRing U p d
  exact CommRingCat.of (PDCompletionH0 U p d)

def envelopeBaseChangeUnit {A' T : Type u} [CommRing A'] [CommRing T] [Algebra A A'] [Algebra A T]
    (P' : OrientedPrism p A') :
    (A' ⊗[A] T) →+* envelopeBaseChangeRing (A := A) (T := T) P' :=
  pdCompletionUnit _ p ((Algebra.TensorProduct.includeLeftRingHom : A' →+* A' ⊗[A] T) P'.generator)

/-- 完備底変換後の二つの脚 A′→T′ と T→T′。 -/
def envelopeBaseLeg {A' T : Type u} [CommRing A'] [CommRing T] [Algebra A A'] [Algebra A T]
    (P' : OrientedPrism p A') : A' →+* envelopeBaseChangeRing (A := A) (T := T) P' :=
  (envelopeBaseChangeUnit P').comp Algebra.TensorProduct.includeLeftRingHom

def envelopeChangeLeg {A' T : Type u} [CommRing A'] [CommRing T] [Algebra A A'] [Algebra A T]
    (P' : OrientedPrism p A') : T →+* envelopeBaseChangeRing (A := A) (T := T) P' :=
  (envelopeBaseChangeUnit P').comp (Algebra.TensorProduct.includeRight : T →ₐ[A] A' ⊗[A] T).toRingHom

/-- 概要：Prop 3.13(2)：envelope の形成は有界 prism の底変換と可換（変数の場合）。
方針：模型が自由 δ 環なので、底変換後も同じ形。普遍性で比較。
規約：底変換は prism の射 (A,(d)) → (A′,(d′)) に沿う完備テンソル。
使われ方：Rem 4.19 の底変換、Lemma 4.20、Thm 5.2 の φ_A^* C^•。
-/
theorem prismaticEnvelope_baseChange_of_variables {A' : Type u} [CommRing A']
    (P' : OrientedPrism p A') (f : OrientedPrism.Hom P P') (hP : IsBoundedPrism P) (hP' : IsBoundedPrism P')
    (S : Type u) (Z : Set S) {C : Type u} [CommRing C] (Q : OrientedPrism p C)
    (η : completedFreeDelta P S →+* C) (hJ : completedFreeDeltaBase P S P.generator ∈ variableIdeal P S Z)
    (h : IsPrismaticEnvelope P (completedFreeDeltaStructure P S) (completedFreeDeltaBase P S)
      (completedFreeDeltaBase_isDeltaHom P S) (variableIdeal P S Z) hJ Q η) :
    let B := completedFreeDelta P S
    letI := f.toRingHom.toAlgebra
    letI : Algebra A B := (completedFreeDeltaBase P S).toAlgebra
    letI : Algebra A C := (η.comp (completedFreeDeltaBase P S)).toAlgebra
    let B' := envelopeBaseChangeRing (A := A) (T := B) P'
    let C' := envelopeBaseChangeRing (A := A) (T := C) P'
    let b := envelopeBaseLeg (A := A) (T := B) P'
    let c := envelopeBaseLeg (A := A) (T := C) P'
    let u := envelopeChangeLeg (A := A) (T := B) P'
    let v := envelopeChangeLeg (A := A) (T := C) P'
    let J' := (variableIdeal P S Z).map u
    ∃ (D' : DeltaStructure p B') (Q' : OrientedPrism p C') (η' : B' →+* C')
      (hb : P'.deltaStructure.IsDeltaHom D' b) (hd : b P'.generator ∈ J'),
      (completedFreeDeltaStructure P S).IsDeltaHom D' u ∧ Q.deltaStructure.IsDeltaHom Q'.deltaStructure v ∧
      η'.comp u = v.comp η ∧ η'.comp b = c ∧ IsBoundedPrism Q' ∧
      IsPrismaticEnvelope P' D' b hb J' hd Q' η' := by
  sorry -- 自由変数模型と dY による模型を A′ 上に移す。二脚と完備化単位で誘導射を指定し、剛性で dA′ = (d′)

end SerrePositivity.BhattScholze.Prismatic
