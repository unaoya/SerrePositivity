module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander

/-!
# 大きい prismatic 枠の変数像による持ち上げ

## 概要
大きい枠の各変数に剰余の構造射と両立する像を指定し、prismatic envelope からの射を作る。

## 方針
完備自由 δ 環へ延長し、剰余への合成が評価を経由することから包のイデアル条件を得る。

## 規約
枠の変数の像に δ が零であることは課さない。比較は同じ係数 prism の上で行う。

## 使われ方
BS 著者版 Remark 4.19 と Theorem 6.4 の枠の比較。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.BhattScholze.Prismatic.BigCechTerm

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {Q : Poly (A ⧸ P.ideal)} {n : ℕ} (X : BigCechTerm P Q n)

local notation "C" => (A ⧸ P.ideal)
local notation "B" => completedFreeDelta P (BigCechIndex P Q n)
local notation "base" => completedFreeDeltaBase P (BigCechIndex P Q n)
local notation "V" => completedFreeDeltaVariable P (BigCechIndex P Q n)

variable {R : Type u} [CommRing R] (T : OrientedPrism p R) (b : OrientedPrism.Hom P T)
variable (sec : polyCompletion P Q.n →+* R ⧸ T.ideal)
variable (hsec : sec.comp (algebraMap (A ⧸ P.ideal) (polyCompletion P Q.n)) = b.quotientMap)
variable (v : BigCechIndex P Q n → R)
variable (hv : ∀ s, Ideal.Quotient.mk T.ideal (v s) = sec s.1)

include hsec hv in
/-- 剰余の評価と両立する変数像は、大きい枠の包からの一意な δ 射を定める。 -/
theorem existsUnique_liftVariables :
    ∃! f : X.carrier →+* R,
      X.prism.deltaStructure.IsDeltaHom T.deltaStructure f ∧
      f.comp X.base.toRingHom = b.toRingHom ∧ ∀ s, f (X.variableImage s) = v s := by
  obtain ⟨g, hg, hgu⟩ := existsUnique_completedFreeDeltaHom P (BigCechIndex P Q n)
    T.deltaStructure b.toRingHom b.map_delta T.complete_p b.isModuleComplete_map_generator v
  have he : (Ideal.Quotient.mk T.ideal).comp (g.comp (bigCechInitial P Q n)) =
      sec.comp (bigCechEval Q n) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Ideal.Quotient.mk T.ideal (g (bigCechInitial P Q n (MvPolynomial.C a))) =
        sec (bigCechEval Q n (MvPolynomial.C a))
      have hbase : g (base a) = b.toRingHom a := RingHom.congr_fun hg.2.1 a
      rw [bigCechInitial_C, hbase, bigCechEval, MvPolynomial.eval₂Hom_C]
      change Ideal.Quotient.mk T.ideal (b.toRingHom a) =
        (sec.comp (algebraMap C (polyCompletion P Q.n))) (Ideal.Quotient.mk P.ideal a)
      rw [hsec, OrientedPrism.Hom.quotientMap_mk]
    · intro s
      change Ideal.Quotient.mk T.ideal (g (bigCechInitial P Q n (MvPolynomial.X s))) =
        sec (bigCechEval Q n (MvPolynomial.X s))
      rw [bigCechInitial_X, hg.2.2, bigCechEval, MvPolynomial.eval₂Hom_X']
      exact hv s
  have hJ : (bigCechIdeal P Q n).map g ≤ T.ideal := by
    rw [bigCechIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro x hx
    change g (bigCechInitial P Q n x) ∈ T.ideal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change ((Ideal.Quotient.mk T.ideal).comp (g.comp (bigCechInitial P Q n))) x = 0
    rw [he, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]
  obtain ⟨f, hf, hfu⟩ := X.isEnvelope.lift T g hg.1 (by rw [hg.2.1]; exact b.ideal_le) hJ
  refine ⟨f, ⟨hf.1, ?_, ?_⟩, ?_⟩
  · change f.comp (X.unit.comp base) = _
    rw [← RingHom.comp_assoc, hf.2, hg.2.1]
  · intro s
    change (f.comp X.unit) (V s) = _
    rw [hf.2, hg.2.2]
  intro f' hf'
  apply hfu
  refine ⟨hf'.1, hgu _ ⟨hf'.1.comp X.isEnvelope.isDeltaHom, ?_, hf'.2.2⟩⟩
  rw [RingHom.comp_assoc]
  exact hf'.2.1

end SerrePositivity.BhattScholze.Prismatic.BigCechTerm
