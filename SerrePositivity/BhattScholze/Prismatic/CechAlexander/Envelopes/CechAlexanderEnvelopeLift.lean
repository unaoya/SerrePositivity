module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.CechAlexanderEnvelopeData
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity

/-!
# 一般の Čech–Alexander 包絡からの変数の持ち上げ

## 概要
一般の剰余環の HasEnvelopes による包から、剰余と両立する変数像を持つ射を得る。

## 方針
完備自由 δ 環の普遍性と生の評価核の包絡の普遍性を順に使う。

## 規約
BS 著者版 Construction 4.17。原典の導来閉包からの比較は EnvelopeData で行う。

## 使われ方
HasEnvelopes から site の Čech–Alexander 対象を組み立てる。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic.CechEnvelopeTerm
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R]
variable {n : ℕ} (X : CechEnvelopeTerm P R n)
variable {S : Type u} [CommRing S] (T : OrientedPrism p S) (b : OrientedPrism.Hom P T)
variable (sec : R →+* S ⧸ T.ideal)
variable (hsec : sec.comp (algebraMap (A ⧸ P.ideal) R) = b.quotientMap)
variable (v : cechIndex R n → S)
variable (hv : ∀ s, Ideal.Quotient.mk T.ideal (v s) = sec s.1)

include hsec hv in
/-- 剰余の評価と両立する変数像は、一般の包絡からの一意な δ 射を定める。 -/
theorem existsUnique_liftVariables :
    ∃! f : X.carrier →+* S,
      X.prism.deltaStructure.IsDeltaHom T.deltaStructure f ∧
      f.comp X.base.toRingHom = b.toRingHom ∧ ∀ s, f (X.variableImage s) = v s := by
  obtain ⟨g, hg, hgu⟩ := existsUnique_completedFreeDeltaHom P (cechIndex R n)
    T.deltaStructure b.toRingHom b.map_delta T.complete_p b.isModuleComplete_map_generator v
  have he : (Ideal.Quotient.mk T.ideal).comp (g.comp (cechInitial P R n)) =
      sec.comp (cechEval P R n) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Ideal.Quotient.mk T.ideal (g (cechInitial P R n (MvPolynomial.C a))) =
        sec (cechEval P R n (MvPolynomial.C a))
      have hbase : g (completedFreeDeltaBase P (cechIndex R n) a) = b.toRingHom a := RingHom.congr_fun hg.2.1 a
      rw [cechInitial_C, hbase, cechEval, MvPolynomial.eval₂Hom_C]
      change Ideal.Quotient.mk T.ideal (b.toRingHom a) =
        (sec.comp (algebraMap (A ⧸ P.ideal) R)) (Ideal.Quotient.mk P.ideal a)
      rw [hsec, OrientedPrism.Hom.quotientMap_mk]
    · intro s
      change Ideal.Quotient.mk T.ideal (g (cechInitial P R n (MvPolynomial.X s))) =
        sec (cechEval P R n (MvPolynomial.X s))
      rw [cechInitial_X, hg.2.2, cechEval, MvPolynomial.eval₂Hom_X']
      exact hv s
  have hJ : (cechRawKernel P R n).map g ≤ T.ideal := by
    rw [cechRawKernel, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro x hx
    change g (cechInitial P R n x) ∈ T.ideal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change ((Ideal.Quotient.mk T.ideal).comp (g.comp (cechInitial P R n))) x = 0
    rw [he, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]
  obtain ⟨f, hf, hfu⟩ := X.isEnvelope.lift T g hg.1 (by rw [hg.2.1]; exact b.ideal_le) hJ
  refine ⟨f, ⟨hf.1, ?_, ?_⟩, ?_⟩
  · change f.comp (X.unit.comp (completedFreeDeltaBase P (cechIndex R n))) = _
    rw [← RingHom.comp_assoc, hf.2, hg.2.1]
  · intro s
    change (f.comp X.unit) (completedFreeDeltaVariable P (cechIndex R n) s) = _
    rw [hf.2, hg.2.2]
  intro f' hf'
  apply hfu
  refine ⟨hf'.1, hgu _ ⟨hf'.1.comp X.isEnvelope.isDeltaHom, ?_, hf'.2.2⟩⟩
  rw [RingHom.comp_assoc]
  exact hf'.2.1

end SerrePositivity.BhattScholze.Prismatic.CechEnvelopeTerm
