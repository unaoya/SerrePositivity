module

public import SerrePositivity.BhattScholze.Andre.Remark715.BoundedPrismTiltQuotient
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectSourceDeltaHom
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismWittPresentation
public import SerrePositivity.CommutativeAlgebra.WittLiftUniqueness
public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-!
# André A1-a：完全 prism から一般有界 prism への商射の持上げ

## 概要

完全 prism の商から有界 prism の商への環射は、唯一の prism 射へ持ち上がる。
BS Lemma 4.8（著者版 pp.38–39）の向き付き有界標的での証明。

## 方針

完全源を Witt 環として復元し、商での mod p 射を tilt へ持ち上げる。
標的とその prism 商の tilt 比較の逆と Fontaine 写像を合成する。
商図式は Witt 持上げの一意性で確認し、δ 保存性を完全源の剛性から得る。
原典の変形理論と逆 Frobenius 極限とは異なる経路。

## 規約

標的の完全性・p 正則性・非零性は要求しない。有界性を明示し、零商も含める。
一般 Cartier イデアルを持つ向きなし prism への比較は本ファイルには含まない。

## 使われ方

BS Rem 7.15（著者版 p.62）の絶対入力対象に、完全基底からの一意な基底射を供給する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

omit [Fact p.Prime] in
private theorem prime_nonunit_of_complete {C : Type*} [CommRing C] [Nontrivial C]
    [IsAdicComplete (Ideal.span {(p : C)}) C] : ¬ IsUnit (p : C) := by
  intro h
  have ht : Ideal.span {(p : C)} = ⊤ := Ideal.span_singleton_eq_top.mpr h
  have hz : (1 : C) = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {(p : C)})
    intro n
    apply SModEq.sub_mem.mpr
    simp [ht, Ideal.top_pow]
  exact one_ne_zero hz

private theorem exists_perfectPrismRingHomLift_nonunit
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    [Fact (¬ IsUnit (p : B ⧸ Q.ideal))]
    (g : A ⧸ W.ideal →+* B ⧸ Q.ideal) :
    ∃ F : A →+* B, (Ideal.Quotient.mk Q.ideal).comp F =
      g.comp (Ideal.Quotient.mk W.ideal) := by
  let qA := Ideal.Quotient.mk W.ideal
  let qB := Ideal.Quotient.mk Q.ideal
  let : Fact (¬ IsUnit (p : B)) := ⟨fun h =>
    (Fact.out : ¬ IsUnit (p : B ⧸ Q.ideal))
      (by simpa only [map_natCast] using h.map qB)⟩
  let : Fact (¬ IsUnit (p : A)) := ⟨fun h =>
    (Fact.out : ¬ IsUnit (p : B ⧸ Q.ideal))
      (by simpa only [map_natCast] using h.map (g.comp qA))⟩
  let := W.isAdicComplete_p_of_perfect hW
  let := boundedPrism_isAdicComplete_prime Q hB
  let := boundedPrism_quotient_isAdicComplete_prime Q hB
  let := hW.perfectRing_mod_p
  let k := ModP A p
  let ea := perfectPrismWittRecoveryEquiv W hW
  let eQ := boundedPrism_preTiltQuotientEquiv Q hB
  let s : k →+* ModP (B ⧸ Q.ideal) p := modPMap p (g.comp qA)
  let l : k →+* PreTilt (B ⧸ Q.ideal) p := Perfection.lift p k _ s
  let t : k →+* PreTilt B p := eQ.symm.toRingHom.comp l
  let Fw : WittVector p k →+* B := (WittVector.fontaineTheta B p).comp (WittVector.map t)
  have hFw : qB.comp Fw = (g.comp qA).comp ea.toRingHom := by
    apply wittLift_unique
    ext x
    have hm := congrArg (modPMap p qB)
      (WittVector.mk_fontaineTheta (WittVector.map t x))
    rw [WittVector.map_coeff] at hm
    have ht : modPMap p qB (PreTilt.coeff 0 (t (x.coeff 0))) = s (x.coeff 0) := by
      change PreTilt.coeff 0 (eQ (eQ.symm (l (x.coeff 0)))) = s (x.coeff 0)
      rw [eQ.apply_symm_apply]
      rfl
    have hea : Ideal.Quotient.mk (Ideal.span {(p : A)}) (ea x) = x.coeff 0 :=
      RingHom.congr_fun (perfectDeltaWittRecoveryEquiv_mod_p W.deltaStructure hW) x
    change Ideal.Quotient.mk (Ideal.span {(p : B ⧸ Q.ideal)}) (qB (Fw x)) =
      Ideal.Quotient.mk (Ideal.span {(p : B ⧸ Q.ideal)}) (g (qA (ea x)))
    calc
      _ = modPMap p qB (PreTilt.coeff 0 (t (x.coeff 0))) := hm
      _ = s (x.coeff 0) := ht
      _ = _ := by rw [← hea]; rfl
  refine ⟨Fw.comp ea.symm.toRingHom, ?_⟩
  ext a
  exact (RingHom.congr_fun hFw (ea.symm a)).trans
    (congrArg (g.comp qA) (ea.apply_symm_apply a))

/-- 概要：完全 prism の商射は一般有界 prism の台環へ唯一の環射として持ち上がる。
方針：非零商では tilt 比較と Fontaine 写像、零商では生成元完備性を使う。
規約：標的の完全性・p 正則性・非零性を仮定しない。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の環射の存在と一意性。 -/
theorem existsUnique_perfectPrismRingHomLift_to_bounded
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (g : A ⧸ W.ideal →+* B ⧸ Q.ideal) :
    ∃! F : A →+* B, (Ideal.Quotient.mk Q.ideal).comp F =
      g.comp (Ideal.Quotient.mk W.ideal) := by
  have hex : ∃ F : A →+* B, (Ideal.Quotient.mk Q.ideal).comp F =
      g.comp (Ideal.Quotient.mk W.ideal) := by
    rcases subsingleton_or_nontrivial (B ⧸ Q.ideal) with hs | hn
    · let : IsAdicComplete Q.ideal B := Q.isAdicComplete_generator
      let := hs
      have ht : Q.ideal = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
      have hz : (1 : B) = 0 := by
        apply IsHausdorff.haus' (I := Q.ideal)
        intro n
        apply SModEq.sub_mem.mpr
        simp [ht, Ideal.top_pow]
      let : Subsingleton B := subsingleton_of_zero_eq_one hz.symm
      exact ⟨{ toFun := fun _ => 0
               map_zero' := rfl
               map_one' := Subsingleton.elim _ _
               map_add' := fun _ _ => by simp
               map_mul' := fun _ _ => by simp }, by ext a; exact hs.elim _ _⟩
    · let := boundedPrism_quotient_isAdicComplete_prime Q hB
      let : Fact (¬ IsUnit (p : B ⧸ Q.ideal)) := ⟨prime_nonunit_of_complete⟩
      exact exists_perfectPrismRingHomLift_nonunit W hW Q hB g
  obtain ⟨F, hF⟩ := hex
  refine ⟨F, hF, ?_⟩
  intro G hG
  exact ringHom_ext_to_boundedPrism_of_perfect_source W.deltaStructure hW Q hB G F
    (hG.trans hF.symm)

/-- 概要：完全 prism の商射は一般有界 prism へ唯一の prism 射として持ち上がる。
方針：環射の一意持上げに自動的な δ 保存性と商図式からのイデアル保存性を付ける。
規約：向きは生成元の厳密な保存を要求せず、標的の完全性・p 正則性も不要。
使われ方：BS Lemma 4.8（著者版 pp.38–39）と Rem 7.15（p.62）の絶対入力圏。 -/
theorem existsUnique_perfectPrismHomLift_to_bounded
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (g : A ⧸ W.ideal →+* B ⧸ Q.ideal) :
    ∃! F : OrientedPrism.Hom W Q, F.quotientMap = g := by
  obtain ⟨f, hf, _⟩ := existsUnique_perfectPrismRingHomLift_to_bounded W hW Q hB g
  let F : OrientedPrism.Hom W Q := {
    toRingHom := f
    map_delta := perfectSource_ringHom_isDeltaHom_to_boundedPrism W.deltaStructure hW Q hB f
    ideal_le := by
      intro a ha
      change f a ∈ Q.ideal
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have h := RingHom.congr_fun hf a
      change Ideal.Quotient.mk Q.ideal (f a) = g (Ideal.Quotient.mk W.ideal a) at h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at h
      exact h }
  have hF : F.quotientMap = g := by
    apply Ideal.Quotient.ringHom_ext
    exact hf
  exact ⟨F, hF, fun G hG => perfectPrismHom_ext_to_bounded_target W hW Q hB G F
    (hG.trans hF.symm)⟩

end SerrePositivity.BhattScholze.Andre
