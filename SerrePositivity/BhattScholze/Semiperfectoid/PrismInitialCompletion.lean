module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import SerrePositivity.BhattScholze.Semiperfectoid.PrismInitialTransport
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComparison

/-!
# 任意関係の剰余表示と実完備化上の始性

## 概要
通常の関係商の比較と、源の実 p 完備化へ剰余単位の始性を移す補題を与える。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## PrismRelationFamilyQuotient -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]
variable (P : OrientedPrism p A) (e : A ⧸ P.ideal ≃+* S) {J : Type u}
variable (w : J → A) (z : J → S)
variable (hw : ∀ i, e (Ideal.Quotient.mk P.ideal (w i)) = z i)

/-- 二段の任意関係商を、指定された剰余環の関係商へ送る標準同型。 -/
def prismRelationFamilyQuotientEquiv :
    A ⧸ (P.ideal ⊔ Ideal.span (Set.range w)) ≃+* S ⧸ Ideal.span (Set.range z) := by
  let K := Ideal.span (Set.range w)
  have hK : K.map (Ideal.Quotient.mk P.ideal) =
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk P.ideal (w i))) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hmap : (K.map (Ideal.Quotient.mk P.ideal)).map e.toRingHom = Ideal.span (Set.range z) := by
    rw [hK, Ideal.map_span, ← Set.range_comp]
    congr 1
    congr 1
    funext i
    exact hw i
  exact (DoubleQuot.quotQuotEquivQuotSup P.ideal K).symm.trans
    (Ideal.quotientEquiv _ _ e hmap.symm)

/-- 関係商の同型は、元の環からの商射と両立する。 -/
theorem prismRelationFamilyQuotientEquiv_mk (x : A) :
    prismRelationFamilyQuotientEquiv P e w z hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (e (Ideal.Quotient.mk P.ideal x)) := by
  change Ideal.Quotient.mk _ (e (Ideal.Quotient.mk P.ideal x)) = _
  rfl

end SerrePositivity.BhattScholze.Semiperfectoid

end

/-! ## PrismInitialCompletion -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open CategoryTheory DerivedCompletion Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {T B : Type u} [CommRing T] [CommRing B]
variable (Q : OrientedPrism p B) (v : T →+* B ⧸ Q.ideal)

/-- 概要：通常の剰余単位の全有界標的への始性を、源の実 p 完備化へ移す。
方針：標的の生成元剰余は p 完備であり、射の等式を元の源上で確認できる。
規約：BS 著者版 Proposition 7.10。標的の p 正則性は不要。
使われ方：S′ の実 H⁰ 完備化上の単位と始性。 -/
theorem exists_initialPrismUnit_on_completion
    (hv : ∀ (C : Type u) [CommRing C] (Y : OrientedPrism p C) (hY : IsBoundedPrism Y)
      (s : T →+* C ⧸ Y.ideal), ∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp v = s) :
    ∃ w : CompletedRing p T →+* B ⧸ Q.ideal,
      w.comp (principalCompletionRingCatUnit p (CommRingCat.of T)).hom = v ∧
      ∀ (C : Type u) [CommRing C] (Y : OrientedPrism p C) (hY : IsBoundedPrism Y)
        (s : CompletedRing p T →+* C ⧸ Y.ideal),
        ∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp w = s := by
  have hcQ : IsModuleComplete (B ⧸ Q.ideal) (p : B ⧸ Q.ideal) (ModuleCat.of _ (B ⧸ Q.ideal)) :=
    isModuleComplete_principal_quotient_natCast B p Q.generator Q.complete_p
  obtain ⟨w₀, hw₀, _⟩ := principalCompletion_existsUnique_ringHom T (p : T) (B ⧸ Q.ideal) v
    (natCast_complete_restrict p v hcQ)
  let w : CompletedRing p T →+* B ⧸ Q.ideal := w₀
  have hw : w.comp (principalCompletionRingCatUnit p (CommRingCat.of T)).hom = v := hw₀
  refine ⟨w, hw, ?_⟩
  intro C _ Y hY s
  let u := (principalCompletionRingCatUnit p (CommRingCat.of T)).hom
  obtain ⟨g, hg, hgu⟩ := hv C Y hY (s.comp u)
  have hcY : IsModuleComplete (C ⧸ Y.ideal) (p : C ⧸ Y.ideal) (ModuleCat.of _ (C ⧸ Y.ideal)) :=
    isModuleComplete_principal_quotient_natCast C p Y.generator Y.complete_p
  refine ⟨g, ?_, ?_⟩
  · apply (principalCompletion_existsUnique_ringHom T (p : T) (C ⧸ Y.ideal) (s.comp u)
      (natCast_complete_restrict p (s.comp u) hcY)).unique
    · change (g.quotientMap.comp w).comp u = s.comp u
      rw [RingHom.comp_assoc, hw, hg]
    · rfl
  · intro k hk
    apply hgu
    rw [← hw, ← RingHom.comp_assoc, hk]

end SerrePositivity.BhattScholze.Semiperfectoid

end
