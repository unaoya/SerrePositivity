module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeExistence
public import SerrePositivity.HomologicalAlgebra.KoszulRingEquiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Prism の剰余表示と有限関係商

## 概要
剰余の同型で有限関係を持ち上げ、その商を元の有限関係商へ同定する。
## 方針
二重商とイデアルの像の標準同型を合成する。
## 規約
BS 著者版 Example 7.9・Proposition 7.10。持ち上げの選択は任意。
## 使われ方
有界性と Koszul 正則性を lci 包絡の入力へ渡す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]
variable (P : OrientedPrism p A) (e : A ⧸ P.ideal ≃+* S) {r : ℕ}
variable (w : Fin r → A) (z : Fin r → S)
variable (hw : ∀ i, e (Ideal.Quotient.mk P.ideal (w i)) = z i)

/-- 二段の有限関係商を、指定された剰余環の関係商へ送る標準同型。 -/
def prismRelationQuotientEquiv :
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
theorem prismRelationQuotientEquiv_mk (x : A) :
    prismRelationQuotientEquiv P e w z hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (e (Ideal.Quotient.mk P.ideal x)) := by
  change Ideal.Quotient.mk _ (e (Ideal.Quotient.mk P.ideal x)) = _
  rfl

include e hw in
/-- 関係列の Koszul 正則性は剰余表示へ戻せる。 -/
theorem prismRelation_isKoszulResolution (hz : IsKoszulResolution z) :
    IsKoszulResolution (fun i => Ideal.Quotient.mk P.ideal (w i)) := by
  have h := hz.map_ringEquiv e.symm
  have he : e.symm ∘ z = fun i => Ideal.Quotient.mk P.ideal (w i) := by
    funext i
    apply e.injective
    simp only [Function.comp_apply, e.apply_symm_apply, hw]
  rwa [he] at h

end SerrePositivity.BhattScholze.Semiperfectoid
