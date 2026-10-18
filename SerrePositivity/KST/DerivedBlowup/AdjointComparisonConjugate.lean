module

public import SerrePositivity.KST.DerivedBlowup.AdjointSquareComparison

/-!
概要：KST §3.1 の標準左随伴比較と Mathlib の共役対応の一致。
方針：共役対応の単位公式と左随伴一意性の指定成分を照合する。
規約：右同型の逆が標準左比較の共役像に対応する。
使われ方：標準係数拡大同型の結合・単位整合性を制限側から移す。
-/

@[expose] public noncomputable section

universe u v w z

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]

/-- 概要：指定右同型から左随伴一意性で作る左同型の共役像は右同型の逆。
方針：共役像の逆対応の単位公式で同じ随伴像を持つことを示す。
規約：KST §3.1。使われ方：Mathlib の共役対応の合成・whisker 公式との接続。 -/
theorem adjointComparison_conjugate {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (A : L₁ ⊣ R₁) (B : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv B A (Adjunction.leftAdjointUniq (A.ofNatIsoRight e) B).hom = e.inv := by
  apply (conjugateEquiv B A).symm.injective
  simp only [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext X
  symm
  have he := adjointComparison_of_rightIso A B e
    (((conjugateEquiv B A).symm e.inv).app X) (𝟙 (L₂.obj X)) (by
      rw [A.homEquiv_unit, ← unit_conjugateEquiv_symm B A e.inv X]
      rw [Category.assoc, e.inv_hom_id_app]
      exact (Category.comp_id (B.unit.app X)).trans (B.homEquiv_id X).symm)
  simpa only [Category.comp_id] using he

end SerrePositivity.KST.DerivedBlowup
