module

public import SerrePositivity.Spectra.SymmetricSequence.ConvolutionMiddleExchange

/-! # 空の生成ブロックについての添字交換の簡約 -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.FiniteBijection

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 濃度の等式による標準有限集合の全単射は対象の等式による移送。 -/
lemma homOfEquiv_finCongr {a b : ℕ} (h : a = b) :
    homOfEquiv (X := of a) (Y := of b) (finCongr h) =
      eqToHom (congrArg of h) := by
  subst b
  exact homOfEquiv_refl (of a)

/-- 標準有限集合の左単位子は零加法による移送。 -/
lemma leftUnitor_of_hom (q : ℕ) :
    (λ_ (of q)).hom = eqToHom (congrArg of (Nat.zero_add q)) := by
  exact homOfEquiv_finCongr (Nat.zero_add q)

/-- 標準有限集合の逆左単位子も零加法による移送。 -/
lemma leftUnitor_of_inv (q : ℕ) :
    (λ_ (of q)).inv = eqToHom (congrArg of (Nat.zero_add q).symm) := by
  apply (cancel_mono (λ_ (of q)).hom).mp
  rw [Iso.inv_hom_id, leftUnitor_of_hom]
  change 𝟙 (of q) = eqToHom _ ≫ eqToHom _
  simp only [eqToHom_trans, eqToHom_refl]

end SerrePositivity.FiniteBijection

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 空の生成ブロックとの交換は左単位子の移送だけになる。 -/
lemma middleExchangeIndex_tensorUnit (b d : FiniteBijection) :
    middleExchangeIndex (𝟙_ FiniteBijection) b d =
      b ◁ (λ_ d).hom ≫ (λ_ (b ⊗ d)).inv := by
  unfold middleExchangeIndex
  rw [braiding_tensorUnit_right, comp_whiskerRight]
  simp only [Category.assoc]
  rw [triangle_assoc_comp_right_assoc, leftUnitor_inv_whiskerRight_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- 生成次数零のブロック交換には置換がなく、次数の等式による移送になる。 -/
lemma middleExchangeIndex_zero (p q : ℕ) :
    middleExchangeIndex (FiniteBijection.of 0) (FiniteBijection.of p)
        (FiniteBijection.of q) =
      eqToHom (congrArg FiniteBijection.of
        ((congrArg (p + ·) (Nat.zero_add q)).trans (Nat.zero_add (p + q)).symm)) := by
  erw [middleExchangeIndex_tensorUnit, FiniteBijection.leftUnitor_of_hom]
  rw [whiskerLeft_eqToHom]
  change eqToHom (congrArg (fun k => FiniteBijection.of (p + k)) (Nat.zero_add q)) ≫
    (λ_ (FiniteBijection.of (p + q))).inv = _
  rw [FiniteBijection.leftUnitor_of_inv, eqToHom_trans]

end SerrePositivity.SymmetricSequence
