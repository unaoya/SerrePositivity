module
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomDifferential

/-!
概要：零延長からの Hom 微分を、各全次数の成分表示そのものに戻す。
方針：斉次射の評価先の等式を明示し、縦横の二項を同じ標的へ輸送する。
規約：非有界整数次数を保ち、横次数零と正の横次数を分ける。
使われ方：HA 1.2.4、G10 の重み end と Hom の微分比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits CochainComplex HomComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
variable (K : ChainComplex C ℕ) (H : CochainComplex C ℤ)

/-- 斉次射の評価先の書き方を変えたときの指定輸送。 -/
theorem extendedChainHomRows_v (q : ℤ)
    (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q)
    (n : ℕ) (t : ℤ) (ht : -(n : ℤ)+q=t) :
    (negativeChainRowIso K n).inv ≫ z.v (-n) t ht =
      extendedChainHomRows K H q z n ≫ eqToHom (by congr 1; omega) := by
  have he : t=q-n := by omega
  cases he
  simp only [extendedChainHomRows, eqToHom_refl, Category.comp_id]

/-- 正の鎖次数における Hom 微分を、同じ全次数の成分として表示する。 -/
theorem extendedChainHomRows_d_succ (q : ℤ)
    (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q) (n : ℕ) :
    extendedChainHomRows K H (q+1) (δ q (q+1) z) (n+1) =
      extendedChainHomRows K H q z (n+1) ≫
        H.d (q-(n+1 : ℕ)) (q+1-(n+1 : ℕ)) +
      (q+1).negOnePow • (K.d (n+1) n ≫ extendedChainHomRows K H q z n ≫
        eqToHom (by congr 1; push_cast; omega)) := by
  dsimp only [extendedChainHomRows]
  rw [δ_v q (q+1) rfl z _ _ _ (q-(n+1 : ℕ)) (-(n : ℤ))
    (by push_cast; omega) (by push_cast; omega)]
  rw [Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc,
    ← Category.assoc, negativeChainRowIso_inv_d, Category.assoc]
  conv_lhs =>
    simp only [Category.assoc]
    rw [extendedChainHomRows_v K H q z n]
  simp only [extendedChainHomRows, Category.assoc]

/-- 零鎖次数の成分では Hom 微分は縦項のみ。 -/
theorem extendedChainHomRows_d_zero (q : ℤ)
    (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q) :
    extendedChainHomRows K H (q+1) (δ q (q+1) z) 0 =
      extendedChainHomRows K H q z 0 ≫ H.d (q-0) (q+1-0) := by
  have hz (b c : ℤ) (hb : b=q) (hc : c=q+1) :
      (negativeChainRowIso K 0).inv ≫ (δ q (q+1) z).v 0 c (by omega) =
      (negativeChainRowIso K 0).inv ≫ z.v 0 b (by omega) ≫ H.d b c := by
    cases hb; cases hc
    exact extendedChainHom_differential_zero K H q z
  simpa only [extendedChainHomRows, Int.natCast_zero, Int.neg_zero, Category.assoc] using
    hz (q-0) (q+1-0) (by omega) (by omega)

end SerrePositivity.HomologicalAlgebra
