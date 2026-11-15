module
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomRows

/-!
概要：負次数へ零延長した鎖重みからの Hom 微分を、元の鎖次数の成分で計算する。
方針：指定延長同型と微分の可換性を使い、Hom 微分を縦横の二項へ展開する。
規約：零鎖次数の横項は実際の零延長によって消える。内部次数は非有界。
使われ方：HA 1.2.4、G10 の積 end と Hom 複体の符号付き比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits CochainComplex HomComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
variable (K : ChainComplex C ℕ) (H : CochainComplex C ℤ)

/-- 元の鎖微分を保つ、負次数への指定延長同型の可換性。 -/
theorem negativeChainRowIso_inv_d (n : ℕ) :
    (negativeChainRowIso K (n+1)).inv ≫
        (K.extend ComplexShape.embeddingDownNat).d (-(n+1 : ℕ)) (-(n : ℤ)) =
      K.d (n+1) n ≫ (negativeChainRowIso K n).inv := by
  erw [K.extend_d_eq ComplexShape.embeddingDownNat (i := n+1) (j := n) rfl rfl]
  simp [negativeChainRowIso]

/-- 正の鎖次数における Hom 微分の縦項と横項。 -/
theorem extendedChainHom_differential_succ (q : ℤ)
    (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q) (n : ℕ) :
    (negativeChainRowIso K (n+1)).inv ≫
        (δ q (q+1) z).v (-(n+1 : ℕ)) (q-n) (by push_cast; omega) =
      extendedChainHomRows K H q z (n+1) ≫ H.d (q-(n+1 : ℕ)) (q-n) +
        (q+1).negOnePow • (K.d (n+1) n ≫ extendedChainHomRows K H q z n) := by
  rw [δ_v q (q+1) rfl z _ _ _ (q-(n+1 : ℕ)) (-(n : ℤ)) (by push_cast; omega)
    (by push_cast; omega)]
  rw [Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc,
    ← Category.assoc, negativeChainRowIso_inv_d, Category.assoc]
  simp only [extendedChainHomRows, Category.assoc]

/-- 零鎖次数における Hom 微分は標的の縦微分のみ。 -/
theorem extendedChainHom_differential_zero (q : ℤ)
    (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q) :
    (negativeChainRowIso K 0).inv ≫ (δ q (q+1) z).v 0 (q+1) (by omega) =
      (negativeChainRowIso K 0).inv ≫ z.v 0 q (by omega) ≫ H.d q (q+1) := by
  rw [δ_v q (q+1) rfl z 0 (q+1) (by omega) q 1 (by omega) rfl]
  have hd : (K.extend ComplexShape.embeddingDownNat).d 0 1 = 0 :=
    (K.isZero_extend_X ComplexShape.embeddingDownNat 1
      (fun n hn => by change -(n : ℤ) = 1 at hn; omega)).eq_of_tgt _ _
  rw [hd, zero_comp, smul_zero, add_zero]

end SerrePositivity.HomologicalAlgebra
