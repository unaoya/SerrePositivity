module

public import SerrePositivity.HomologicalAlgebra.Complexes.NatTensor.Homogeneous

/-!
# 四重テンソル交換の任意の全次数での成分

概要：Berger–Fresse §1.1.4 の交換公式を二つの独立な全次数の同定に対応させる。
方針：二つの次数和を消去し、斉次包含上の公式を適用する。
規約：交換符号を整数のスカラー作用として述べる。
使われ方：二つの AW 対角の有限和の各項を shuffle と比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NatTensor

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：テンソル鎖写像の任意の斉次包含上の値（BF §1.1.4）。
方針：二変数全複体の包含公式をテンソル積の射で書き直す。
規約：全次数 n の同定を明示する。
使われ方：交換後の二つの shuffle 鎖写像の成分。 -/
@[reassoc]
lemma inclusion_tensorMap {P Q P' Q' : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q n : ℕ) (h : p + q = n) :
    ιTensorObj P Q p q n h ≫ (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj P' Q' p q n h := by
  rw [ι_mapBifunctorMap]
  simp only [tensorHom_def, Category.assoc]
  rfl

/-- 概要：四重テンソルの包含に続く交換の整数符号公式（BF §1.1.4）。
方針：前後の全次数の等式を消去して既存の斉次公式を用いる。
規約：第二因子 j と第三因子 k の交換符号を付ける。
使われ方：AW と shuffle の成分適合性を全複体へ束ねる。 -/
@[reassoc]
lemma inclusion_interchange (P Q T U : ChainComplex (ModuleCat.{u} A) ℕ)
    (i j k l a b n : ℕ) (ha : i + j = a) (hb : k + l = b) (hn : a + b = n) :
    (ιTensorObj P Q i j a ha ⊗ₘ ιTensorObj T U k l b hb) ≫
        ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) (_root_.SerrePositivity.NatTensor.tensor T U) a b n hn ≫ (_root_.SerrePositivity.NatTensor.interchange P Q T U).hom.f n =
      (-1 : ℤ) ^ (j * k) •
        (tensorμ (P.X i) (Q.X j) (T.X k) (U.X l) ≫
          (ιTensorObj P T i k (i + k) rfl ⊗ₘ ιTensorObj Q U j l (j + l) rfl) ≫
          ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P T) (_root_.SerrePositivity.NatTensor.tensor Q U) (i + k) (j + l) n (by omega)) := by
  subst a
  subst b
  simpa only [_root_.SerrePositivity.NatTensor.tensorQuadι, Category.assoc, Units.smul_def, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one] using _root_.SerrePositivity.NatTensor.ιTensorQuad_interchange_hom P Q T U i j k l n (by omega)

end SerrePositivity.NatTensor
