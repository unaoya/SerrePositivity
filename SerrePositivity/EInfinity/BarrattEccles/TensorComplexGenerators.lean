module

public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionExt
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizChains

/-!
# 二因子の複体の射を正規化生成元で判定する

概要：Berger–Fresse §1.1.2 の正規化生成元を複体のテンソルからの射の判定に使う。
方針：負の純粋テンソルの判定と正規化鎖の双線形写像の外延性を組み合わせる。
規約：入力鎖次数は任意の自然数 p,q でよい。
使われ方：augmentation の部分合成の保存を生成元で検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：二つの複体のテンソルからの射は負の正規化生成元で決まる（Berger–Fresse §1.1.2）。
方針：双線形写像へ curry し、二つの正規化生成元による外延性を使う。
規約：終域は任意の整数コチェイン複体でよい。
使われ方：shuffle 合成を保つ射の検証を各単体へ帰着する。 -/
lemma tensor_complex_generator_hom_ext (m n : ℕ) {T : Complex A}
    (f g : complex A m ⊗ complex A n ⟶ T)
    (h : ∀ (p q : ℕ) (x : (simplicial m) _⦋p⦌) (y : (simplicial n) _⦋q⦌),
      f.f (-((p + q : ℕ) : ℤ))
          (ιTensorObj (complex A m) (complex A n) (-(p : ℤ)) (-(q : ℤ))
            (-((p + q : ℕ) : ℤ)) (by omega)
            ((complexXIso A m p).inv (normalizedGenerator A m p x) ⊗ₜ[A]
              (complexXIso A n q).inv (normalizedGenerator A n q y))) =
        g.f (-((p + q : ℕ) : ℤ))
          (ιTensorObj (complex A m) (complex A n) (-(p : ℤ)) (-(q : ℤ))
            (-((p + q : ℕ) : ℤ)) (by omega)
            ((complexXIso A m p).inv (normalizedGenerator A m p x) ⊗ₜ[A]
              (complexXIso A n q).inv (normalizedGenerator A n q y)))) : f = g := by
  apply tensor_complex_hom_ext A m n
  intro p q x y
  let I := ιTensorObj (complex A m) (complex A n) (-(p : ℤ)) (-(q : ℤ))
    (-((p + q : ℕ) : ℤ)) (by omega)
  let L := (TensorProduct.curry ((f.f (-((p + q : ℕ) : ℤ))).hom.comp I.hom)).compl₁₂
    (complexXIso A m p).inv.hom (complexXIso A n q).inv.hom
  let R := (TensorProduct.curry ((g.f (-((p + q : ℕ) : ℤ))).hom.comp I.hom)).compl₁₂
    (complexXIso A m p).inv.hom (complexXIso A n q).inv.hom
  have hLR : L = R := by
    apply normalizedGenerator_bilinear_ext A m n p q
    exact h p q
  have hxy := congrArg (fun F => F ((complexXIso A m p).hom x) ((complexXIso A n q).hom y)) hLR
  change f.f (-((p + q : ℕ) : ℤ))
      (I ((complexXIso A m p).inv ((complexXIso A m p).hom x) ⊗ₜ[A]
        (complexXIso A n q).inv ((complexXIso A n q).hom y))) =
    g.f (-((p + q : ℕ) : ℤ))
      (I ((complexXIso A m p).inv ((complexXIso A m p).hom x) ⊗ₜ[A]
        (complexXIso A n q).inv ((complexXIso A n q).hom y))) at hxy
  simpa only [Iso.hom_inv_id_apply] using hxy

end SerrePositivity.EInfinity.BarrattEccles
