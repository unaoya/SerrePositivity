module

public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.TensorDegrees

/-!
# 負次数のテンソル比較と微分

概要：Berger–Fresse §1.1 の次数変更がテンソル微分を保つことを証明する。
方針：二つの因子の微分を分け、次数零の境界と正次数を個別に検査する。
規約：(−1)^p と整数次数 −p の Koszul 符号を同定する。
使われ方：テンソルの次数比較を複体の同型へ束ねる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NegativeTensor

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：次数比較は第一因子の微分と可換（Berger–Fresse §1.1 のテンソル規約）。
方針：直和成分で検査し、第一次数零の場合の微分を零とする。
規約：全鎖次数 n+1 から n への微分を比較する。
使われ方：次数比較の全テンソル微分との可換性。 -/
lemma degreeMap_D₁ (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    mapBifunctor.D₁ K L (curriedTensor (ModuleCat A)) (.down ℕ) (n + 1) n ≫ _root_.SerrePositivity.NegativeTensor.degreeMap K L n =
      _root_.SerrePositivity.NegativeTensor.degreeMap K L (n + 1) ≫
        mapBifunctor.D₁ (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (curriedTensor (ModuleCat A)) (.up ℤ)
          (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n + 1 at hpq
  rw [mapBifunctor.ι_D₁_assoc, _root_.SerrePositivity.NegativeTensor.ι_degreeMap_assoc, mapBifunctor.ι_D₁]
  cases p with
  | zero =>
    have hd : (_root_.SerrePositivity.NegativeTensor.extend K).d 0 1 = 0 := (_root_.SerrePositivity.NegativeTensor.isZero_positive K 1 (by omega)).eq_of_tgt _ _
    erw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp),
      mapBifunctor.d₁_eq (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (curriedTensor (ModuleCat A)) (.up ℤ)
        (show (ComplexShape.up ℤ).Rel 0 1 from rfl) (-(q : ℤ)) (-(n : ℤ)) (by dsimp; omega)]
    simp [hd]
  | succ p =>
    rw [mapBifunctor.d₁_eq K L (curriedTensor (ModuleCat A)) (.down ℕ)
      (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl) q n (by dsimp; omega)]
    rw [mapBifunctor.d₁_eq (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (curriedTensor (ModuleCat A)) (.up ℤ)
      (show (ComplexShape.up ℤ).Rel (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) from by
        change -((_ + 1 : ℕ) : ℤ) + 1 = -(_ : ℤ)
        omega)
      (-(q : ℤ)) (-(n : ℤ)) (by dsimp; omega)]
    rw [show ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p + 1, q) = 1 from rfl,
      show ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ)
        (-((p + 1 : ℕ) : ℤ), -(q : ℤ)) = 1 from rfl]
    simp only [one_smul, Category.assoc, _root_.SerrePositivity.NegativeTensor.ι_degreeMap]
    change (K.d (p + 1) p ▷ L.X q) ≫ _ =
      ((_root_.SerrePositivity.NegativeTensor.xIso K (p + 1)).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L q).inv) ≫
        ((_root_.SerrePositivity.NegativeTensor.extend K).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ▷ (_root_.SerrePositivity.NegativeTensor.extend L).X (-(q : ℤ))) ≫ _
    simp only [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp,
      _root_.SerrePositivity.NegativeTensor.xIso_inv_d]

/-- 概要：次数比較は第二因子の微分と可換（Berger–Fresse §1.1 のテンソル規約）。
方針：直和成分で第二次数零を除き、二つの Koszul 符号を同定する。
規約：p 次の鎖と −p 次のコチェインの符号は一致する。
使われ方：次数比較の全テンソル微分との可換性。 -/
lemma degreeMap_D₂ (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    mapBifunctor.D₂ K L (curriedTensor (ModuleCat A)) (.down ℕ) (n + 1) n ≫ _root_.SerrePositivity.NegativeTensor.degreeMap K L n =
      _root_.SerrePositivity.NegativeTensor.degreeMap K L (n + 1) ≫
        mapBifunctor.D₂ (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (curriedTensor (ModuleCat A)) (.up ℤ)
          (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n + 1 at hpq
  rw [mapBifunctor.ι_D₂_assoc, _root_.SerrePositivity.NegativeTensor.ι_degreeMap_assoc, mapBifunctor.ι_D₂]
  cases q with
  | zero =>
    have hd : (_root_.SerrePositivity.NegativeTensor.extend L).d 0 1 = 0 := (_root_.SerrePositivity.NegativeTensor.isZero_positive L 1 (by omega)).eq_of_tgt _ _
    erw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp),
      mapBifunctor.d₂_eq (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (curriedTensor (ModuleCat A)) (.up ℤ)
        (-(p : ℤ)) (show (ComplexShape.up ℤ).Rel 0 1 from rfl) (-(n : ℤ)) (by dsimp; omega)]
    simp [hd]
  | succ q =>
    rw [mapBifunctor.d₂_eq K L (curriedTensor (ModuleCat A)) (.down ℕ) p
      (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl) n (by dsimp; omega)]
    rw [mapBifunctor.d₂_eq (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (curriedTensor (ModuleCat A)) (.up ℤ)
      (-(p : ℤ))
      (show (ComplexShape.up ℤ).Rel (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) from by
        change -((_ + 1 : ℕ) : ℤ) + 1 = -(_ : ℤ)
        omega)
      (-(n : ℤ)) (by dsimp; omega)]
    rw [show ComplexShape.ε₂ (.down ℕ) (.down ℕ) (.down ℕ) (p, q + 1) =
        (-1 : ℤˣ) ^ p from rfl,
      show ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ)
        (-(p : ℤ), -((q + 1 : ℕ) : ℤ)) = (-(p : ℤ)).negOnePow from rfl]
    simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      Int.negOnePow_neg, Int.coe_negOnePow_natCast, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.assoc, _root_.SerrePositivity.NegativeTensor.ι_degreeMap]
    change (-1 : ℤ) ^ p • ((K.X p ◁ L.d (q + 1) q) ≫ _) =
      (-1 : ℤ) ^ p • (((_root_.SerrePositivity.NegativeTensor.xIso K p).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L (q + 1)).inv) ≫
        ((_root_.SerrePositivity.NegativeTensor.extend K).X (-(p : ℤ)) ◁ (_root_.SerrePositivity.NegativeTensor.extend L).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ))) ≫ _)
    simp only [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp,
      _root_.SerrePositivity.NegativeTensor.xIso_inv_d]

/-- 概要：次数比較は全テンソル微分と可換（Berger–Fresse §1.1 のテンソル規約）。
方針：第一・第二因子の微分の比較を加える。
規約：自然数次数 n+1 → n を負の整数次数へ移す。
使われ方：AW を整数コチェイン模型へ移すための複体同型の条件。 -/
lemma degreeMap_d (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).d (n + 1) n ≫ _root_.SerrePositivity.NegativeTensor.degreeMap K L n =
      _root_.SerrePositivity.NegativeTensor.degreeMap K L (n + 1) ≫
        (HomologicalComplex.tensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L)).d
          (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) := by
  rw [mapBifunctor.d_eq, mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add,
    _root_.SerrePositivity.NegativeTensor.degreeMap_D₁, _root_.SerrePositivity.NegativeTensor.degreeMap_D₂]

end SerrePositivity.NegativeTensor
