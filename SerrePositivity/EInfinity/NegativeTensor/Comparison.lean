module

public import SerrePositivity.EInfinity.NegativeTensor.Differential

/-!
# 零延長とテンソルの複体同型

概要：Berger–Fresse §1.1 の次数変更をテンソル複体の同型として実現する。
方針：負次数の標準同型と正次数の零対象の同型を束ねる。
規約：既存の整数コチェインテンソルと Koszul 符号を保つ。
使われ方：AW 対角を Barratt–Eccles の整数コチェイン模型へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.NegativeTensor

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：延長とテンソルの全整数次数での比較同型（Berger–Fresse §1.1）。
方針：非正次数では直和比較、正次数では零対象の同型を使う。
規約：自然数全次数は負の整数全次数へ移す。
使われ方：テンソル比較の複体同型を次数ごとに構成する。 -/
def comparisonX (K L : ChainComplex (ModuleCat.{u} A) ℕ) (i : ℤ) :
    (extend (HomologicalComplex.tensorObj K L)).X i ≅
      (HomologicalComplex.tensorObj (extend K) (extend L)).X i :=
  if hi : i ≤ 0 then
    ((HomologicalComplex.tensorObj K L).extendXIso ComplexShape.embeddingDownNat
      (show -(((-i).toNat : ℕ) : ℤ) = i by omega)).trans
      ((degreeIso K L (-i).toNat).trans (eqToIso (congrArg
        (HomologicalComplex.tensorObj (extend K) (extend L)).X (by omega :
          -(((-i).toNat : ℕ) : ℤ) = i))))
  else (isZero_positive (HomologicalComplex.tensorObj K L) i (by omega)).iso
    (tensor_isZero_positive K L i (by omega))

/-- 概要：全次数の比較は負次数では元の直和比較に一致（Berger–Fresse §1.1）。
方針：非正性の分岐と自然数への変換を簡約する。
規約：鎖次数零も含む。
使われ方：複体比較の微分条件と成分公式。 -/
lemma comparisonX_neg (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    comparisonX K L (-(n : ℤ)) =
      (xIso (HomologicalComplex.tensorObj K L) n).trans (degreeIso K L n) := by
  rw [comparisonX, dite_eq_left (show -(n : ℤ) ≤ 0 by omega)]
  cases n <;> simp only [eqToIso_refl, Iso.trans_refl] <;> rfl

/-- 概要：全次数の比較はコチェイン微分と可換（Berger–Fresse §1.1）。
方針：正次数の零対象を除き、負次数のテンソル微分の比較を使う。
規約：全整数次数の隣接する微分に対して述べる。
使われ方：次数ごとの比較を複体同型へ束ねる。 -/
lemma comparisonX_comm (K L : ChainComplex (ModuleCat.{u} A) ℕ) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (comparisonX K L i).hom ≫
        (HomologicalComplex.tensorObj (extend K) (extend L)).d i j =
      (extend (HomologicalComplex.tensorObj K L)).d i j ≫ (comparisonX K L j).hom := by
  by_cases hj : 0 < j
  · exact (tensor_isZero_positive K L j hj).eq_of_tgt _ _
  by_cases hi : 0 < i
  · exact (isZero_positive (HomologicalComplex.tensorObj K L) i hi).eq_of_src _ _
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
  have hp : p = q + 1 := by change -(p : ℤ) + 1 = -(q : ℤ) at hij; omega
  subst p
  rw [comparisonX_neg, comparisonX_neg, d_eq]
  simp only [Iso.trans_hom, degreeIso, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← degreeMap_d]

/-- 概要：零延長は自然数鎖複体のテンソルと可換（Berger–Fresse §1.1）。
方針：全次数の比較同型を微分との可換性で束ねる。
規約：標数・有界性・平坦性の追加仮定を置かない。
使われ方：AW 鎖写像を整数コチェインテンソルへの射に移す。 -/
def comparison (K L : ChainComplex (ModuleCat.{u} A) ℕ) :
    extend (HomologicalComplex.tensorObj K L) ≅
      HomologicalComplex.tensorObj (extend K) (extend L) :=
  HomologicalComplex.Hom.isoOfComponents (comparisonX K L) (comparisonX_comm K L)

/-- 概要：複体比較の順方向の負次数成分（Berger–Fresse §1.1）。
方針：次数ごとの比較とその負次数での公式を使う。
規約：入力の標準同型の後に直和比較を施す。
使われ方：整数 AW 対角の切断成分を計算する。 -/
@[simp] lemma comparison_hom_f_neg (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (comparison K L).hom.f (-(n : ℤ)) =
      (xIso (HomologicalComplex.tensorObj K L) n).hom ≫ degreeMap K L n := by
  change (comparisonX K L (-(n : ℤ))).hom = _
  rw [comparisonX_neg]
  rfl

/-- 概要：複体比較の逆方向の負次数成分（Berger–Fresse §1.1）。
方針：次数ごとの比較とその負次数での公式を使う。
規約：直和比較の逆の後に入力の標準同型の逆を施す。
使われ方：整数模型の射の等式を自然数鎖模型へ戻す。 -/
@[simp] lemma comparison_inv_f_neg (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (comparison K L).inv.f (-(n : ℤ)) =
      degreeInv K L n ≫ (xIso (HomologicalComplex.tensorObj K L) n).inv := by
  change (comparisonX K L (-(n : ℤ))).inv = _
  rw [comparisonX_neg]
  rfl

end SerrePositivity.EInfinity.NegativeTensor
