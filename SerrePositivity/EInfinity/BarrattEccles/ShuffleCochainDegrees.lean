module

public import SerrePositivity.EInfinity.BarrattEccles.Generators

/-!
# shuffle の鎖次数とコチェイン次数の微分の比較

概要：Berger–Fresse §1.1.3 の鎖次数の微分公式を整数コチェイン次数へ移す。
方針：次数埋め込み q ↦ −q の延長の標準同型と微分の公式を用いる。
規約：鎖次数 p の成分はコチェイン次数 −p に対応し、微分は +1 である。
使われ方：shuffle の双線形写像を既存のテンソル複体からの射へまとめる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：負の整数次数の微分は正規化鎖の微分を同型で移したものである（Berger–Fresse §1.1.2）。
方針：次数埋め込みの延長の微分の公式を適用する。
規約：任意の二つの自然数 p,q について述べ、隣接しないときは両辺とも零になる。
使われ方：鎖次数で証明した Leibniz 則をコチェイン次数で使う。 -/
lemma complex_d_eq (n p q : ℕ) :
    (complex A n).d (-(p : ℤ)) (-(q : ℤ)) =
      (complexXIso A n p).hom ≫ (normalizedChains A n).d p q ≫ (complexXIso A n q).inv :=
  HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat rfl rfl

/-- 概要：次数同型の順方向は微分と可換する（Berger–Fresse §1.1.2）。
方針：微分の移送の公式の右側で逆同型と順同型を消去する。
規約：鎖次数 p から q の微分を比較する。
使われ方：shuffle の微分の等式の出力を正規化鎖へ移す。 -/
lemma complexXIso_hom_d (n p q : ℕ) :
    (complex A n).d (-(p : ℤ)) (-(q : ℤ)) ≫ (complexXIso A n q).hom =
      (complexXIso A n p).hom ≫ (normalizedChains A n).d p q := by
  rw [complex_d_eq A n p q]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：次数同型の逆方向は微分と可換する（Berger–Fresse §1.1.2）。
方針：微分の移送の公式の左側で順同型と逆同型を消去する。
規約：鎖次数 p から q の微分を比較する。
使われ方：入力の微分を正規化鎖の微分へ直す。 -/
lemma complexXIso_inv_d (n p q : ℕ) :
    (complexXIso A n p).inv ≫ (complex A n).d (-(p : ℤ)) (-(q : ℤ)) =
      (normalizedChains A n).d p q ≫ (complexXIso A n q).inv := by
  rw [complex_d_eq A n p q]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 概要：任意の非正整数次数の成分を正規化鎖の成分と同定する（Berger–Fresse §1.1.2）。
方針：非正整数 r に対応する自然数 (−r).toNat を次数埋め込みで戻す。
規約：出力の鎖次数は (−r).toNat である。
使われ方：整数次数で添字づけられたテンソル成分上に shuffle を定義する。 -/
def complexXIsoNonpos (n : ℕ) (r : ℤ) (hr : r ≤ 0) :
    (complex A n).X r ≅ (normalizedChains A n).X (-r).toNat :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (by
    change -(((-r).toNat : ℕ) : ℤ) = r
    omega)

/-- 概要：非正整数次数の標準同型は微分と可換する（Berger–Fresse §1.1.2）。
方針：延長の微分の公式と標準同型の逆性を使う。
規約：両方の整数次数が非正の場合を扱う。
使われ方：整数次数で定義した shuffle の成分について微分の両立性を判定する。 -/
lemma complexXIsoNonpos_hom_d (n : ℕ) (r s : ℤ) (hr : r ≤ 0) (hs : s ≤ 0) :
    (complex A n).d r s ≫ (complexXIsoNonpos A n s hs).hom =
      (complexXIsoNonpos A n r hr).hom ≫ (normalizedChains A n).d (-r).toNat (-s).toNat := by
  have hd := HomologicalComplex.extend_d_eq (normalizedChains A n) ComplexShape.embeddingDownNat
    (i := (-r).toNat) (j := (-s).toNat)
    (show -(((-r).toNat : ℕ) : ℤ) = r by omega)
    (show -(((-s).toNat : ℕ) : ℤ) = s by omega)
  change (complex A n).d r s =
    (complexXIsoNonpos A n r hr).hom ≫ (normalizedChains A n).d (-r).toNat (-s).toNat ≫
      (complexXIsoNonpos A n s hs).inv at hd
  rw [hd]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.EInfinity.BarrattEccles
