module

public import SerrePositivity.EInfinity.TableReduction.CochainMap
public import SerrePositivity.EInfinity.Surjection.ComplexDegrees
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCochainDegrees

/-!
# 整数 TR の非正次数の比較と全整数次数の全射性

概要：Berger–Fresse §1.3 の TR の鎖次数の公式を任意の非正整数次数で使う。
方針：次数延長の射の成分公式を比較同型で評価し、正次数では零対象を使う。
規約：全整数次数・全 arity・任意の可換環。
使われ方：BE の整数合成と χ の整数合成を TR で比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.TableReduction

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：任意の非正整数次数の TR の成分は元の正規化 TR（BF §1.3）。
方針：次数延長の成分公式をその整数次数に適用する。
規約：鎖次数は (−r).toNat。
使われ方：整数合成の非正入力を鎖合成保存へ移す。 -/
lemma cochainMap_f_nonpos (n : ℕ) (r : ℤ) (hr : r ≤ 0) :
    (cochainMap A n).f r = (BarrattEccles.complexXIsoNonpos A n r hr).hom ≫
      ModuleCat.ofHom (normalizedMap A n (-r).toNat) ≫
        (Surjection.complexXIsoNonpos A n r hr).inv :=
  HomologicalComplex.extendMap_f (chainMap A n) ComplexShape.embeddingDownNat (by
    change -(((-r).toNat : ℕ) : ℤ) = r
    omega)

/-- 概要：非正次数の TR の像を全射語加群へ移すと正規化 TR（BF §1.3）。
方針：成分公式と比較同型の逆性を元で評価する。
規約：入力元の選択に制限を課さない。
使われ方：整数部分合成の二入力の比較。 -/
lemma cochainMap_nonpos_hom_apply (n : ℕ) (r : ℤ) (hr : r ≤ 0)
    (x : (BarrattEccles.complex A n).X r) :
    (Surjection.complexXIsoNonpos A n r hr).hom ((cochainMap A n).f r x) =
      normalizedMap A n (-r).toNat ((BarrattEccles.complexXIsoNonpos A n r hr).hom x) := by
  rw [cochainMap_f_nonpos]
  exact (Surjection.complexXIsoNonpos A n r hr).toLinearEquiv.apply_symm_apply _

/-- 概要：非正次数の TR は比較同型の逆写像と可換（BF §1.3）。
方針：BE 側の逆同型と成分公式の順同型を消去する。
規約：引数は任意の正規化 BE 鎖。
使われ方：整数合成の出力の比較。 -/
lemma cochainMap_nonpos_inv_apply (n : ℕ) (r : ℤ) (hr : r ≤ 0)
    (x : (BarrattEccles.normalizedChains A n).X (-r).toNat) :
    (cochainMap A n).f r ((BarrattEccles.complexXIsoNonpos A n r hr).inv x) =
      (Surjection.complexXIsoNonpos A n r hr).inv (normalizedMap A n (-r).toNat x) := by
  rw [cochainMap_f_nonpos]
  change (Surjection.complexXIsoNonpos A n r hr).inv
    (normalizedMap A n (-r).toNat
      ((BarrattEccles.complexXIsoNonpos A n r hr).toLinearEquiv
        ((BarrattEccles.complexXIsoNonpos A n r hr).toLinearEquiv.symm x))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- 概要：整数 TR は全整数次数で全射（BF §1.3.4）。
方針：非正次数は既存の全射性、正次数は目標が零対象であることを使う。
規約：全 arity と任意の係数環。
使われ方：整数複体の合成法則と微分を BE の法則から移す。 -/
lemma cochainMap_f_surjective_int (n : ℕ) (r : ℤ) :
    Function.Surjective ((cochainMap A n).f r).hom := by
  by_cases hr : 0 < r
  · intro y
    refine ⟨0, ?_⟩
    rw [map_zero, Surjection.complex_eq_zero_of_positive A n r hr y]
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, r = -(d : ℤ) := ⟨(-r).toNat, by omega⟩
    exact cochainMap_f_surjective A n d

/-- 概要：整数 TR の微分可換性を任意の元で評価する（BF §1.3）。
方針：複体射の可換性を元に適用する。
規約：隣接しない次数の零微分も含む。
使われ方：BE の整数 Leibniz 則を χ へ移す。 -/
lemma cochainMap_d_apply (n : ℕ) (r s : ℤ) (x : (BarrattEccles.complex A n).X r) :
    (cochainMap A n).f s ((BarrattEccles.complex A n).d r s x) =
      (Surjection.complex A n).d r s ((cochainMap A n).f r x) :=
  congrArg (fun f => f x) ((cochainMap A n).comm r s).symm

end SerrePositivity.EInfinity.TableReduction
