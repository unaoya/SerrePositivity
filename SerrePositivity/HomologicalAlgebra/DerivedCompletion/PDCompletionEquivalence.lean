module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons

/-!
# 二座標完備化の環同型による移送

## 概要
生成元を保つ環同型は、二座標完備化の零次環の同型を与える。

## 方針
一つの座標の完備化を二度移送し、既存の反復との比較を合成する。

## 規約
正則性や有界性は仮定しない。

## 使われ方
BS 著者版 Example 7.9 の通常テンソル積の因子交換。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.DerivedCompletion

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：指定の第二座標を保つ環同型は、p と第二座標の完備化の同型を与える。
方針：p 完備化、第二座標の完備化、二座標と反復の比較を順に合成する。
規約：環同型以外の正則性は不要。
使われ方：完備通常テンソル積の因子の順序を変える。 -/
@[expose] def pdCompletionRingEquiv (e : R ≃+* S) (p : ℕ) (d : R) (b : S) (hd : e d = b) :
    letI := pdCompletionCommRing R p d
    letI := pdCompletionCommRing S p b
    PDCompletionH0 R p d ≃+* PDCompletionH0 S p b := by
  letI := pdCompletionCommRing R p d
  letI := pdCompletionCommRing S p b
  letI := principalCompletionCommRing R (p : R)
  letI := principalCompletionCommRing S (p : S)
  let uR := principalCompletionUnitRingHom R (p : R)
  let uS := principalCompletionUnitRingHom S (p : S)
  let eP := principalCompletionRingEquiv e (p : R) (p : S) (map_natCast e p)
  have heP : eP (uR d) = uS b := by
    rw [principalCompletionRingEquiv_unit, hd]
  letI := iteratedCompletionCommRing R (p : R) d
  letI := iteratedCompletionCommRing S (p : S) b
  let eD := principalCompletionRingEquiv eP (uR d) (uS b) heP
  exact (pdCompletionIteratedEquiv R p d).trans
    (eD.trans (pdCompletionIteratedEquiv S p b).symm)

/-- 概要：二座標完備化の同型は、すべての標準単位の像で元の環同型に一致する。
方針：反復比較と二つの主元完備化の単位公式を適用する。
規約：任意の係数の元を追跡する。
使われ方：因子交換で生成元と基底の脚を保つことの確認。 -/
theorem pdCompletionRingEquiv_unit (e : R ≃+* S) (p : ℕ) (d : R) (b : S)
    (hd : e d = b) (x : R) :
    let := pdCompletionCommRing R p d
    let := pdCompletionCommRing S p b
    pdCompletionRingEquiv e p d b hd (pdCompletionUnit R p d x) =
      pdCompletionUnit S p b (e x) := by
  let := pdCompletionCommRing R p d
  let := pdCompletionCommRing S p b
  let := principalCompletionCommRing R (p : R)
  let := principalCompletionCommRing S (p : S)
  let := iteratedCompletionCommRing R (p : R) d
  let := iteratedCompletionCommRing S (p : S) b
  apply (pdCompletionIteratedEquiv S p b).injective
  simp only [pdCompletionRingEquiv, RingEquiv.trans_apply, RingEquiv.apply_symm_apply,
    pdCompletionIteratedEquiv_unit, iteratedCompletionUnitRingHom, RingHom.comp_apply,
    principalCompletionRingEquiv_unit]

end SerrePositivity.DerivedCompletion
