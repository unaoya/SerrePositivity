module
public import SerrePositivity.HomologicalAlgebra.WeightEndHomComponents
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomDifferential

/-!
概要：重み end と Hom の次数同値が指定成分で何をするかを計算する。
方針：零延長からの成分表示の相互逆を使い、同じ積射影に符号を掛けた式を得る。
規約：零鎖次数の評価は符号を持たない。図式の自然変換全体として等式を述べる。
使われ方：HA 1.2.4、G10 の微分との可換性と指定脚の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]
variable (K : ChainComplex (Jᵒᵖ ⥤ ModuleCat.{u} A) ℕ) (X : Jᵒᵖ ⥤ Complex A)

/-- 次数同値の n 成分は元の積射影に指定符号を掛けたもの。 -/
theorem weightEndHomComponentsEquiv_rows (q : ℤ)
    (z : ((linearWeightEndTotalFunctor A X).obj (op K)).X q) (n : ℕ) :
    extendedChainHomRows K
      ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X) q
      (weightEndHomComponentsEquiv A K X q z) n =
    weightEndHomSign n q • CochainProductTotal.componentπ
      ((linearWeightEndCochainFunctor A X).obj (op K)) n q z := by
  change extendedChainHomRows K _ q (extendedChainHomRowsInverse K _ q _) n = _
  rw [extendedChainHomRows_inverse]
  rfl

/-- 零鎖次数の指定射影は、この比較で変わらない。 -/
theorem weightEndHomComponentsEquiv_zero (q : ℤ)
    (z : ((linearWeightEndTotalFunctor A X).obj (op K)).X q) :
    extendedChainHomRows K
      ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X) q
      (weightEndHomComponentsEquiv A K X q z) 0 =
    CochainProductTotal.componentπ
      ((linearWeightEndCochainFunctor A X).obj (op K)) 0 q z := by
  rw [weightEndHomComponentsEquiv_rows, weightEndHomSign_zero, one_smul]

end SerrePositivity.HomologicalAlgebra
