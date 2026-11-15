module
public import SerrePositivity.HomologicalAlgebra.ProductTotalHorizontalHomotopy
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
概要：非負余鎖次数の二重複体のホモトピーを、非有界の積全複体へ移す。
方針：横次数を整数へ零延長し、指定された横ホモトピーを積射影で全複体化する。
規約：内部次数は任意の整数。積の完全性や収束を仮定しない。
使われ方：HA 1.2.4、G10 の線形重みの射影分解の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits HomologicalComplex
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra
variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [∀ K : HomologicalComplex₂ Cᵒᵖ (.down ℤ) (.down ℤ), K.HasTotal (.down ℤ)]

/-- 非負の横余鎖次数を零延長して取る、同じ積全複体の関手。 -/
def cochainProductTotalizationFunctor :
    CochainComplex (CochainComplex C ℤ) ℕ ⥤ CochainComplex C ℤ :=
  ComplexShape.embeddingUpNat.extendFunctor (CochainComplex C ℤ) ⋙ ProductTotal.functor C

/-- 元の指定横ホモトピーを積全複体の同じ二つの射へ移す。 -/
def cochainProductTotalizationHomotopy
    {K L : CochainComplex (CochainComplex C ℤ) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) :
    Homotopy ((cochainProductTotalizationFunctor C).map f)
      ((cochainProductTotalizationFunctor C).map g) :=
  ProductTotal.horizontalHomotopy (h.extend ComplexShape.embeddingUpNat)

/-- 横の鎖ホモトピー同値は内部次数の有界性なしに積全複体の同値を誘導する。 -/
def cochainProductTotalizationHomotopyEquiv
    {K L : CochainComplex (CochainComplex C ℤ) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv ((cochainProductTotalizationFunctor C).obj K)
      ((cochainProductTotalizationFunctor C).obj L) where
  hom := (cochainProductTotalizationFunctor C).map e.hom
  inv := (cochainProductTotalizationFunctor C).map e.inv
  homotopyHomInvId := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      cochainProductTotalizationHomotopy C e.homotopyHomInvId
  homotopyInvHomId := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      cochainProductTotalizationHomotopy C e.homotopyInvHomId

end SerrePositivity.HomologicalAlgebra
