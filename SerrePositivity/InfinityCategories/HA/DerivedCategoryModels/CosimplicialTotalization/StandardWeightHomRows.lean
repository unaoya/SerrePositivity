module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalInverseEvaluation
public import SerrePositivity.HomologicalAlgebra.WeightEndHomEvaluation

/-!
# 標準重みへの指定射から得る Hom の各行

概要：同じ重み射の前合成と符号つきend–Hom比較を、元の積成分で評価する。
方針：積射影の自然性と自由Yoneda逆評価を使う。
規約：IS-W2 B02の成分照合の分割。内部次数を非有界に保つ。
使われ方：HA 1.2.4、元のHom–Totから指定BK Homへの射の行表示。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 概要：指定標準重み射によるHom比較の各行を同じ積成分で計算する。
方針：元の積射影の自然性・逆評価・end–Hom成分式。
規約：任意の鎖重みKと指定射g。使われ方：HA 1.2.4 のBK比較の行の照合。 -/
theorem standardWeightHomComparison_rows
    (K : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ)
    (g : K ⟶ (alternatingFaceMapComplex _).obj (standardSimplexWeight (ModuleCat.of A A)))
    (X : CosimplicialObject (Complex A)) (q : ℤ)
    (z : ((productTotalFunctor A).obj X).X q) (n : ℕ) :
    extendedChainHomRows K
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram X)) q
      ((weightEndHomIso A K (doubleOppositeDiagram X)).hom.f q
        (((linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map g.op).f q
          ((standardWeightEndTotalIso X).inv.f q z))) n =
    weightEndHomSign n q • (g.f n ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram X)).inv.f (q - n) (componentπ X n q z)) := by
  rw [weightEndHomIso_hom_f, weightEndHomComponentsEquiv_rows]
  apply congrArg (fun t => weightEndHomSign n q • t)
  have hn := CochainProductTotal.componentπ_naturality
    ((linearWeightEndCochainFunctor A (doubleOppositeDiagram X)).map g.op) n q
  have he := ConcreteCategory.congr_hom hn ((standardWeightEndTotalIso X).inv.f q z)
  change CochainProductTotal.componentπ
      ((linearWeightEndCochainFunctor A (doubleOppositeDiagram X)).obj (Opposite.op K)) n q
      (((linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map g.op).f q
        ((standardWeightEndTotalIso X).inv.f q z)) =
    g.f n ≫ CochainProductTotal.componentπ
      ((linearWeightEndCochainFunctor A (doubleOppositeDiagram X)).obj
        (Opposite.op ((alternatingFaceMapComplex _).obj
          (standardSimplexWeight (ModuleCat.of A A))))) n q
      ((standardWeightEndTotalIso X).inv.f q z) at he
  rw [he]
  have hs := ConcreteCategory.congr_hom (standardWeightEndTotalIso_inv_component X n q) z
  change CochainProductTotal.componentπ
      ((linearWeightEndCochainFunctor A (doubleOppositeDiagram X)).obj
        (Opposite.op ((alternatingFaceMapComplex _).obj
          (standardSimplexWeight (ModuleCat.of A A))))) n q
      ((standardWeightEndTotalIso X).inv.f q z) =
    ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
      (doubleOppositeDiagram X)).inv.f (q - n) (componentπ X n q z) at hs
  rw [hs]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
