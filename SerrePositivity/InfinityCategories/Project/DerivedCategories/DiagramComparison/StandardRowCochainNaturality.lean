module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain

/-!
概要：元の直和実現の各行のcochainを、元の単体的自然変換に厳密に自然にする。
方針：添字延長の標準同型と、既存のtotalRowCochain_naturalityを使う。
規約：全内部次数を保持する。図式を有界なものへ制限しない。
使われ方：3b-3 R6、barの比較射と指定余錐の元の高次成分の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex HomComplex AlgebraicTopology
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A]
  {X Y : SimplicialObject (Complex A)} (η : X ⟶ Y)

/-- 元の横次数の標準表示同型は、同じ単体的自然変換に自然。 -/
lemma doubleComplexRowIso_inv_naturality (n : ℕ) :
    (doubleComplexRowIso A X n).inv ≫ ((doubleComplexFunctor A).map η).f (-(n : ℤ)) =
      η.app (Opposite.op ⦋n⦌) ≫ (doubleComplexRowIso A Y n).inv := by
  change (doubleComplexRowIso A X n).inv ≫
    (HomologicalComplex.extendMap ((alternatingFaceMapComplex (Complex A)).map η)
      SerrePositivity.embUp).f (-(n : ℤ)) = _
  rw [HomologicalComplex.extendMap_f _ _ (show SerrePositivity.embUp.f n = -(n : ℤ) by
    change (0 : ℤ) - (n : ℤ) = -(n : ℤ)
    omega)]
  change (doubleComplexRowIso A X n).inv ≫
    (doubleComplexRowIso A X n).hom ≫ η.app (Opposite.op ⦋n⦌) ≫
      (doubleComplexRowIso A Y n).inv = _
  rw [Iso.inv_hom_id_assoc]

/-- 元の全行のcochainは、元の実現関手の射と各内部次数で厳密に可換。 -/
lemma standardRowCochain_naturality (n : ℕ) (p q : ℤ) (h : p + -(n : ℤ) = q) :
    (standardRowCochain A X n).v p q h ≫ ((directSumTotalFunctor A).map η).f q =
      (η.app (Opposite.op ⦋n⦌)).f p ≫ (standardRowCochain A Y n).v p q h := by
  rw [standardRowCochain_v, standardRowCochain_v, Category.assoc]
  change (doubleComplexRowIso A X n).inv.f p ≫
      (totalRowCochain ((doubleComplexFunctor A).obj X) (-(n : ℤ))).v p q h ≫
        (HomologicalComplex₂.total.map ((doubleComplexFunctor A).map η) (.up ℤ)).f q = _
  rw [totalRowCochain_naturality]
  have hr := congrArg (fun f => f.f p) (doubleComplexRowIso_inv_naturality A η n)
  simpa only [HomologicalComplex.comp_f, Category.assoc, totalRowCochain_v] using
    congrArg (fun f => f ≫ ((doubleComplexFunctor A).obj Y).ιTotal (.up ℤ)
      (-(n : ℤ)) p q (by dsimp; omega)) hr

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
