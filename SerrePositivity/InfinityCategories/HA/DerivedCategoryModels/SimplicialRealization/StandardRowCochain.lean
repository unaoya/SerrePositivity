module

public import SerrePositivity.HomologicalAlgebra.TotalRowCochain
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal
import all SerrePositivity.HomologicalAlgebra.TotalRowCochain
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal

/-!
# 単体的実現の全次数の同じ指定成分

## 概要
単体次数 n の元の複体から、実現全複体への次数 -n の cochain を作る。

## 方針
添字延長の標準同型で元の n 次へ戻し、全行の包含の一般公式を使う。

## 規約
各成分は同じ直和包含で、非有界の内部次数を許す。

## 使われ方
HA 1.2.4。strict coherent bar の全高次成分と実現の標準成分の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex HomComplex AlgebraicTopology
open scoped _root_.Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

/-- 延長後の横次数 -n の行と、元の単体次数 n の複体の標準同型。 -/
def doubleComplexRowIso (X : SimplicialObject (Complex A)) (n : ℕ) :
    ((doubleComplexFunctor A).obj X).X (-(n : ℤ)) ≅ X.obj (Opposite.op ⦋n⦌) :=
  (AlternatingFaceMapComplex.obj X).extendXIso SerrePositivity.embUp (by
    change (0 : ℤ) - (n : ℤ) = -(n : ℤ)
    omega)

/-- 元の単体次数 n からの、同じ標準包含による次数 -n の cochain。 -/
def standardRowCochain (X : SimplicialObject (Complex A)) (n : ℕ) :
    Cochain (X.obj (Opposite.op ⦋n⦌)) ((directSumTotalFunctor A).obj X) (-(n : ℤ)) :=
  (Cochain.ofHom (doubleComplexRowIso A X n).inv).comp
    (totalRowCochain ((doubleComplexFunctor A).obj X) (-(n : ℤ))) (zero_add _)

/-- 各高次成分は、元の同型の後の同じ直和包含である。 -/
theorem standardRowCochain_v (X : SimplicialObject (Complex A)) (n : ℕ)
    (p q : ℤ) (h : p + -(n : ℤ) = q) :
    (standardRowCochain A X n).v p q h = (doubleComplexRowIso A X n).inv.f p ≫
      ((doubleComplexFunctor A).obj X).ιTotal (.up ℤ) (-(n : ℤ)) p q (by dsimp; omega) := by
  exact Cochain.comp_v _ _ (zero_add _) p p q (by omega) h

/-- 全高次成分の cochain 微分は、元の横微分の後の同じ包含で与えられる。 -/
theorem standardRowCochain_δ_v (X : SimplicialObject (Complex A)) (n : ℕ) (p : ℤ) :
    (δ (-(n : ℤ)) (-(n : ℤ) + 1) (standardRowCochain A X n)).v
      p ((p + -(n : ℤ)) + 1) (by omega) =
      (doubleComplexRowIso A X n).inv.f p ≫
        (((doubleComplexFunctor A).obj X).d (-(n : ℤ)) (-(n : ℤ) + 1)).f p ≫
        ((doubleComplexFunctor A).obj X).ιTotal (.up ℤ) (-(n : ℤ) + 1) p
          ((p + -(n : ℤ)) + 1) (by dsimp; omega) := by
  dsimp only [standardRowCochain]
  rw [δ_ofHom_comp]
  rw [Cochain.comp_v _ _ (zero_add _) p p _ (by omega) (by omega)]
  rw [totalRowCochain_δ_v]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
