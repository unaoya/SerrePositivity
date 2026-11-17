module

public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphColimit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Unit

/-!
# 元の E 代数の hammock の空語による単位射

概要：任意の可換環上で、元の空語の graph と全語の余極限への単位射を構成。
方針：実際の弱同値に全次数で定値な空語の単位を代入する。
規約：元の端点を変更しない。左右単位則は余極限上の合成の構成後に証明する。
使われ方：元の hammock の豊穣圏の単位。
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory _root_.HomotopicalAlgebra MonoidalCategory

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 同じ元の E 代数の空語の graph への単位射。 -/
def algebraHammockGraphUnit (X : (operad A).Algebra) :
    𝟙_ SSet.{u + 1} ⟶ algebraHammockGraph A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty X X := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit (weakEquivalences (operad A).Algebra) X

/-- 同じ元の空語の標準射を通る、全語の余極限への単位射。 -/
def algebraHammockColimitUnit (X : (operad A).Algebra) :
    𝟙_ SSet.{u + 1} ⟶ algebraHammockColimitGraph A X X :=
  algebraHammockGraphUnit A X ≫ algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty X X

end SerrePositivity.EInfinity.BarrattEccles
