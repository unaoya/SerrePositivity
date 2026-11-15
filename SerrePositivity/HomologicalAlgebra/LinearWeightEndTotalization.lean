module
public import SerrePositivity.HomologicalAlgebra.LinearWeightEnd
public import SerrePositivity.HomologicalAlgebra.CochainProductTotalizationHomotopy
public import SerrePositivity.HomologicalAlgebra.ComplexOppositeHomotopy
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
概要：線形重みの鎖複体から非有界複体図式への end を積全複体として取る。
方針：重みの鎖次数を反対化で余鎖次数へ移し、各次数の線形 end と積全複体を合成する。
規約：重みの射に反変。ホモトピー同値の前向き射と逆射は元の比較射の像そのもの。
使われ方：HA 1.2.4、G10 の標準重みと BK 重みの射影分解比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 線形重みの鎖複体から、各次数の end の余鎖二重複体を作る。 -/
def linearWeightEndCochainFunctor (X : Jᵒᵖ ⥤ Complex A) :
    (ChainComplex (Jᵒᵖ ⥤ ModuleCat.{u} A) ℕ)ᵒᵖ ⥤ CochainComplex (Complex A) ℕ :=
  HomologicalComplex.opFunctor (Jᵒᵖ ⥤ ModuleCat.{u} A) (.down ℕ) ⋙
    (linearWeightEnd A X).mapHomologicalComplex (.up ℕ)

/-- 重みの鎖複体からの線形 end の積全複体の関手。 -/
def linearWeightEndTotalFunctor (X : Jᵒᵖ ⥤ Complex A) :
    (ChainComplex (Jᵒᵖ ⥤ ModuleCat.{u} A) ℕ)ᵒᵖ ⥤ Complex A :=
  linearWeightEndCochainFunctor A X ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} A)

/-- 重みの指定鎖ホモトピーを、同じ end 比較射の積全複体へ移す。 -/
def linearWeightEndTotalHomotopy (X : Jᵒᵖ ⥤ Complex A)
    {K L : ChainComplex (Jᵒᵖ ⥤ ModuleCat.{u} A) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) :
    Homotopy ((linearWeightEndTotalFunctor A X).map f.op)
      ((linearWeightEndTotalFunctor A X).map g.op) :=
  cochainProductTotalizationHomotopy (ModuleCat.{u} A)
    ((linearWeightEnd A X).mapHomotopy (complexOppositeHomotopy h))

/-- 重みの鎖ホモトピー同値は、内部次数の有界性なしに end の積全複体を比較する。 -/
def linearWeightEndTotalHomotopyEquiv (X : Jᵒᵖ ⥤ Complex A)
    {K L : ChainComplex (Jᵒᵖ ⥤ ModuleCat.{u} A) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv ((linearWeightEndTotalFunctor A X).obj (op L))
      ((linearWeightEndTotalFunctor A X).obj (op K)) :=
  cochainProductTotalizationHomotopyEquiv (ModuleCat.{u} A)
    ((linearWeightEnd A X).mapHomotopyEquiv (complexOppositeHomotopyEquiv e))

end SerrePositivity.HomologicalAlgebra
