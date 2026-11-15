module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation

/-!
概要：元の関手評価は係数の全後合成と厳密に可換する。
方針：同じ内部 Hom の単体の評価を計算する。
使われ方：Kerodon §4.5.1（Tag 01DQ）の関手の成分評価、HTT 1.2.7.3。
規約：全単体の写像の等式であり、頂点ごとの同型へ弱めない。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 元の関手評価は、同じ係数関手による後合成と厳密に可換。 -/
lemma evaluateFunctorAt_postcomp {K X Y : SSet.{u}} (F : X ⟶ Y) (k : K _⦋0⦌) :
    (ihom K).map F ≫ evaluateFunctorAt k = evaluateFunctorAt (Y := X) k ≫ F := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
