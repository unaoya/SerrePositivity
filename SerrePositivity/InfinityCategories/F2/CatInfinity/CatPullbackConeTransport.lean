module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackDiagramComparison
public import SerrePositivity.InfinityCategories.F1.CatInfinity.SpecifiedLimitConeTransport

/-!
概要：Cat_∞ の引き戻し錐の追跡可能な相対輸送。
方針：頂点を固定し、定値 path の切断による指定円柱を保つ。
規約：図式の同型の代表を別に選び直さない。
使われ方：元の p、q の図式上の錐の二脚の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：元の cospan の極限錐を指定切断の円柱を保って構成する。
方針：成分が同値な自然変換の coherent prism を相対錐の輸送に適用する。
規約：頂点固定と全図式の指定自然変換をデータとして保持する。
使われ方：引き戻し錐の二射影との具体的な照合。 -/
def catPullbackConeTransport (p : A ⟶ C) (q : B ⟶ C) :
    SpecifiedLimitConeTransport
      (p := HomotopyLimits.strictCoherentDiagram (catPullbackDiagram p q))
      (strictCoherentNatTransMap (catPullbackReplacementNatTrans p q))
      (catPullbackReplacementCone p q) := by
  apply specifiedLimitConeTransport _ (strictCoherentNatTransMap_zero _)
    (strictCoherentNatTransMap_one _) _ _ (catPullbackReplacementCone_isLimit p q)
  apply strictCoherentNatTransMap_vertical_isInvertible
  intro i
  exact (catInfinityEdge_isInvertible_iff _).mpr
    (catPullbackReplacementNatTrans_isEquivalence p q i)

end SerrePositivity.InfinityCategories.F2
