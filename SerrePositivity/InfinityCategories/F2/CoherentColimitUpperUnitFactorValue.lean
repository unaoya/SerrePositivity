module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUpperTransportFactor
public import SerrePositivity.InfinityCategories.F2.CoherentNativeUnitValue

/-!
概要：a6 の上側の指定単位因子を、同じ native 単位の値の指定比較の前合成へ戻す。
方針：既存の終点等式による表示変更だけを除く。
規約：元の指定因子を保持。使われ方：上側単位因子の三角形交換則の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 上側の指定単位因子の値は、同じ native 単位比較を同じ native 作用で前合成した値。 -/
lemma coherentColimitUpperUnitFactorIso_heq_unitValue (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G) :
    HEq (coherentColimitUpperUnitFactorIso B H)
      ((coherentNativeUnitValueIso G).precomp
        (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val) := by
  unfold coherentColimitUpperUnitFactorIso
  exact functorIsoOfEq_heq _ rfl _

end SerrePositivity.InfinityCategories.F2
