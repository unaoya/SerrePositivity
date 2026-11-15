module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationLocalComma
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.NerveAdjunction

/-!
概要：篩の二段分解と局所 fiber の、反変図式の極限を計算する cofinal 比較。
方針：構成済みの通常の随伴を反転し、元の nerve 写像の left cofinal 性へ渡す。
使われ方：HTT 6.2.2.6 の篩に沿う降下の合成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 交叉の元の圏への合成は、反転すると極限を計算する left cofinal 比較。 -/
lemma sieveFactorizationComposite_op_isLeftCofinal (R S : Sieve U) :
    IsLeftCofinal (nerveMap (sieveFactorizationComposite R S).op) :=
  nerveMap_isLeftCofinal_of_adjunction (sieveFactorizationAdjunction R S).op

/-- 局所右 Kan の comma では、反転した固定 fiber の包含で極限を計算できる。 -/
lemma sieveFactorizationLocalInclusion_op_isLeftCofinal (R S : Sieve U)
    (t : sieveCategory R) :
    IsLeftCofinal (nerveMap (sieveFactorizationLocalInclusion R S t).op) :=
  nerveMap_isLeftCofinal_of_adjunction (sieveFactorizationLocalAdjunction R S t).op

end SerrePositivity.InfinityCategories.Sheaves
