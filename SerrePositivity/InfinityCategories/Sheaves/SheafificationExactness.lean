module

public import SerrePositivity.InfinityCategories.Sheaves.SheafStability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.AdjunctionExactness
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFiniteLimitPreservation

/-!
概要：安定な presentable 係数の指定層化は、元の任意有限形状の極限錐を保つ。
方針：層圏の安定性から反射と包含を完全とし、同じ自己関手の完全性を有限極限保存へ移す。
  文献対応：HTT 6.2.2.7、HA Proposition 1.1.4.1、Kerodon §7.1（Tag 02H1）。
規約：指定した層化の選択を変えない。Postnikov 左完全性は主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 安定係数の指定層化の自己関手は、同じ反射と包含の完全性の合成で完全。 -/
theorem sheafification_isExactFunctor [IsStable E] (J : GrothendieckTopology C)
    (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    IsExactFunctor (sheafificationFunctor J hJ) := by
  letI : IsStable (PresheafCat C E) := isStable_functorCategory _ E
  letI : IsStable (SheafCat J E) := sheaf_isStable J hE
  let r := Classical.choice hJ
  letI := isExactFunctor_leftAdjoint r.adjunction
  letI := isExactFunctor_rightAdjoint r.adjunction
  change IsExactFunctor (r.reflector ≫ sheafInclusion J)
  exact isExactFunctor_comp r.reflector
    (fullSubcomplexOnVertices (PresheafCat C E) (sheafProperty (E := E) J)).ι

/-- 安定係数の同じ指定層化は、元の任意有限形状の指定極限錐を保つ。 -/
theorem sheafification_map_isLimit_finite [IsStable E] (J : GrothendieckTopology C)
    (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {K : SSet.{u + 1}} [K.Finite] {p : K ⟶ PresheafCat C E}
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (sheafificationFunctor J hJ) c) := by
  letI : IsStable (PresheafCat C E) := isStable_functorCategory _ E
  letI := sheafification_isExactFunctor J hJ hE
  exact isExactFunctor_map_isLimit_finite (sheafificationFunctor J hJ) c hc

end SerrePositivity.InfinityCategories.Sheaves
