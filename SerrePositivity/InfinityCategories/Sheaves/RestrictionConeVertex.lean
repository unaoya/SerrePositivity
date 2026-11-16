module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits

/-!
概要：篩上の指定制限錐の頂点は元の前層の評価値である。
方針：nerve錐の頂点、宇宙持ち上げ、後合成の既存の計算則を合成する。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の層条件の指定頂点。
規約：同値な別の頂点で置き換えず、実際の頂点の等式を示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]

/-- 指定制限錐は元のF(U)を頂点に持つ。 -/
lemma restrictionCone_vertex (F : Presheaf C E) {U : C} (S : Sieve U) :
    (restrictionCone F S).vertex =
      F.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Opposite.op U))) := by
  change (mapJoinCone F
    (SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u,u+1}
      (nerveCone (sieveCone S)))).vertex = _
  rw [mapJoinCone_vertex,
    SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex,
    nerveCone_vertex]
  rfl

end SerrePositivity.InfinityCategories.Sheaves
