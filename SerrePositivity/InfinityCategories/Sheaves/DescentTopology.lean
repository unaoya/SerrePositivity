module

public import SerrePositivity.InfinityCategories.Sheaves.UniversalSieveDescent

/-!
概要：元の前層が全引き戻しで降下する篩は位相をなし、その順序で層条件を判定する。
方針：全引き戻しでの降下の推移性を位相の三公理へ渡し、元の層条件へ戻す。
使われ方：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の位相の上限と生成系。
規約：任意の準圏係数。極限存在は仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の前層に対し、すべての引き戻しで元の錐が極限となる篩の位相。 -/
def descentTopology (F : Presheaf C E) : GrothendieckTopology C where
  sieves U := {S | UniversallyDescendingSieve F S}
  top_mem' U := universallyDescendingSieve_top F U
  pullback_stable' := by
    intro X Y S f h
    exact UniversallyDescendingSieve.pullback h f
  transitive' := by
    intro X R hR S hS
    exact UniversallyDescendingSieve.transitive hR (fun t => hS t.property)

/-- 降下位相への所属は、元のすべての引き戻しでの降下そのもの。 -/
lemma mem_descentTopology_iff (F : Presheaf C E) {U : C} (S : Sieve U) :
    S ∈ (descentTopology F) U ↔ UniversallyDescendingSieve F S := Iff.rfl

/-- 元の位相での層条件は、同じ前層の降下位相への包含と同値。 -/
lemma isSheaf_iff_le_descentTopology (J : GrothendieckTopology C) (F : Presheaf C E) :
    IsSheaf J F ↔ J ≤ descentTopology F := by
  constructor
  · intro h U S hS
    apply (mem_descentTopology_iff F S).mpr
    intro V f
    exact h V (S.pullback f) (J.pullback_stable f hS)
  · intro h U S hS
    exact ((mem_descentTopology_iff F S).mp (h U hS)).isLimit

/-- 二つの位相の上限での元の層条件は、両方の元の層条件と同値。 -/
lemma isSheaf_sup_iff (J J' : GrothendieckTopology C) (F : Presheaf C E) :
    IsSheaf (J ⊔ J') F ↔ IsSheaf J F ∧ IsSheaf J' F := by
  simp only [isSheaf_iff_le_descentTopology, sup_le_iff]

end SerrePositivity.InfinityCategories.Sheaves
