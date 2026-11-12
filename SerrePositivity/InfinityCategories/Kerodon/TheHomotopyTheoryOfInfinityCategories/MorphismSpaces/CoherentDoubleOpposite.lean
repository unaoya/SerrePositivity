module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentNervePost

/-!
概要：二重の反対の単体的豊穣圏から元の圏への標準関手。
方針：対象を二回 unop し、二回の対称性が合成で打ち消し合うことを使う。
規約：SSet 自体の反転とは区別する。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent nerve の標準射の逆と往復則。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：二重の反対の単体的豊穣圏から元の圏への標準の豊穣関手。
方針：対象を二回 unop し、Hom は恒等射とする。
規約：二重反対の合成の二つの対称性は打ち消し合う。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent simplex の往復の標的。 -/
def coherentEnrichedDoubleUnop (C : Type v) [EnrichedCategory SSet.{u} C] :
    EnrichedFunctor SSet Cᵒᵖᵒᵖ C where
  obj x := x.unop.unop
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp _ _ _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    rfl

/-- 概要：二重反対からの標準関手は豊穣関手に自然。
方針：対象と Hom の射を直接比較する。
規約：対象の宇宙は異なってよい。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent simplex の往復則の合成の整理。 -/
lemma coherentEnrichedDoubleUnop_naturality {C : Type v} {D : Type w}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    (F : EnrichedFunctor SSet C D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F)).comp SSet
      (coherentEnrichedDoubleUnop D) =
      (coherentEnrichedDoubleUnop C).comp SSet F := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) (fun _ _ => ?_)
  change (_ ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp only [Category.comp_id, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
