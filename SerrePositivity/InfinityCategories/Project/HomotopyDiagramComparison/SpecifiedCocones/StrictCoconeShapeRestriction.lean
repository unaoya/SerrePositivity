module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictNativeCocones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction

/-!
概要：通常の指定余錐の全 coherent 表示と、添字関手による制限の可換則。
方針：反対の錐の再添字則と反転の制限則を、同じ添字の標準同型で戻す。
規約：脚や頂点だけの比較ではなく、join からの全射の等式。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、S8 の押し出しの二つの三角形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I J : Type u} [SmallCategory I] [SmallCategory J]

/-- 通常の添字の反転比較は、元の添字関手に全単体で自然。
HTT 4.2.4.1、Kerodon §4.6.7（Tag 01LA）、既存の添字同型の法則。 -/
lemma strictCoconeIndexIso_naturality (G : J ⥤ I) :
    (SSet.uliftFunctor.{v, u}).map (nerveMap G) ≫ (strictCoconeIndexIso.{u, v} I).hom =
      (strictCoconeIndexIso.{u, v} J).hom ≫
        SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (nerveMap G.op)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 反対の錐の同じ全反転余錐は、元の通常の添字関手での制限を保つ。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、制限則の証明分割。 -/
lemma strictCoconeOppositeWhisker_reverse_val
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F : I ⥤ C} (c : Cocone F) (G : J ⥤ I) :
    joinMap (SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (nerveMap G.op)))
        (𝟙 Δ[0]) ≫ (strictCoherentCone c.op).reverseCocone.val =
      (strictCoherentCone (c.whisker G).op).reverseCocone.val := by
  change ((strictCoherentCone c.op).reverseCocone.restrict
    (SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (nerveMap G.op)))).val = _
  rw [reverseCocone_restrict_val]
  rw [SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.JoinCone.reverseCocone_val,
    SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.JoinCone.reverseCocone_val]
  change _ ≫ _ ≫ SSet.opFunctor.map
      (joinMap (𝟙 Δ[0]) ((SSet.uliftFunctor.{v, u}).map (nerveMap G.op)) ≫
        strictCoherentConeMap c.op) =
    _ ≫ _ ≫ SSet.opFunctor.map (strictCoherentConeMap (c.op.whisker G.op))
  rw [strictCoherentConeMap_whisker]


/-- 通常の指定余錐の全表示は、元の添字関手に沿う制限と可換。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）。単射性や同値性は要求しない。 -/
lemma strictNativeCocone_whisker_val
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F : I ⥤ C} (c : Cocone F) (G : J ⥤ I) :
    joinMap ((SSet.uliftFunctor.{v, u}).map (nerveMap G)) (𝟙 Δ[0]) ≫
        (strictNativeCocone c).val = (strictNativeCocone (c.whisker G)).val := by
  rw [strictNativeCocone_val, strictNativeCocone_val]
  unfold strictCoherentCocone
  rw [coherentCoconePost_val, coherentCoconePost_val]
  change joinMap ((SSet.uliftFunctor.{v, u}).map (nerveMap G)) (𝟙 Δ[0]) ≫
      ((joinMap (strictCoconeIndexIso.{u, v} I).hom (𝟙 Δ[0]) ≫
        (strictCoherentCone c.op).reverseCocone.val) ≫ (coherentOppositeReturnIso C).hom) =
    (joinMap (strictCoconeIndexIso.{u, v} J).hom (𝟙 Δ[0]) ≫
      (strictCoherentCone (c.whisker G).op).reverseCocone.val) ≫
        (coherentOppositeReturnIso C).hom
  rw [← Category.assoc, ← Category.assoc, ← joinMap_comp, Category.id_comp,
    strictCoconeIndexIso_naturality]
  have hj : joinMap ((strictCoconeIndexIso.{u, v} J).hom ≫
      SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (nerveMap G.op))) (𝟙 Δ[0]) =
    joinMap (strictCoconeIndexIso.{u, v} J).hom (𝟙 Δ[0]) ≫
      joinMap (SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (nerveMap G.op)))
        (𝟙 Δ[0]) := by
    rw [← joinMap_comp, Category.id_comp]
  rw [hj]
  simp only [Category.id_comp, Category.assoc]
  rw [← Category.assoc
    (joinMap (SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (nerveMap G.op)))
      (𝟙 Δ[0])) (strictCoherentCone c.op).reverseCocone.val
    (coherentOppositeReturnIso C).hom,
    strictCoconeOppositeWhisker_reverse_val]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
