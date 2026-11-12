module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.StrictConeTransformation
public import SerrePositivity.KST.Fibration.SizedDiagramTransformation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-! # 元の頂点・全脚の通常の錐比較を、同じ全 coherent 錐の比較へ送る -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.Fibration
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] {F G : I ⥤ C}

/-- 頂点と全成分が可逆な同じ通常の比較は、全 coherent 錐の自然同型を与える。 -/
def strictCoherentConeTransformationIso [Quasicategory (SimplicialNerve C)]
    (α : F ⟶ G) (c : Cone F) (d : Cone G) (f : c.pt ⟶ d.pt)
    (hf : ∀ i, f ≫ d.π.app i = c.π.app i ≫ α.app i)
    (hα : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (α.app i)))
    (hfi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c).val (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone d).val := by
  have he := sizedCoherentNatTransIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictConeTransformation α c d f hf) (by
    intro j
    cases j with
    | star => exact hfi
    | of j => exact hα (AsSmall.down.obj j))
  exact he.precomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictConeShapeMap (I := I))

/-- 同じ通常の錐比較の全成分の可逆性に沿って、実極限性を移す。 -/
theorem strictCoherentCone_isLimit_iff_of_transformation [Quasicategory (SimplicialNerve C)]
    (α : F ⟶ G) (c : Cone F) (d : Cone G) (f : c.pt ⟶ d.pt)
    (hf : ∀ i, f ≫ d.π.app i = c.π.app i ≫ α.app i)
    (hα : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (α.app i)))
    (hfi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone d) :=
  ⟨fun h => h.of_functorIso (strictCoherentConeTransformationIso α c d f hf hα hfi),
    fun h => h.of_functorIso (strictCoherentConeTransformationIso α c d f hf hα hfi).symm⟩

end SerrePositivity.KST.Fibration
