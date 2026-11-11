module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.WithInitialKanCone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StrictConeFamilyRead
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConeFamilyColimitTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCurryPointVertex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorVertexConeReindex

/-!
概要：共同 strictification の各段階の全錐は、元の共同図式から読んだ N の strict 錐に一致する。
方針：共同図式の curry の頂点を元の fiber 制限に戻し、錐添字の全単体比較を合成する。
規約：各段階で同型を選ばず、同じ共同図式と指定頂点を保持する。
使われ方：元の coherent な段階錐の極限性を strict な保存定理へ渡す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {I J : Type u} [SmallCategory I] [SmallCategory J]

/-- 元の共同 Kan 図式の curry の指定頂点は、同じ fiber 上の strict 図式の全実現。 -/
lemma jointKanDiagram_curry_vertex (D : J × I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (j : J) :
    (curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.uliftNerveProductSwapIso J I).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve D)).app
        (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (CategoryTheory.Prod.sectR j I ⋙ D)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorCurry_point_vertex]
  have h : lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))
        (SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j))) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.uliftNerveProductSwapIso J I).inv =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (CategoryTheory.Prod.sectR j I)) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    refine ComposableArrows.ext (fun _ ↦ rfl) ?_
    intro a ha
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  rw [← Category.assoc, h, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_precomp]

variable [Quiver.IsThin I]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 元の strict 化した段階錐の全単体は、読み戻した同じ N の strict 錐と一致する。 -/
lemma coneFamilyStrictRealization_stage_map (j : J) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexConeMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictRealization F).app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.strictConeFamilyStage (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F) j) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictRealization _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.spaceFamilyStrictRealization
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    ((((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uliftInitialConeIso I).inv).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).app (Opposite.op ⦋0⦌))
      ((curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.uliftNerveProductSwapIso J (WithInitial I)).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.spaceFamilyStrictification (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyWithInitial F)))).app
          (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexMap_precomp, jointKanDiagram_curry_vertex]
  erw [Equiv.symm_apply_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.withInitialKanCone_coherentMap _

/-- 元の任意の coherent 段階錐の極限性を、同じ共同 strict 図式の段階錐へ移す。 -/
lemma coneFamilyStage_isLimit_iff (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.strictConeFamilyStage (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F) j)) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (F.app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)))) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_functorVertexCone_iff_of_val
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.strictConeFamilyStage (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F) j)) _
    (coneFamilyStrictRealization_stage_map F j)).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification_stage_isLimit_iff F j)

/-- 元の coherent な段階錐の極限性から、共同 strict 模型の指定余極限錐の極限性を得る。 -/
lemma coneFamilyStrictModelColimit_isLimit
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I]
    (hI : HasCardinalLT I μ) (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hc : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (F.app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j))))) :
    letI := isFiltered_of_isCardinalFiltered J μ
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredKanConeColimit
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.strictConeFamilyDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.strictConeFamilyApex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.strictConeFamilyLimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F)))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.strictConeFamilyColimit_isLimit h I hI J
  intro j
  exact (coneFamilyStage_isLimit_iff F j).mpr (hc j)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
