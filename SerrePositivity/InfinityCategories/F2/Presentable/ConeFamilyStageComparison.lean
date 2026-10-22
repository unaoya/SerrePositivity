module

public import SerrePositivity.InfinityCategories.F2.Presentable.WithInitialKanCone
public import SerrePositivity.InfinityCategories.F2.Presentable.StrictConeFamilyRead
public import SerrePositivity.InfinityCategories.F2.Presentable.ConeFamilyColimitTransport
public import SerrePositivity.InfinityCategories.F2.FunctorCurryPointVertex
public import SerrePositivity.InfinityCategories.F2.FunctorVertexConeReindex

/-!
概要：共同 strictification の各段階の全錐は、元の共同図式から読んだ N の strict 錐に一致する。
方針：共同図式の curry の頂点を元の fiber 制限に戻し、錐添字の全単体比較を合成する。
規約：各段階で同型を選ばず、同じ共同図式と指定頂点を保持する。
使われ方：元の coherent な段階錐の極限性を strict な保存定理へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {I J : Type u} [SmallCategory I] [SmallCategory J]

/-- 元の共同 Kan 図式の curry の指定頂点は、同じ fiber 上の strict 図式の全実現。 -/
lemma jointKanDiagram_curry_vertex (D : J × I ⥤ KanObject.{u}) (j : J) :
    (curry ((uliftNerveProductSwapIso J I).inv ≫ kanDiagramCoherentNerve D)).app
        (Opposite.op ⦋0⦌) (ULift.up (nerveVertex j)) =
      functorVertex (kanDiagramCoherentNerve (CategoryTheory.Prod.sectR j I ⋙ D)) := by
  rw [functorCurry_point_vertex]
  have h : lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))
        (SSet.const (ULift.up (nerveVertex j))) ≫ (uliftNerveProductSwapIso J I).inv =
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
  rw [← Category.assoc, h, kanDiagramCoherentNerve_precomp]

variable [Quiver.IsThin I]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
    (ihom (join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj SpaceInfinity.{u})

/-- 元の strict 化した段階錐の全単体は、読み戻した同じ N の strict 錐と一致する。 -/
lemma coneFamilyStrictRealization_stage_map (j : J) :
    functorVertexConeMap ((coneFamilyStrictRealization F).app
      (Opposite.op ⦋0⦌) (ULift.up (nerveVertex j))) =
      strictCoherentConeMap (strictConeFamilyStage (coneFamilyStrictification F) j) := by
  unfold coneFamilyStrictRealization spaceFamilyStrictRealization
  change (functorVertexEquiv _ _).symm
    ((((pre (uliftInitialConeIso I).inv).app SpaceInfinity).app (Opposite.op ⦋0⦌))
      ((curry ((uliftNerveProductSwapIso J (WithInitial I)).inv ≫
        kanDiagramCoherentNerve (spaceFamilyStrictification (coneFamilyWithInitial F)))).app
          (Opposite.op ⦋0⦌) (ULift.up (nerveVertex j)))) = _
  rw [functorVertexMap_precomp, jointKanDiagram_curry_vertex]
  erw [Equiv.symm_apply_apply]
  exact withInitialKanCone_coherentMap _

/-- 元の任意の coherent 段階錐の極限性を、同じ共同 strict 図式の段階錐へ移す。 -/
lemma coneFamilyStage_isLimit_iff (j : J) :
    IsLimitCone (strictCoherentCone
      (strictConeFamilyStage (coneFamilyStrictification F) j)) ↔
    IsLimitCone (functorVertexCone (F.app
      (Opposite.op ⦋0⦌) (ULift.up (nerveVertex j)))) := by
  exact (isLimitCone_functorVertexCone_iff_of_val
    (strictCoherentCone (strictConeFamilyStage (coneFamilyStrictification F) j)) _
    (coneFamilyStrictRealization_stage_map F j)).symm.trans
      (coneFamilyStrictification_stage_isLimit_iff F j)

/-- 元の coherent な段階錐の極限性から、共同 strict 模型の指定余極限錐の極限性を得る。 -/
lemma coneFamilyStrictModelColimit_isLimit
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I]
    (hI : HasCardinalLT I μ) (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom (join (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj SpaceInfinity.{u})
    (hc : ∀ j, IsLimitCone (functorVertexCone (F.app
      (Opposite.op ⦋0⦌) (ULift.up (nerveVertex j))))) :
    letI := isFiltered_of_isCardinalFiltered J μ
    IsLimitCone (strictCoherentCone
      (cardinalFilteredKanConeColimit
        (strictConeFamilyDiagram (coneFamilyStrictification F))
        (strictConeFamilyApex (coneFamilyStrictification F))
        (strictConeFamilyLimitMap (coneFamilyStrictification F)))) := by
  apply strictConeFamilyColimit_isLimit h I hI J
  intro j
  exact (coneFamilyStage_isLimit_iff F j).mpr (hc j)

end SerrePositivity.InfinityCategories.F2.Presentable
