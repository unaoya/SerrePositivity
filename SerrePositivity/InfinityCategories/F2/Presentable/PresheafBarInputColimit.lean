module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafBarIndexEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullyFaithfulPrecompositionColimits
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Core.CatInfinity.CoconeValEquality

/-!
概要：bar 入力の元の前層を頂点とする密度余極限。
方針：初頂点局所化の充満忠実な前合成と単体添字同型で、元の密度余錐を制限する。
規約：元の前層を厳密な頂点に固定する。
使われ方：bar 左 Kan 延長の幾何学的実現を元の前層へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 概要：元の前層は、元の全単体へ展開した bar 入力の同じ頂点の余極限。
方針：局所化に沿う全余錐制限の同値性で元の密度全余錐を移す。
規約：終点や元の図式の全高次を取り替えない。
使われ方：次数への左 Kan 延長と余極限の合成による幾何学的実現。 -/
lemma presheafBarInput_colimitPresentation :
    ∃ c : JoinCocone (presheafBarInputDiagram F),
      IsColimitCone c ∧ c.vertex = functorVertex F := by
  let j := (SSet.uliftFunctor.{u + 1, u}).map
    (transportSimplexFirstVertexMap (smallRightUnstraightening F))
  have hj : IsFullyFaithful ((pre j).app (PresheafInfinity C)) :=
    localization_pre_isFullyFaithful
      (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1}
        (smallRightUnstraightening F)) _
  let c := (presheafDensityCocone F).restrict j
  have hc := (isColimitCone_iff_restrict_of_fullyFaithful_pre j hj
    (presheafDensityCocone F)).mp (presheafDensityCocone_isColimit F)
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso (presheafBarIndexNerveIso F)
  let d := c.restrict e.hom
  have hd := (isColimitCone_iff_restrict_of_fullyFaithful_pre e.hom
    ((isPrecompositionEquivalence_of_iso e) (PresheafInfinity C)).isFullyFaithful c).mp hc
  have hdiag : e.hom ≫ (j ≫ presheafElementsYonedaDiagram F) = presheafBarInputDiagram F := by
    dsimp only [e, j, presheafBarInputDiagram, Functor.mapIso_hom,
      presheafBarIndexNerveIso]
    rw [Functor.map_comp, Category.assoc]
  let t : JoinCocone (presheafBarInputDiagram F) := ⟨d.val, d.property.trans hdiag⟩
  refine ⟨t, (F2.isColimitCone_iff_of_cocone_val_eq d t rfl).mp hd, ?_⟩
  change d.vertex = functorVertex F
  rw [JoinCocone.vertex_restrict, JoinCocone.vertex_restrict]
  exact presheafDensityCocone_vertex F

end SerrePositivity.InfinityCategories.HomotopyLimits
