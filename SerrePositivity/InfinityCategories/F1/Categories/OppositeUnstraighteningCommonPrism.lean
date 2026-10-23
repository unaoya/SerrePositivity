module

public import SerrePositivity.InfinityCategories.F1.Categories.OppositeUnstraighteningHomPrism

/-!
概要：全 Hom の普遍 prism を、元の反転比較と厳密に照合した同じ共通 weighted 係数へ制限する。
方針：始域のパラメーター射で引き戻し、始点では既存の全単体の比較等式を使う。
規約：変換の Hom パラメーターは固定せず、全体を保持する。
使われ方：weighted 作用から構成するもう一つの prism と同じ両境界で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

variable {I : Type u} [SmallCategory I] (F G : KanDiagramObject I)

/-- 同じ全 Hom の prism を、同じ共通 weighted 始域へ制限した実際の持ち上げ。 -/
def oppositeUnstraighteningCommonPrism :=
  (((Δ[1] : SSet.{u + 1}) ◁ strictKanCommonWeightedParameterMap F.val) ▷
    (SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
    oppositeUnstraighteningHomPrism F G

/-- 共通係数上の始点は、元の共通 cone 比較と同じ左脚の pointed 成分そのもの。 -/
lemma oppositeUnstraighteningCommonPrism_zero :
    (prismEndpoint 0 ((SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve
      (simplicialHomDiagram (strictKanCommonDiagram F.val) edgewisePointKanObject ⋙
        SSet.opFunctor))) ▷ (SSet.uliftFunctor.{u + 1, u}).obj
        (edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
      oppositeUnstraighteningCommonPrism F G =
    fst _ _ ≫ weightedCoherentConeComparison (strictKanCommonDiagram F.val) edgewisePointKanObject ≫
      strictKanCommonUnstraighteningOpposite F.val ≫
      pullback.fst pointedSpaceProjection
        (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor)) := by
  rw [oppositeUnstraighteningCommonPrism, ← Category.assoc,
    ← comp_whiskerRight, prismEndpoint_naturality, comp_whiskerRight, Category.assoc,
    oppositeUnstraighteningHomPrism_zero, whiskerRight_fst_assoc,
    ← Category.assoc (strictKanCommonWeightedParameterMap F.val),
    strictKanCommonWeightedParameterMap_compare, Category.assoc]

/-- 共通係数上の終点は、元の右端の全相対射の族を同じパラメーター射で制限したもの。 -/
lemma oppositeUnstraighteningCommonPrism_one :
    (prismEndpoint 1 ((SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve
      (simplicialHomDiagram (strictKanCommonDiagram F.val) edgewisePointKanObject ⋙
        SSet.opFunctor))) ▷ (SSet.uliftFunctor.{u + 1, u}).obj
        (edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
      oppositeUnstraighteningCommonPrism F G =
    (strictKanCommonWeightedParameterMap F.val ▷
      (SSet.uliftFunctor.{u + 1, u}).obj
        (edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
      relativeFunctorUncurry (oppositeUnstraighteningHomRight F G) ≫
      pullback.fst pointedSpaceProjection
        (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) := by
  rw [oppositeUnstraighteningCommonPrism, ← Category.assoc,
    ← comp_whiskerRight, prismEndpoint_naturality, comp_whiskerRight, Category.assoc,
    oppositeUnstraighteningHomPrism_one]

/-- 共通係数上でも底は同じ反転変換の全区間族であり、元の共通 weighted 射影を通す。 -/
lemma oppositeUnstraighteningCommonPrism_projection :
    oppositeUnstraighteningCommonPrism F G ≫ pointedSpaceProjection =
    ((Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
      (simplicialHomDiagram (strictKanCommonDiagram F.val) edgewisePointKanObject ⋙
        SSet.opFunctor))) ▷ (SSet.uliftFunctor.{u + 1, u}).obj
        (edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
    functorParameterizedPrism (intervalMappingUncurry (kanDiagramOppositeHomInterval F G)) := by
  rw [oppositeUnstraighteningCommonPrism, Category.assoc,
    oppositeUnstraighteningHomPrism_projection, oppositeUnstraighteningHomBase,
    ← Category.assoc]
  congr 1
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, x⟩, t⟩
  exact congrArg (fun z => ((a, z), t))
    (congrArg (fun k => k.app n x) (strictKanCommonWeightedParameterMap_projection F.val))

end SerrePositivity.InfinityCategories
