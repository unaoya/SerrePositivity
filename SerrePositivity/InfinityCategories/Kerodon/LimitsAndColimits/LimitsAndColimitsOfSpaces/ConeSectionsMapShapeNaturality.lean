module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConstantSourceMapShapeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeTransformationShapeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSectionsMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：元の錐の切断写像は、実切断の形状制限と全 fiber 上で可換。
方針：全変換の比較を同じ錐の標準変換で評価し、元の切断写像の頂点を回収する。
規約：指定 fiber 内の各点でなく、fiber 全体からの写像の同型である。
使われ方：G8 の元の指定極限比較と形状制限の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 同じ形状へ制限した錐の切断写像は、元の全切断写像の実際の制限と同型。 -/
def coneSectionsMapAt_shapeIso {B K : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B)
    (c : JoinCone F) (d : JoinCone (i ≫ F))
    (hd : d.val = joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ c.val)
    (z : SpaceInfinity.{u} _⦋0⦌) (hc : c.vertex = z) (hz : d.vertex = z) :
    FunctorIso (coneSectionsMapAt c z hc ≫ unstraighteningSectionsRestriction F i)
      (coneSectionsMapAt d z hz) := by
  letI : KanComplex (simplicialSections (leftUnstraighteningProjection (i ≫ F))) :=
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex _
  have h := (coherentConstantSourceMap_shapeIso F i z).app
    (coneTransformationPointAt c z hc)
  change VertexIso
    (((ihom _).map (unstraighteningSectionsRestriction F i)).app _
      ((coherentConstantSourceMap F z).app _ (coneTransformationPointAt c z hc)))
    ((coherentConstantSourceMap (i ≫ F) z).app _
      ((sourceConstantShapeRestriction i F z).app _ (coneTransformationPointAt c z hc))) at h
  rw [coneTransformationPointAt_shapeRestriction i F c d hd z hc hz,
    ← coneSectionsMapAt_vertex, ← coneSectionsMapAt_vertex] at h
  have hvcomp : ((ihom _).map (unstraighteningSectionsRestriction F i)).app _
      (functorVertex (coneSectionsMapAt c z hc)) =
      functorVertex (coneSectionsMapAt c z hc ≫ unstraighteningSectionsRestriction F i) := by
    unfold functorVertex
    rw [← curry'_ihom_map]
    rfl
  rw [hvcomp] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
