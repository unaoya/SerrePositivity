module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowRealizedAugmentationWeak
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FixedQuillenFrameInvariance

/-!
概要：指定自由frameの増大射は、fibrant標的への実Hom上でホモトピー同値。
方針：既存の固定Quillen類によるframe比較に、同じ増大射の全次数の弱同値を入れる。
使われ方：HTT 4.2.4.4、RR02(a)のBK比較射の弱同値性。
規約：SSetのモデル構造の存在は仮定しない。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape

/-- 元の増大射による前合成そのものが、同じ指定fibrant標的でホモトピー同値。 -/
lemma strictDiagramFreeArrowAugmentationHom_equivalence (X Y : StrictComplexDiagram A d) :
    IsSimplicialHomotopyEquivalence
      ((cosimplicialHomMap (strictDiagramFreeArrowRealizedAugmentation A d X)).app
        (strictDiagramFibrantTarget A d Y)) := by
  haveI := strictDiagramFibrantTarget_isFibrant A d Y
  exact frameHomMap_homotopyEquivalence (strictDiagramFreeArrowRealizedAugmentation A d X)
    (strictDiagramFreeArrowRealizedFrame_cofibrant A d X)
    (strictDiagramSourceFrame A d X).cofibrant
    (strictDiagramFreeArrowRealizedFrame_homotopicallyConstant A d X)
    (strictDiagramSourceFrame A d X).homotopicallyConstant
    (strictDiagramFreeArrowRealizedAugmentation_weak A d X) _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
