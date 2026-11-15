module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFrameEndpointIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramMixedFrameEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentPinchedTransport

/-!
概要：元の source frame Hom を同じ局所化の元の二端点の pinched Hom へ送る。
方針：同じ混合比較を宇宙移送し、right frame 比較と元の増大射の端点同型を合成する。
規約：局所化や frame を新しく選び直さない。
使われ方：RR01 の元の実評価への入力。HTT 4.2.4.4 の模型比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance sourcePinchedModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance sourcePinchedInitial : HasInitial (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial
local instance sourcePinchedCofibrant (X : StrictComplexDiagram A d) :
    IsCofibrant (strictDiagramSourceFrameZero A d X) :=
  strictDiagramSourceFrameZero_isCofibrant A d X
local instance sourcePinchedSourceKan (X Y : StrictComplexDiagram A d) :
    KanComplex (strictDiagramFrameMapping A d X Y) :=
  strictDiagramFrameMapping_kanComplex A d X Y
local instance sourcePinchedRightKan (X Y : StrictComplexDiagram A d) :
    KanComplex ((strictDiagramRightFrameMapping A d (strictDiagramSourceFrameZero A d X)).obj
      (strictDiagramFibrantTarget A d Y)) :=
  Project.ModelCategoryComparison.rightFrameHom_kanComplex (strictDiagramRightFrameFamily A d)
    (strictDiagramSourceFrameZero A d X) (strictDiagramFibrantTarget A d Y)

/-- 元の source frame Hom と指定局所化の元の二端点の比較。 -/
def strictDiagramSourceFramePinchedEquivalence (X Y : StrictComplexDiagram A d) :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (strictDiagramFrameMapping A d X Y))
      (pinchedHom
        ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))
        ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ Y))) :=
  (Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1}
    (strictDiagramSourceRightFrameEquivalence A d X Y).isQCatEquivalence).choose.trans
      ((strictDiagramRightFramePinchedEquivalence A d (strictDiagramSourceFrameZero A d X)
        (strictDiagramFibrantTarget A d Y)).trans
          (pinchedEndpointEquivalence (strictDiagramSourceFrameEndpointIso A d X)
            (strictDiagramFibrantTargetEndpointIso A d Y).symm))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
