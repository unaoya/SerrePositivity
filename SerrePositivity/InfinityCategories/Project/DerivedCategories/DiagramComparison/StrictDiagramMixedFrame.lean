module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramSourceFrameZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramRightFrameComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameComparison

/-!
概要：同じ source frame と right frame の共通の Hom 空間と両脚を固定する。
方針：元の二つの増大射を前後合成し、既存の両側 frame 比較を適用する。
規約：同じ元の frame を使い、anodyne 局所化の同型と実際の射を区別する。
使われ方：RR01 の source frame から指定評価への比較の入口。Hovey §5.4。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance mixedFrameModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance mixedFrameInitial : HasInitial (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial

/-- 元の source frame と、同じ fibrant target の right frame の混合 Hom。 -/
def strictDiagramMixedFrame (X Y : StrictComplexDiagram A d) : SSet.{u} :=
  (EInfinity.FrameHom.MixedFrame.mixedFunctor (strictDiagramSourceFrame A d X).obj).obj
    ((rightFrameDiagram (strictDiagramRightFrameFamily A d)).obj
      (strictDiagramFibrantTarget A d Y))

/-- 元の source frame Hom から、同じ right augmentation の後合成による射。 -/
def strictDiagramMixedFrameLeft (X Y : StrictComplexDiagram A d) :
    strictDiagramFrameMapping A d X Y ⟶ strictDiagramMixedFrame A d X Y :=
  EInfinity.FrameHom.MixedFrame.leftComparison (strictDiagramSourceFrame A d X).obj
    ((rightFrameUnit (strictDiagramRightFrameFamily A d)).app
      (strictDiagramFibrantTarget A d Y))

/-- 同じ零次の対象からの right Hom を、零次への増大射で前合成する。 -/
def strictDiagramMixedFrameRight (X Y : StrictComplexDiagram A d) :
    (strictDiagramRightFrameMapping A d (strictDiagramSourceFrameZero A d X)).obj
      (strictDiagramFibrantTarget A d Y) ⟶ strictDiagramMixedFrame A d X Y :=
  EInfinity.FrameHom.MixedFrame.rightComparison (strictDiagramSourceFrame A d X).obj
    (strictDiagramSourceFrameZeroAugmentation A d X)
    ((rightFrameDiagram (strictDiagramRightFrameFamily A d)).obj
      (strictDiagramFibrantTarget A d Y))

/-- 左脚は元の標的の fibrancy と既存の left frame 比較により局所化で可逆。 -/
lemma strictDiagramMixedFrameLeft_isIso (X Y : StrictComplexDiagram A d) :
    IsIso (AnodyneHomotopy.anodyneQ.map (strictDiagramMixedFrameLeft A d X Y)) := by
  haveI := strictDiagramFibrantTarget_isFibrant A d Y
  apply leftComparison_isIso (strictDiagramSourceFrame A d X).obj
    (strictDiagramSourceFrame A d X).cofibrant
    ((rightFrameUnit (strictDiagramRightFrameFamily A d)).app
      (strictDiagramFibrantTarget A d Y))
    (rightFrameDiagram_isFibrant (strictDiagramRightFrameFamily A d)
      (strictDiagramFibrantTarget A d Y))
  intro n
  exact (rightFrameUnit_trivialCofibration (strictDiagramRightFrameFamily A d)
    (strictDiagramFibrantTarget A d Y) n).2

/-- 右脚は同じ零次の cofibrancy と両 frame の Reedy 条件により局所化で可逆。 -/
lemma strictDiagramMixedFrameRight_isIso (X Y : StrictComplexDiagram A d) :
    IsIso (AnodyneHomotopy.anodyneQ.map (strictDiagramMixedFrameRight A d X Y)) := by
  haveI := strictDiagramSourceFrameZero_isCofibrant A d X
  apply rightComparison_isIso (strictDiagramSourceFrame A d X).obj
    (strictDiagramSourceFrame A d X).cofibrant
    (strictDiagramSourceFrameZeroAugmentation A d X)
    (strictDiagramSourceFrameZeroAugmentation_weak A d X)
  change SerrePositivity.Reedy.reedyLeft SerrePositivity.Reedy.simplex
    (cofibrations (StrictComplexDiagram A d)ᵒᵖ)
    (initial.to ((strictDiagramRightFrameFamily A d).obj.obj
      (op (strictDiagramFibrantTarget A d Y))))
  exact (strictDiagramRightFrameFamily A d).cofibrant _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
