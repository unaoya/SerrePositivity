module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramMixedFrame
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ExInfinityWeakMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-!
概要：同じ混合 Hom の Kan 置換を通じて元の二つの frame Hom を比較する。
方針：既存の両脚の反転性と Ex∞ の単位の弱同値性を合成する。
規約：混合 Hom 自体の Kan 性は仮定しない。元の両脚を保持する。
使われ方：RR01 の source frame から同じ right frame への接続。Hovey §5.4。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits _root_.HomotopicalAlgebra SSet
open SerrePositivity.SimplicialModel
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance mixedEquivModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance mixedEquivInitial : HasInitial (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial

/-- 左脚を同じ混合 Hom の Kan 置換へ送った元の射。 -/
def strictDiagramMixedKanLeft (X Y : StrictComplexDiagram A d) :
    strictDiagramFrameMapping A d X Y ⟶ exInfinity.obj (strictDiagramMixedFrame A d X Y) :=
  strictDiagramMixedFrameLeft A d X Y ≫ exInfinityUnit.app _

/-- 右脚を同じ混合 Hom の Kan 置換へ送った元の射。 -/
def strictDiagramMixedKanRight (X Y : StrictComplexDiagram A d) :
    (strictDiagramRightFrameMapping A d (strictDiagramSourceFrameZero A d X)).obj
      (strictDiagramFibrantTarget A d Y) ⟶ exInfinity.obj (strictDiagramMixedFrame A d X Y) :=
  strictDiagramMixedFrameRight A d X Y ≫ exInfinityUnit.app _

private lemma mixedUnitWeak (X Y : StrictComplexDiagram A d) :
    IsWeakHomotopyEquivalence (exInfinityUnit.app (strictDiagramMixedFrame A d X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (SSet.anodyneExtensions.Q_inverts _ (exInfinityUnit_anodyne _))

/-- 元の左脚は Kan 置換後も弱同値。 -/
lemma strictDiagramMixedKanLeft_weak (X Y : StrictComplexDiagram A d) :
    IsWeakHomotopyEquivalence (strictDiagramMixedKanLeft A d X Y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (strictDiagramMixedFrameLeft_isIso A d X Y)).comp (mixedUnitWeak A d X Y)

/-- 元の右脚は Kan 置換後も弱同値。 -/
lemma strictDiagramMixedKanRight_weak (X Y : StrictComplexDiagram A d) :
    IsWeakHomotopyEquivalence (strictDiagramMixedKanRight A d X Y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (strictDiagramMixedFrameRight_isIso A d X Y)).comp (mixedUnitWeak A d X Y)

local instance mixedEquivSourceKan (X Y : StrictComplexDiagram A d) :
    KanComplex (strictDiagramFrameMapping A d X Y) :=
  strictDiagramFrameMapping_kanComplex A d X Y

local instance mixedEquivZeroCofibrant (X : StrictComplexDiagram A d) :
    IsCofibrant (strictDiagramSourceFrameZero A d X) :=
  strictDiagramSourceFrameZero_isCofibrant A d X

local instance mixedEquivRightKan (X Y : StrictComplexDiagram A d) :
    KanComplex ((strictDiagramRightFrameMapping A d (strictDiagramSourceFrameZero A d X)).obj
      (strictDiagramFibrantTarget A d Y)) :=
  Project.ModelCategoryComparison.rightFrameHom_kanComplex
    (strictDiagramRightFrameFamily A d) (strictDiagramSourceFrameZero A d X)
      (strictDiagramFibrantTarget A d Y)

/-- 同じ二つの Kan Hom の比較。逆の選択はこの同じ右脚に固定する。 -/
def strictDiagramSourceRightFrameEquivalence (X Y : StrictComplexDiagram A d) :
    QCatEquivalence (strictDiagramFrameMapping A d X Y)
      ((strictDiagramRightFrameMapping A d (strictDiagramSourceFrameZero A d X)).obj
        (strictDiagramFibrantTarget A d Y)) := by
  exact (strictDiagramMixedKanLeft_weak A d X Y).isSimplicialHomotopyEquivalence.isQCatEquivalence.choose.trans
    (strictDiagramMixedKanRight_weak A d X Y).isSimplicialHomotopyEquivalence.isQCatEquivalence.choose.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
