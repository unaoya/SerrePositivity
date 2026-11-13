module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionBaseIso
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRightCorrectionHomotopy

/-!
概要：左右の三角形の長辺制限を、元の共通根辺上の一つの延長空間へ移す。
方針：元の三角形の射影による底の等式を使い、実際の長辺を全族で保持する。
規約：右の実際の像は指定修正円柱の始点そのもの。使われ方：左右の比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg

variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "β" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "v" => SSet.yonedaEquiv.symm c
local notation "k" => stdSimplex.δ (1 : Fin 3)
local notation "a" => stdSimplex.δ (1 : Fin 2)
local notation "σL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "σR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "βL" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σL)
local notation "βR" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σR)
local notation "hvL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtension_initial_base hp p c hc dB dC
local notation "hvR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtension_initial_base hp p c hc dB dC
local notation "hv" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace hp p c hc dB dC

/-- 左二単体の底の長辺は、同じ元の根辺そのもの。 -/
lemma specifiedCoconeLeftTriangleLongBase : k ≫ βL = β :=
  ((congrArg (fun z ↦ k ≫ z)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_projection hp p c hc dB dC)).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC))

/-- 右初面の底の長辺も、同じ元の根辺そのもの。 -/
lemma specifiedCoconeRightPrefixTriangleLongBase : k ≫ βR = β :=
  ((congrArg (fun z ↦ k ≫ z)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_rootProjection hp p c hc dB dC))

/-- 左三角形の長辺を、共通根辺の固定延長空間へ写す。 -/
def specifiedCoconeLeftCommonRootRestriction :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtensionSpace hp p c hc dB dC ⟶ S :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleLongRestriction hp p c hc dB dC ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso q (specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)
      a v ((hvL).trans (Category.assoc _ _ _)) hv).hom

/-- 右初面の長辺も、全く同じ共通根辺の固定延長空間へ写す。 -/
def specifiedCoconeRightPrefixCommonRootRestriction :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtensionSpace hp p c hc dB dC ⟶ S :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso q (specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)
      a v ((hvR).trans (Category.assoc _ _ _)) hv).hom

/-- 左の全パラメータ族も、元の同じ長辺の制限である。 -/
lemma specifiedCoconeLeftCommonRootRestriction_uncurry {T : SSet.{u + 1}}
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtensionSpace hp p c hc dB dC) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (t ≫ specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q β a v hv) =
      (k ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q βL (a ≫ k)
        v hvL) := by
  dsimp only [specifiedCoconeLeftCommonRootRestriction]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso_uncurry q (specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)
    a v ((hvL).trans (Category.assoc _ _ _)) hv
    (t ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleLongRestriction hp p c hc dB dC)
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
        ((t ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleLongRestriction hp p c hc dB dC) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q (k ≫ βL) a v
            ((hvL).trans (Category.assoc _ _ _))) := by
      simpa only [Category.assoc] using h
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_uncurry q βL k a v hvL t

/-- 右の全パラメータ族も、元の右初面の同じ長辺の制限である。 -/
lemma specifiedCoconeRightPrefixCommonRootRestriction_uncurry {T : SSet.{u + 1}}
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtensionSpace hp p c hc dB dC) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      (t ≫ specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q β a v hv) =
      (k ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q βR (a ≫ k)
        v hvR) := by
  dsimp only [specifiedCoconeRightPrefixCommonRootRestriction]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso_uncurry q
    (specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)
    a v ((hvR).trans (Category.assoc _ _ _)) hv
    (t ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC)
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
        ((t ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q (k ≫ βR) a v
            ((hvR).trans (Category.assoc _ _ _))) := by
      simpa only [Category.assoc] using h
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_uncurry q βR k a v hvR t

/-- 左の実際の頂点は、新しい持ち上げではなく元の左長辺そのもの。 -/
lemma specifiedCoconeLeftCommonRootRestriction_actual :
    (specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC).app _
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv q β a v hv
        ⟨k ≫ L, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC,
          (Category.assoc _ _ _).symm.trans
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtension_initial hp p c hc dB dC)⟩ := by
  have h := congrArg
    (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso q
      (specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)
      a v ((hvL).trans (Category.assoc _ _ _)) hv).hom.app _ z)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftActualTriangleExtensionVertex_long hp p c hc dB dC)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso_vertex q
    (specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)
    a v ((hvL).trans (Category.assoc _ _ _)) hv (k ≫ L)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ k ≫ z)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_projection hp p c hc dB dC)))
    ((Category.assoc _ _ _).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtension_initial hp p c hc dB dC)))

/-- 右の実際の頂点は、同じ指定修正円柱の始点である。 -/
lemma specifiedCoconeRightPrefixCommonRootRestriction_actual :
    (specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC).app _
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv q β a v hv
        ⟨k ≫ R, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_source_projection hp p c hc dB dC,
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_source_initial hp p c hc dB dC⟩ := by
  have h := congrArg
    (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso q
      (specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)
      a v ((hvR).trans (Category.assoc _ _ _)) hv).hom.app _ z)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixActualTriangleExtensionVertex_long hp p c hc dB dC)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso_vertex q
    (specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)
    a v ((hvR).trans (Category.assoc _ _ _)) hv (k ≫ R)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ k ≫ z)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)))
    ((Category.assoc _ _ _).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
