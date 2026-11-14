module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SourceFixedTriangleHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRightCorrectionFace
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionHomotopyEdge

/-!
概要：右修正面から、修正前後の同じ共通長辺の底・始点固定円柱を構成する。
方針：指定修正面を既存の比較正方形で引き戻し、固定延長空間の実際の辺にする。
規約：終点は元の指定修正辺をたどる。使われ方：共通長辺空間での右比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "β" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionFace hp p c hc dB dC
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "U" => stdSimplex.δ (1 : Fin 3) ≫
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge ≫ T
local notation "v" => SSet.yonedaEquiv.symm c
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p)
local notation "κ" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC

/-- 修正前の長辺から修正後の長辺へ向かう、同じ指定面による実際の円柱。 -/
def specifiedCoconeRightCorrectionHomotopy : SSet.Homotopy U V := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sourceFixedTriangleHomotopy Q
  refine
    { h := H.h
      h₀ := H.h₀.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionFace_first hp p c hc dB dC)
      h₁ := H.h₁.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionFace_long hp p c hc dB dC)
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- 円柱は元の修正面の正方形への引き戻しそのものである。 -/
lemma specifiedCoconeRightCorrectionHomotopy_raw :
    (specifiedCoconeRightCorrectionHomotopy hp p c hc dB dC).h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape ≫ Q := rfl

/-- 元の共通長辺の底を全時刻で固定する。 -/
lemma specifiedCoconeRightCorrectionHomotopy_projection :
    (specifiedCoconeRightCorrectionHomotopy hp p c hc dB dC).h ≫ q =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ β :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sourceFixedTriangleHomotopy_projection Q q β
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionFace_projection hp p c hc dB dC)

/-- 始点は元の共通余錐の同じ点で全時刻に固定する。 -/
lemma specifiedCoconeRightCorrectionHomotopy_initial :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (specifiedCoconeRightCorrectionHomotopy hp p c hc dB dC).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ v :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sourceFixedTriangleHomotopy_initial Q v
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionFace_initial hp p c hc dB dC)

/-- 終点の時間方向の辺は、元の指定修正辺の同じ共通制限である。 -/
lemma specifiedCoconeRightCorrectionHomotopy_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u + 1}) ≫
        (specifiedCoconeRightCorrectionHomotopy hp p c hc dB dC).h =
      SSet.yonedaEquiv.symm (κ).edge ≫ r :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sourceFixedTriangleHomotopy_target Q).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionFace_second hp p c hc dB dC)

/-- 修正前の長辺は同じ根辺の上にある。 -/
lemma specifiedCoconeRightCorrectionHomotopy_source_projection : U ≫ q = β :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_rootProjection hp p c hc dB dC

/-- 修正後の長辺も同じ根辺の上にある。 -/
lemma specifiedCoconeRightCorrectionHomotopy_target_projection : V ≫ q = β :=
  (Category.assoc _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedTetrahedron_rootEdge hp p c hc dB dC)

/-- 修正前の長辺の始点は元の共通余錐。 -/
lemma specifiedCoconeRightCorrectionHomotopy_source_initial :
    stdSimplex.δ (1 : Fin 2) ≫ U = v :=
  (Category.assoc _ _ _).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)

/-- 修正後の長辺の始点も元の同じ共通余錐。 -/
lemma specifiedCoconeRightCorrectionHomotopy_target_initial :
    stdSimplex.δ (1 : Fin 2) ≫ V = v :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ T) _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge_source).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_initialVertex hp p c hc dB dC))

/-- 同じ根辺を被覆する固定初期図式の底の整合性。 -/
lemma specifiedCoconeRightRootExtension_initial_base :
    v ≫ q = stdSimplex.δ (1 : Fin 2) ≫ β :=
  (congrArg (fun z ↦ z ≫ q)
    (specifiedCoconeRightCorrectionHomotopy_source_initial hp p c hc dB dC).symm).trans
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ stdSimplex.δ (1 : Fin 2) ≫ z)
        (specifiedCoconeRightCorrectionHomotopy_source_projection hp p c hc dB dC)))

local notation "hv" => specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC

/-- 元の根辺と共通余錐を固定する、同じ長辺の延長空間。 -/
def specifiedCoconeRightRootExtensionSpace : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace q β (stdSimplex.δ (1 : Fin 2)) v hv

/-- ここでの比較を含む延長空間は可縮な Kan 複体である。 -/
lemma specifiedCoconeRightRootExtensionSpace_isContractibleKan :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (specifiedCoconeRightRootExtensionSpace hp p c hc dB dC) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan q β (stdSimplex.δ (1 : Fin 2))
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeInitial_leftAnodyne v hv

/-- 同じ指定円柱を、同じ根辺の固定延長空間の実際の辺として保持する。 -/
def specifiedCoconeRightCorrectionExtensionEdge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge q β (stdSimplex.δ (1 : Fin 2)) v hv
    (specifiedCoconeRightCorrectionHomotopy_source_projection hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy_source_initial hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy_initial hp p c hc dB dC)

/-- 延長空間の辺を展開しても、元の修正面による同じ円柱を厳密に回収する。 -/
lemma specifiedCoconeRightCorrectionExtensionEdge_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm
      (specifiedCoconeRightCorrectionExtensionEdge hp p c hc dB dC).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q β (stdSimplex.δ (1 : Fin 2)) v hv) =
      (specifiedCoconeRightCorrectionHomotopy hp p c hc dB dC).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge_uncurry _ _ _ _ _ _ _ _ _ _ _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
