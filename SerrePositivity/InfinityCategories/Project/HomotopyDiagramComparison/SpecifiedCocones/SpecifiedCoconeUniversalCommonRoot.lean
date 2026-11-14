module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.NativeSpanUniversalRootShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomDiagramRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeNativeUniversalFaces

/-!
概要：左右の native 普遍全図式族の根辺制限を、同じ全余錐族の同じ脚の族へ戻す。
方針：元の join 形状の厳密な一致と、普遍全族の二段制限の式を使う。
規約：共通パラメータと選択済みの全 Hom 族を保持。使われ方：元の左右の根辺比較の合流。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "s" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "root" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "σL" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "σR" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
  (SSet.Edge.CompStruct.simplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "rfL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagram_root hp p c hc dB dC
local notation "rfR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagram_root hp p c hc dB dC
local notation "U" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalNativeParameter hp p c hc dB dC y
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalNativeFamily hp p c hc dB dC y
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalNativeFamily hp p c hc dB dC y

/-- 同じ native 全余錐の共通脚の形状は、元の共通根辺図式を厳密に切り出す。 -/
lemma specifiedCoconeUniversalRootShape_diagram :
    (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftTriangleShape) ≫ Subtype.val s = root :=
  (Category.assoc _ _ _).trans
    ((congrArg (stdSimplex.δ (1 : Fin 3) ≫ ·)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftHomDiagram_shape hp p c hc dB dC)).trans rfL)

/-- 同じ選択済み全 Hom 族を、左右で共通する同じ実際の脚へ制限した族。 -/
def specifiedCoconeUniversalCommonRootFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace root y :=
  U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily s
    (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftTriangleShape) root
    (specifiedCoconeUniversalRootShape_diagram hp p c hc dB dC) y

/-- 左の普遍全図式族の根辺は、同じ全余錐から得た共通脚の族そのもの。 -/
lemma specifiedCoconeLeftUniversalNativeFamily_root :
    L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σL (stdSimplex.δ (1 : Fin 3)) rfL y =
      specifiedCoconeUniversalCommonRootFamily hp p c hc dB dC y := by
  exact (Category.assoc U (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftUniversalHomDiagramFamily hp p c hc dB dC y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σL (stdSimplex.δ (1 : Fin 3)) rfL y)).trans
      (congrArg (U ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily_restrict s
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftTriangleShape σL (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftHomDiagram_shape hp p c hc dB dC)
        (stdSimplex.δ (1 : Fin 3)) root rfL
        (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftTriangleShape) rfl
        (specifiedCoconeUniversalRootShape_diagram hp p c hc dB dC) y))

/-- 右の退化四面体の辺03も、同じ全余錐から得た同じ共通脚の族そのもの。 -/
lemma specifiedCoconeRightUniversalNativeFamily_root :
    R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σR _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge rfR y =
      specifiedCoconeUniversalCommonRootFamily hp p c hc dB dC y := by
  exact (Category.assoc U (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanRightUniversalHomDiagramFamily hp p c hc dB dC y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σR _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge rfR y)).trans
      (congrArg (U ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily_restrict s
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanRightTetrahedronShape σR (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanRightHomDiagram_shape hp p c hc dB dC)
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge root rfR
        (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftTriangleShape)
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanUniversalRootShape_eq.symm
        (specifiedCoconeUniversalRootShape_diagram hp p c hc dB dC) y))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
