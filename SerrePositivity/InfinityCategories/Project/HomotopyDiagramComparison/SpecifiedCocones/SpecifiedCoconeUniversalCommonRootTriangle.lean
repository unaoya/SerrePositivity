module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeUniversalCommonRootComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：元の根辺比較と左右の共通普遍根辺比較を、その同じ三辺の実際の三角形へ束ねる。
方針：元の三円柱の類の合成等式を、関手単体集合の合成二単体へ戻して uncurry する。
規約：三つの元の代表を保つ。使われ方：共通 end における根辺比較の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
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
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y
local notation "root" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "rt" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge_target hp p c hc dB dC
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y
local notation "Q" => Iso.inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) d y)
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalCommonRootFamily hp p c hc dB dC y
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootFamilyComparison hp p c hc dB dC y

local notation "HL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalCommonRootComparison hp p c hc dB dC y
local notation "HR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalCommonRootComparison hp p c hc dB dC y

/-- 元の根辺比較と右・左の元の比較を、その同じ三辺に持つ合成二単体。 -/
def specifiedCoconeUniversalCommonRootTriangle : SSet.Truncated.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy G) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy HR)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy HL) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalCommonRoot_homMk_comp hp p c hc dB dC y)).some

/-- 同じ合成二単体の全パラメータの族。三辺の代表は選び直さない。 -/
def specifiedCoconeUniversalCommonRootTriangleFamily :
    T ⊗ (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace root y :=
  uncurry (SSet.yonedaEquiv.symm
    (specifiedCoconeUniversalCommonRootTriangle hp p c hc dB dC y).simplex)

/-- 三角形の第一辺は、元の左右の根辺族比較の raw な円柱そのもの。 -/
lemma specifiedCoconeUniversalCommonRootTriangle_first :
    (T ◁ stdSimplex.δ (2 : Fin 3)) ≫
        specifiedCoconeUniversalCommonRootTriangleFamily hp p c hc dB dC y = (G).h := by
  rw [specifiedCoconeUniversalCommonRootTriangleFamily, ← uncurry_natural_left]
  have h := (specifiedCoconeUniversalCommonRootTriangle hp p c hc dB dC y).d₂
  change ((ihom T).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace root y)).δ 2 _ =
    SSet.yonedaEquiv (curry (G).h) at h
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, h, Equiv.symm_apply_apply, uncurry_curry]

/-- 三角形の第二辺は、右の同じ全図式比較の根辺面の raw な円柱そのもの。 -/
lemma specifiedCoconeUniversalCommonRootTriangle_second :
    (T ◁ stdSimplex.δ (0 : Fin 3)) ≫
        specifiedCoconeUniversalCommonRootTriangleFamily hp p c hc dB dC y = (HR).h := by
  rw [specifiedCoconeUniversalCommonRootTriangleFamily, ← uncurry_natural_left]
  have h := (specifiedCoconeUniversalCommonRootTriangle hp p c hc dB dC y).d₀
  change ((ihom T).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace root y)).δ 0 _ =
    SSet.yonedaEquiv (curry (HR).h) at h
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, h, Equiv.symm_apply_apply, uncurry_curry]

/-- 三角形の対角辺は、左の同じ全図式比較の根辺面の raw な円柱そのもの。 -/
lemma specifiedCoconeUniversalCommonRootTriangle_diagonal :
    (T ◁ stdSimplex.δ (1 : Fin 3)) ≫
        specifiedCoconeUniversalCommonRootTriangleFamily hp p c hc dB dC y = (HL).h := by
  rw [specifiedCoconeUniversalCommonRootTriangleFamily, ← uncurry_natural_left]
  have h := (specifiedCoconeUniversalCommonRootTriangle hp p c hc dB dC y).d₁
  change ((ihom T).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace root y)).δ 1 _ =
    SSet.yonedaEquiv (curry (HL).h) at h
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, h, Equiv.symm_apply_apply, uncurry_curry]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
