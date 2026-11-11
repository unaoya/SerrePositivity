module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialDiagramHomotopyConstant
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootTotalInitial

/-!
概要：時間零の端面から元の左三角形への比較を、同じ初期 Hom 空間へ移す。
方針：同じ長辺と初期頂点で円柱を fiber に戻し、元の三角形族へ端点を同定する。
規約：raw な制限・評価・底を保持する。使われ方：三比較の同じ固定終点空間での合成。
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
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "v" => Equiv.symm (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (f ≫ (i ≫ p)))) c
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "hW" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootClosingLeft_initial hp p c hc dB dC
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalStartFamily hp p c hc dB dC y
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y
local notation "ha" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalStartFamily_fixed hp p c hc dB dC y
local notation "hb" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily_fixed hp p c hc dB dC y
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y
local notation "hK" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalStartComparison_fixed hp p c hc dB dC y
local notation "G" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamilyHomotopy q c W (stdSimplex.δ (1 : Fin 2))
  hW y a b ha hb K hK
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の時間零の端面の、同じ固定終点の初期 Hom 族。 -/
def specifiedCoconeRootStartInitialFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q c y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c W (stdSimplex.δ (1 : Fin 2)) hW y a ha

/-- 元の左三角形の初期 Hom 族へ至る、同じ時間零の比較円柱。 -/
def specifiedCoconeRootStartInitialHomotopy : SSet.Homotopy
    (specifiedCoconeRootStartInitialFamily hp p c hc dB dC y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y) where
  h := (G).h
  h₀ := by
    exact (G).h₀
  h₁ := by
    exact (G).h₁.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily_initial hp p c hc dB dC y)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 包含後は元の左比較円柱の同じ初期頂点制限である。 -/
lemma specifiedCoconeRootStartInitialHomotopy_ι :
    (specifiedCoconeRootStartInitialHomotopy hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (v) ≫ q) y =
      (K).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction W (stdSimplex.δ (1 : Fin 2)) hW :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamilyHomotopy_ι q c W (stdSimplex.δ (1 : Fin 2))
    hW y a b ha hb K hK

/-- 元の左三角形の可変終点評価を全時刻固定する。 -/
lemma specifiedCoconeRootStartInitialHomotopy_evaluation :
    (specifiedCoconeRootStartInitialHomotopy hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y =
      fst T Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y := by
  have he : (K).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W = fst T Δ[1] ≫ b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection] using
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalStartComparison_projection hp p c hc dB dC y)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamilyHomotopy_evaluation_constant q c W
    (stdSimplex.δ (1 : Fin 2)) hW y a b ha hb K hK he
  exact h.trans (congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily_initial hp p c hc dB dC y))

/-- 元の左三角形の初期 Hom の底も、全時刻固定する。 -/
lemma specifiedCoconeRootStartInitialHomotopy_base :
    (specifiedCoconeRootStartInitialHomotopy hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y =
      fst T Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamilyHomotopy_base_constant q c W (stdSimplex.δ (1 : Fin 2))
    hW y a b ha hb K hK (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalStartComparison_base hp p c hc dB dC y)
  exact h.trans (congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily_initial hp p c hc dB dC y))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
