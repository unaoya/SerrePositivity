module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialPrismRetraction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRootVerticalFamily

/-!
概要：元の根辺円柱の全族を、始点固定の同じ定値な時間図式へ制限する。
方針：空間の初期端の包含を点の円柱の射影と照合し、同じ余錐族を制限する。
規約：元の円柱と全パラメータを保持する。使われ方：二時刻の初期 Hom の作用の比較。
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
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalHomotopy hp p c hc dB dC
local notation "v" => Equiv.symm (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (f ≫ (i ≫ p)))) c
local notation "r" => stdSimplex.σ (0 : Fin 1)
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の根辺円柱の初期側の時間辺は、同じ c の定値図式である。 -/
lemma specifiedCoconeRootVerticalInitial_diagram :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u + 1}) ≫ (H).h = r ≫ v := by
  let l := lift (r : (Δ[1] : SSet.{u + 1}) ⟶ Δ[0]) (𝟙 Δ[1])
  calc
    _ = (l ≫ (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1}))) ≫ (H).h := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialPrismRetraction_vertex]
    _ = l ≫ ((stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ (H).h) :=
      Category.assoc _ _ _
    _ = l ≫ (fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ v) :=
      congrArg (fun m ↦ l ≫ m) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalHomotopy_initial hp p c hc dB dC)
    _ = _ := by rw [← Category.assoc l (fst (Δ[0] : SSet.{u + 1}) Δ[1]) v, lift_fst]

/-- 全 Hom 族を同じ c の定値な時間図式へ制限した、元の実際の全族。 -/
def specifiedCoconeRootVerticalInitialFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (r ≫ v) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (H).h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1])
      (specifiedCoconeRootVerticalInitial_diagram hp p c hc dB dC)

/-- 初期端へ制限しても、可変終点は元の同じ左三角形の全族である。 -/
lemma specifiedCoconeRootVerticalInitialFamily_projection :
    specifiedCoconeRootVerticalInitialFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ v) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC) := by
  rw [specifiedCoconeRootVerticalInitialFamily, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalFamily_projection]

/-- 定値な時間図式上の同じ全族も、底の終点 y を厳密に保つ。 -/
lemma specifiedCoconeRootVerticalInitialFamily_fixed :
    (specifiedCoconeRootVerticalInitialFamily hp p c hc dB dC y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ v)) ≫ q = SSet.const y := by
  rw [specifiedCoconeRootVerticalInitialFamily_projection,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily_fixed]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
