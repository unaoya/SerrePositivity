module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallWitnessContractible
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionFibration

/-!
概要：次数ごとに小さい全空間の表現を任意の単射の底に沿って厳密に延長する。
方針：両側の表現空間の可縮性と制限の Kan fibration 性を合わせる。
規約：分類図式と全空間の射をともに固定し、高次パラメーターも保つ。
使われ方：Kerodon §5.6.5（Tag 028U） の相対表現の全空間が小さい場合。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance smallExtensionPullbackSndLF {E B D : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：小さい全空間の表現空間の任意の単射への制限は trivial Kan fibration。
方針：単射への底変換の小ささと両空間の可縮性を制限の fibration 性に合わせる。
規約：底や部分複体の小ささは仮定しない。
使われ方：境界固定の表現の延長と全高次の比較。 -/
lemma smallTransportWitnessRestriction_trivialKanFibration {E B D : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (g : D ⟶ B) [Mono g] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g) := by
  have : ∀ m, Small.{u} ((pullback p g).obj m) :=
    fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small_of_mono p g m
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionFibration.transportWitnessRestriction_fibration p g
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trivialKanFibration_of_fibration_of_contractible _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportWitnessSpace_isContractibleKan p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportWitnessSpace_isContractibleKan (pullback.snd p g))

/-- 概要：単射の底への制限は表現の全ての族に同時に厳密な切断を持つ。
方針：trivial Kan fibration の全単射の持ち上げ性で切断を得る。
規約：頂点ごとの存在だけには弱めない。
使われ方：任意のパラメーターに自然な表現の延長。 -/
lemma smallTransportWitnessRestriction_exists_section {E B D : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) [Mono g] :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.snd p g) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p,
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g = 𝟙 _ := by
  have := smallTransportWitnessRestriction_trivialKanFibration p g
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section _

/-- 概要：指定した部分複体上の表現の厳密な延長空間は可縮 Kan。
方針：制限の指定頂点の fiber に全境界充填を移す。
規約：全空間の小ささ以外に表現の選択条件を加えない。
使われ方：境界固定延長の全高次の一意性。 -/
lemma smallTransportRepresentationExtension_isContractibleKan {E B D : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) [Mono g]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation (pullback.snd p g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R)) := by
  have := smallTransportWitnessRestriction_trivialKanFibration p g
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 概要：部分複体上の指定した表現は底と全空間の二射を保って厳密に延長できる。
方針：表現空間の制限の切断を表現の頂点の全単射で実際の表現へ戻す。
規約：次数ごとに小さい全空間を持つ任意の left fibration を扱う。
使われ方：Kerodon Theorem 5.6.5.12（Tag 0293） の小さい全空間の場合の相対存在。 -/
lemma exists_small_leftTransportRepresentation_extension {E B D : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) [Mono g]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation (pullback.snd p g)) :
    ∃ S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p, S.restrict g = R := by
  obtain ⟨s, hs⟩ := smallTransportWitnessRestriction_exists_section p g
  obtain ⟨S, hS⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex_surjective p (s.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R))
  refine ⟨S, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex_injective (pullback.snd p g)) ?_⟩
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction_vertex, hS]
  exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R)) hs

/-- 概要：部分パラメーター上の延長を固定して表現の族を同時に延長できる。
方針：底の制限の trivial Kan fibration の全単射の持ち上げ性を使う。
規約：底の制限とパラメーターの制限をともに厳密に保つ。
使われ方：高次パラメーター付きの境界固定延長。 -/
lemma exists_small_transportWitnessFamily_lift {E B D K L : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) [Mono g]
    (j : K ⟶ L) [Mono j] (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p)
    (b : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.snd p g))
    (sq : CommSq a j (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g) b) :
    ∃ F : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p, j ≫ F = a ∧ F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g = b := by
  have := smallTransportWitnessRestriction_trivialKanFibration p g
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g)) j inferInstance
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
