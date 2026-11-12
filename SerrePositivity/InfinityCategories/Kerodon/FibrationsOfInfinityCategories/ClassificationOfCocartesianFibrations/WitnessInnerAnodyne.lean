module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftFibrationInnerAnodynePullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement

/-!
概要：inner anodyne な底の制限は表現空間の trivial Kan fibration。
方針：逆像の前合成同値、全頂点の被覆、四角形の持ち上げを組み合わせる。
規約：モデル構造の instance 仮定は使わない。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK） (2)、表現の境界固定延長。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：inner anodyne 射は全ての頂点を被覆する。
方針：像の頂点が張る全部分複体の inner fibration に対して恒等射を持ち上げる。
規約：始域も終域も quasicategory でなくてよい。
使われ方：inner anodyne 制限から表現条件を反映する。 -/
lemma innerAnodyne_vertex_surjective {A B : SSet.{u}} (g : A ⟶ B)
    (hg : innerAnodyneExtensions g) : Function.Surjective (g.app (Opposite.op ⦋0⦌)) := by
  let P : B _⦋0⦌ → Prop := Set.range (g.app (Opposite.op ⦋0⦌))
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P g (fun x ↦ ⟨x, rfl⟩)
  let q := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B P).ι
  have : HasLiftingProperty g q := hg q (InnerFibration.mem (q := q))
  let sq : CommSq a g q (𝟙 B) := ⟨by
    rw [Category.comp_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _⟩
  intro b
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (sq.lift.app (Opposite.op ⦋0⦌) b)
  have he := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) b) sq.fac_right
  change (sq.lift.app (Opposite.op ⦋0⦌) b).val = b at he
  change P _ at hb
  rw [he] at hb
  exact hb

/-- 概要：inner anodyne な底への四角形の制限は全ての単射を持ち上げる。
方針：left fibration に沿う逆像の前合成同値を相対内部 Hom の判定に入れる。
規約：底と全空間の quasicategory 性は不要。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK） (2)、周囲の四角形の充填。 -/
lemma transportSquareRestriction_trivialKanFibration_of_innerAnodyne
    {E B D : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B)
    (hg : innerAnodyneExtensions g) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g) := by
  have : Mono g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.mono_of_innerAnodyne g hg
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionLifting.transportSquareRestriction_trivialKanFibration_of_precompositionEquivalences p g
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne g hg)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibration_pullback_innerAnodyne_isPrecompositionEquivalence p g hg)

/-- 概要：inner anodyne な底への表現空間の制限は全ての単射を持ち上げる。
方針：周囲の四角形の充填を全頂点の被覆で表現空間へ制限する。
規約：存在や一意性を追加の公理として要求しない。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK） (2) の空間値版。 -/
lemma transportWitnessRestriction_trivialKanFibration_of_innerAnodyne
    {E B D : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B)
    (hg : innerAnodyneExtensions g) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionLifting.transportWitnessRestriction_trivialKanFibration_of_square p g
    (innerAnodyne_vertex_surjective g hg)
    (transportSquareRestriction_trivialKanFibration_of_innerAnodyne p g hg)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
