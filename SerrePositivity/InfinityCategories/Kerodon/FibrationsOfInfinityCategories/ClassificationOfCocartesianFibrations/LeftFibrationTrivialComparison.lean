module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：全空間の同値でもある left fibration の全境界持ち上げ性。
方針：本質的全射性を辺の持ち上げで頂点の全射性へ強め、充満忠実な inner fibration の判定を使う。
規約：モデル構造の弱同値は使わない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対関手空間の前合成比較の厳密化。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：本質的全射な left fibration は頂点上で全射。
方針：像の頂点から指定頂点への同型を辺で表し、その辺を指定した始点から持ち上げる。
規約：標的だけを quasicategory とする。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対比較を全境界持ち上げへ強める前段階。 -/
lemma leftFibration_vertex_surjective_of_essentiallySurjective
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective p) : Function.Surjective (p.app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨x, ⟨e⟩⟩ := hp y
  obtain ⟨a, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (p.app (Opposite.op ⦋0⦌) x) y e.hom
  obtain ⟨F, _, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftEdge_source p x a
  refine ⟨SSet.yonedaEquiv (stdSimplex.δ 0 ≫ F), ?_⟩
  rw [← SSet.yonedaEquiv_comp, Category.assoc, hF,
    stdSimplex.yonedaEquiv_δ_comp]
  exact (congrArg (B.δ 0)
    (SSet.yonedaEquiv.apply_symm_apply (a.edge : B _⦋1⦌))).trans a.tgt_eq

/-- 概要：quasicategory の同値でもある left fibration は trivial Kan fibration。
方針：同値から充満忠実性を取り出し、本質的全射性から頂点上の全射性を示す。
規約：結論は全ての単射の右持ち上げ性。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、底を固定した前合成の比較の厳密な延長。 -/
lemma trivialKanFibration_of_leftFibration_of_isQCatEquivalence
    {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p :=
  hp.isFullyFaithful.trivialKanFibration_of_surjective
    (leftFibration_vertex_surjective_of_essentiallySurjective p hp.choose.isEssentiallySurjective)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "3.1.1.5" (partial := direction) "仮定：準圏間の左ファイブレーションが準圏同値である（Lean は ψ という指定を外し、左ファイブレーション性を仮定）。結論：自明 Kan ファイブレーションになる（ψ に関する同値判定の一方向に一致）。ψ の左ファイブレーション性は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trivialKanFibration_of_leftFibration_of_isQCatEquivalence
attribute [cite HTT "2.1.3.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibration_vertex_surjective_of_essentiallySurjective
attribute [cite HTT "4.3.1.2" (partial := component) "仮定：内ファイブレーションと右結合上の余錐（Lean が強い：圏同値の判定では始域と終域が準圏）。結論：同じ相対コスライス比較の自明 Kan 性と準圏同値性が同値（Joyal 模型でのホモトピー引き戻しの同定は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trivialKanFibration_of_leftFibration_of_isQCatEquivalence
