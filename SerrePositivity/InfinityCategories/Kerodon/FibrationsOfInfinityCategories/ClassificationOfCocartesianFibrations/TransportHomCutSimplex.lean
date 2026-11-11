module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.RightIntervalCutSimplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportDiagramHomInterval
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHomPrism

/-!
概要：元の全 Hom 作用の prism の値を、切断後の同じ対角評価へ移す。
方針：二重 uncurry を共同実現へ戻し、標準区間比較の切断評価式を使う。
規約：追加パラメーターの全次数と、元の底の射列を保持する。
使われ方：実際の第一三角形の全高次を、固定成分の Hom 計算へ接続する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の右 Hom の切断単体を、同じ底の射列上で対角評価する。 -/
def cocartesianTransportHomCutSimplex {C : Type u} [Category.{u} C]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramDiagonalSimplex σ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex s t)

/-- 元の分類作用の実際の prism は、全単体で同じ切断した共同評価に一致する。 -/
lemma cocartesianTransportDiagramHomIntervalPrism_evaluate_cut
    {C : Type u} [Category.{u} C] (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramHomInterval F G)).app
        (Opposite.op ⦋n⦌) ((t, ULift.up σ), ULift.up s) =
      cocartesianTransportHomCutSimplex F G σ s (stdSimplex.objEquiv t).toOrderHom := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramHomInterval_uncurry]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism
  rw [uncurry_natural_left]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramRealization
  erw [uncurry_natural_left, uncurry_curry]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramDiagonalSimplex σ
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison F G)).app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _).app (Opposite.op ⦋n⦌) (t, ULift.up s))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.rightMappingSpacePrism_evaluate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pinchedHomUncurry_simplex]
  rfl

/-- 時刻零の対角評価の対象は、同じ始域図式の同じ底の値。 -/
lemma cocartesianTransportHomCutSimplex_obj_zero
    {C : Type u} [Category.{u} C] (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 0) :
    (cocartesianTransportHomCutSimplex F G σ s t).obj ⟨ULift.up i⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (σ.obj i) :=
  congrArg (fun H ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue H (σ.obj i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero s t i hi)

/-- 時刻一の対角評価の対象は、同じ終域図式の同じ底の値。 -/
lemma cocartesianTransportHomCutSimplex_obj_one
    {C : Type u} [Category.{u} C] (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 1) :
    (cocartesianTransportHomCutSimplex F G σ s t).obj ⟨ULift.up i⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (σ.obj i) :=
  congrArg (fun H ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue H (σ.obj i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one s t i hi)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
