module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.FinitePrism

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteCocartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.FiniteFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrismVerticalSimplex

/-!
概要：有限鎖上の scaffold の最初の係数の prism とその垂直辺。
方針：円柱比較の底への射を計算し、最初の辺の cocartesian 性を全空間へ持ち上げる。
規約：元の全空間の射影は cocartesian fibration。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、Theorem 5.2.4.1（Tag 024N） の垂直辺の条件。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：scaffold の最初の係数の prism の各垂直辺は区間への射に関して cocartesian。
方針：垂直辺の底への像を最初の辺と同定し、cocartesian fibration と合成の定理を使う。
規約：係数値の Kan 性や fiber 比較の同値性はこの条件には不要。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、Theorem 5.2.4.1（Tag 024N） の第三条件。 -/
lemma cocartesianScaffoldFiniteScaffoldPrism_vertical_isCocartesian (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)
    (horiz : ∀ {c d} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (l.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge F f x)))
    (x : (F.obj (ULift.up 0)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteScaffoldPrism n F l) x) := by
  let f : (ULift.up (0 : Fin (n + 2)) : ULift.{u} _) ⟶ ULift.up 1 :=
    homOfLE (Fin.zero_le _)
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteScaffoldPrism n F l) x =
      l.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge F f x) := by
    change ((pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F.obj (ULift.up 0)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCylinderAttachingMap n F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCylinderComparison n F) ≫ l).app _
        (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCylinderComparison_inl]
    change l.app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1))).app _
        (SSet.yonedaEquiv ((stdSimplex.isoNerve 1).hom ≫
          nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitialEdge_yoneda]
    change l.app (Opposite.op ⦋1⦌)
      (⟨ComposableArrows.mk₁ f, SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) ≫
        F.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)).to (ULift.up 0))⟩) = _
    rw [show (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)).to (ULift.up 0) = 𝟙 _ from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)).hom_ext _ _, F.map_id, Category.comp_id]
    have hc : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
        (SSet.const x : (Δ[1] : SSet.{u}) ⟶ F.obj (ULift.up 0)) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      rfl
    rw [hc]
    rfl
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteScaffoldPrism n F l) x) := by
    rw [hv]
    exact horiz f x
  apply hp.comp
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteScaffoldPrism_projection n p F l h)
  change p.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteScaffoldPrism n F l) x) =
      SSet.yonedaEquiv ((stdSimplex.isoNerve 1).hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n)) at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitialEdge_yoneda] at he
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitialEdge_isCocartesian n

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
