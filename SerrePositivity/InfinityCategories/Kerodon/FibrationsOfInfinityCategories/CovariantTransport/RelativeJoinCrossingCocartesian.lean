module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinInitialHornLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IntervalInitialEdgeCut
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornDuality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrismVerticalSimplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian

/-!
概要：相対 join の両因子を渡る辺の cocartesian 性。
方針：時間の最初の辺から切断一を得て、可逆な係数辺に沿って外ホーンを充填する。
規約：係数側 Y に quasicategory 性を要求する。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、Example 5.2.3.18（Tag 02RJ）、標準 prism の垂直辺。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：区間を渡り係数側に可逆辺を持つ相対 join の辺は cocartesian。
方針：係数側の初期外ホーンを可逆辺で充填し、切断一の相対 join の持ち上げを使う。
規約：左因子 X には充填性を要求しない。
使われ方：Kerodon Example 5.2.3.18（Tag 02RJ）、Proposition 5.2.3.15（Tag 024J） の標準垂直辺の場合。 -/
lemma relativeJoin_crossing_isCocartesian {X Y : SSet.{u}} [Quasicategory Y]
    (f : X ⟶ Y) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y)) _⦋1⦌)
    (ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y)).app (Opposite.op ⦋1⦌) e =
      stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f (𝟙 Y)).app (Opposite.op ⦋1⦌) e))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y)) e := by
  intro n a b ha sq
  have hb : b.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n).val =
      stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) := by
    have hh := congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n)) sq.w
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y)).app (Opposite.op ⦋1⦌)
        (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n)) =
      b.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n).val at hh
    rw [ha, ht] at hh
    exact hh.symm
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasInitialHornFillers_of_isInvertibleEdge _ he n
    (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f (𝟙 Y)) (by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f (𝟙 Y)).app (Opposite.op ⦋1⦌)
        (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n)) = _
      rw [ha]
      rfl)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_initialHorn_hasLift_of_coefficient n f a b sq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.intervalHom_cut_one_of_initial_edge n b hb) c hc

/-- 概要：相対 join の標準 prism の垂直辺は cocartesian。
方針：時間の像は標準区間の恒等辺、係数側の像は退化辺であることを計算する。
規約：左因子の quasicategory 性は不要、係数 Y は quasicategory。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、区間上の写像円柱比較の条件。 -/
lemma relativeJoinPrism_vertical_isCocartesian {X Y : SSet.{u}} [Quasicategory Y]
    (f : X ⟶ Y) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f) x) := by
  apply relativeJoin_crossing_isCocartesian
  · exact congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_projection f)
  · have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f (𝟙 Y)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f) x) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (f.app (Opposite.op ⦋0⦌) x) 1 := by
      have hh := congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
        (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_baseProjection f)
      exact hh.trans (ConcreteCategory.congr_hom (C := Type u)
        (f.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) x)
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj Y)
        (f.app (Opposite.op ⦋0⦌) x)) := by
      change IsIso (SSet.Truncated.HomotopyCategory.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) _))
      rw [SSet.Truncated.HomotopyCategory.homMk_id]
      infer_instance
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (hc.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _))).mpr hi

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
