module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeLastVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.FinalHornRestrictionLifting

/-! # 余錐の制限射に対する cartesian な辺

概要：余錐の頂点で可逆な関手の辺は、余錐の制限射に対して cartesian である。
方針：二変数を交換し、相対骨格の最後の頂点での可逆性による外側ホーン充填を使う。
規約：F1 の既存 IsCartesianEdge を用いる。使われ方：S3 の余錐の輸送の認証。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐全体からの関手を余錐の頂点で評価する。
方針：右の零単体の包含を通じて関手を評価する。
規約：X と K は任意の単体集合。
使われ方：Kerodon §5.3.7（Tag 01US） の cartesian な余錐の辺の条件。 -/
def coconeApexEvaluation (K X : SSet.{u}) : (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

/-- 概要：余錐の頂点で可逆な関手の辺は余錐の制限に対して cartesian。
方針：ホーンと余錐の二変数を交換し、余錐の頂点で可逆な最後の辺を用いて相対骨格を充填する。
規約：X は quasicategory、K に有限性や quasicategory 性は仮定しない。
使われ方：Kerodon Corollary 5.3.7.5（Tag 02VW）・7.1.6.13（Tag 02XB） の余錐の制限の輸送。 -/
lemma isCartesianEdge_coconeRestriction_of_apex {K X : SSet.{u}} [Quasicategory X]
    {f g : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X) _⦋0⦌}
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X)) f g)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (coconeApexEvaluation K X)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) e.edge := by
  intro m σ β hσ sq
  have hw := sq.w
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X β
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) D X σ
  have hsq : a ≫ (pre (horn (m + 2) (Fin.last (m + 2))).ι).app X = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ b := by
    have hh := congrArg
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) K X) hw
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre] at hh
    exact hh.symm
  have ht (n : ℕ) (s : D _⦋n⦌)
      (hs : s ∉ Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u})).app (Opposite.op ⦋n⦌))) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s) 1))) := by
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex
      rw [SSet.yonedaEquiv_symm_app]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeSimplex_lastVertex_of_not_range s hs
    have hedge : (uncurry b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s) 1) =
        (e.map ((truncation 2).map (coconeApexEvaluation K X))).edge := by
      rw [hv]
      dsimp [b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv]
      rw [uncurry_curry]
      change (coconeApexEvaluation K X).app (Opposite.op ⦋1⦌)
        (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m)) = _
      rw [hσ]
      rfl
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hedge).2 he
  obtain ⟨F, hF₁, hF₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.finalHornRestriction_lift_of_last_vertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) m a b hsq ht
  let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).symm F
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X G = F :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).apply_symm_apply F
  refine CommSq.HasLift.mk' { l := G, fac_left := ?_, fac_right := ?_ }
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) D X).injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre, hG]
    exact hF₂
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X
      (G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}))).app X) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, hG]
    exact hF₁


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
