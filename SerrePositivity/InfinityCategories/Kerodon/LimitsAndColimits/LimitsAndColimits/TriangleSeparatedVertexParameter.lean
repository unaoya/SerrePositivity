module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedConstantNative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLiftedCoordinateIdentities

/-!
概要：K の頂点を固定しても、補助パラメーター L の高次単体全体は保持される。
方針：二つの K 切断だけを同じ定値頂点へ戻し、延長の対角式を使う。
規約：L の単体を定値とは仮定しない。任意の次数での全 native Hom の等号。
使われ方：単射性の検討に使う、高次パラメーターの明示的な回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma triangleSeparatedLongHom_vertex_parameter
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (q : (Δ[1] : SSet.{max u v}) ⊗ (K ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (hdiag : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleParameterDiagonal K L) ≫ M = q)
    (k : K _⦋0⦌) {n : ℕ} (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    (SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k n) r t hi j) =
      lift ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddleMap t i j) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).hom)
        (lift (SSet.const k) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) r)) ≫ q := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate_constant,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate_constant, ← hdiag]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
