module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedLongHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleDiagonalKanExtension

/-!
概要：中間対象を含まない部分の長 Hom は、元の区間族の直接 path 評価そのもの。
方針：二つの切断を同じ K 座標へ戻し、延長の対角上の等式を使う。
規約：全次数の Hom の射の厳密等号であり、零単体だけの照合ではない。
使われ方：再構成二胞体の長辺と標準 coherent 区間族の全対角式。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 元の長 Hom を対角上で保持する延長は、中間ラベルのない部分で直接 path を回収する。 -/
lemma triangleSeparatedLongHom_of_no_middle
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj H)
    (q : (Δ[1] : SSet.{max u v}) ⊗ (K ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj H)
    (hM : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleParameterDiagonal K L) ≫ M = q)
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (hP : ∀ P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j),
      ¬ ∃ k : Fin (n + 1), ULift.up k ∈ P.I ∧ t k = 1) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M s r t hi j) =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) s)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) r) ≫
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (K ⊗ L)) ≫ q := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleCutMaps_eq_of_no_middle t hi hP,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleMiddleMap_eq_zero_of_no_middle t hP]
  have hc : (SSet.uliftFunctor.{v, u}).map
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
          nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶ Δ[1]) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).hom =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    rfl
  rw [hc, ← hM]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
