module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleTwoCutCoordinates
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：二つの K 座標を持つ長 Hom の区間族を、元の小さい豊穣 Hom の作用へ戻す。
方針：有限 path の座標だけを持ち上げ、元の K・L の単体を評価して fully faithful な
ulift の逆像を取る。
規約：K・L は対象宇宙の単体集合でよい。豊穣 Hom の宇宙は元のまま保持する。
使われ方：SpaceInfinity の元の native Hom に全パラメーターを反映する二胞体構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 有限の標準単体座標を持ち上げ、元の大きいパラメーターの単体で評価する。 -/
def triangleLiftedCoordinate {A : SSet.{u}} {K : SSet.{max u v}} {n : ℕ}
    (c : A ⟶ (Δ[n] : SSet.{u})) (s : K _⦋n⦌) :
    (SSet.uliftFunctor.{v, u}).obj A ⟶ K :=
  (SSet.uliftFunctor.{v, u}).map c ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom ≫
    SSet.yonedaEquiv.symm s

/-- 分離した二つの K 座標と一つの L 座標による、元の小さい長 Hom の作用。 -/
def triangleSeparatedLongHom
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj H)
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶ H :=
  (SSet.uliftFunctor.{v, u}).preimage
    (lift ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddleMap t i j) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).hom)
      (lift
        (lift (triangleLiftedCoordinate
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) s)
          (triangleLiftedCoordinate
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel_zero t hi) j) s))
        (triangleLiftedCoordinate
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) r)) ≫ M)

/-- 同じ作用を持ち上げると、定義した二切断・中間ラベルの全座標を厳密に回収する。 -/
lemma triangleSeparatedLongHom_map
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj H)
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    (SSet.uliftFunctor.{v, u}).map (triangleSeparatedLongHom M s r t hi j) =
      lift ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddleMap t i j) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).hom)
        (lift
          (lift (triangleLiftedCoordinate
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) s)
            (triangleLiftedCoordinate
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel_zero t hi) j) s))
          (triangleLiftedCoordinate
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) r)) ≫ M := by
  exact (SSet.uliftFunctor.{v, u}).map_preimage _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
