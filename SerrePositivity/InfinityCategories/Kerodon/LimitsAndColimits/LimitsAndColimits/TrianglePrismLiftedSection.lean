module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TrianglePrismCoordinateSection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedVertexParameter

/-!
概要：有限 native path の切断を対象宇宙へ持ち上げる。
方針：標準単体とテンソルの既存 ulift 同型を使い、二座標の切断を移す。
規約：大きい補助パラメーターの全次数を保持する。
使われ方：K の頂点上で、実長 Hom から元の区間・高次パラメーターを回収する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 二座標の有限切断を、対象宇宙の標準単体の積から実現する。 -/
def trianglePrismLiftedSection (n : ℕ) :
    (Δ[1] : SSet.{max u v}) ⊗ Δ[n] ⟶
      (SSet.uliftFunctor.{v, u}).obj
        (nerve (Path (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3)))
          (ULift.up (Fin.last (n + 2))))) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).inv ⊗ₘ
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, v} Δ[1] Δ[n]).inv ≫
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinateSection n)

/-- 元の区間座標を、そのまま回収する。 -/
lemma trianglePrismLiftedSection_middle (n : ℕ) :
    trianglePrismLiftedSection.{u, v} n ≫
      (SSet.uliftFunctor.{v, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddleMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n) 0 (Fin.last (n + 2))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).hom = fst Δ[1] Δ[n] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨b, k⟩
  apply stdSimplex.ext
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinatePath_middle.{u} n (b i) (k i)

/-- 零側の全標準単体座標を、そのまま回収する。 -/
lemma trianglePrismLiftedSection_lastZero (n : ℕ) :
    trianglePrismLiftedSection.{u, v} n ≫ (SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel_zero n)) (Fin.last (n + 2)) ≫
        stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismRetraction n))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom = snd Δ[1] Δ[n] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨b, k⟩
  apply stdSimplex.ext
  intro i
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismRetraction n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel_zero n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinatePath.{u} n (b i) (k i))) = k i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinatePath_lastZero.{u}]
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt_succ (k i).isLt)

/-- 任意の補助パラメーターの単体を、零側の切断から厳密に回収する。 -/
lemma trianglePrismLiftedSection_parameter {L : SSet.{max u v}}
    (n : ℕ) (r : L _⦋n⦌) :
    trianglePrismLiftedSection.{u, v} n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel_zero n)) (Fin.last (n + 2)))
      (L.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismRetraction n)).op r) =
        snd Δ[1] Δ[n] ≫ SSet.yonedaEquiv.symm r := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate_naturality, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ SSet.yonedaEquiv.symm r)
      (trianglePrismLiftedSection_lastZero n))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
