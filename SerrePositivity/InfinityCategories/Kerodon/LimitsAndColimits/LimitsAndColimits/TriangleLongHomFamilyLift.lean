module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanIntervalEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.VertexDiscrete

/-!
概要：合成端固定の長い Hom 全族を、全入力点の指定値を保って構成する。
方針：全 path の評価の trivial Kan 持ち上げ性を零骨格包含へ適用する。
規約：指定値は全 native Hom の関手頂点であり、直接 path の値だけではない。
使われ方：Ind-S (9) の各二胞体からの全族読出し。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- trivial Kan fibration の持ち上げは全頂点の指定値を保てる。 -/
lemma trivialKanFibration_exists_lift_with_vertices {E B K : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (c : K ⟶ B)
    (x : K _⦋0⦌ → E _⦋0⦌)
    (hx : ∀ k, p.app (Opposite.op ⦋0⦌) (x k) = c.app (Opposite.op ⦋0⦌) k) :
    ∃ q : K ⟶ E, q ≫ p = c ∧ ∀ k, q.app (Opposite.op ⦋0⦌) k = x k := by
  have : HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι K) p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _ inferInstance
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι K) p c :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp p c x hx⟩
  refine ⟨sq.lift, sq.fac_right, ?_⟩
  intro k
  have hk := ConcreteCategory.congr_hom
    (NatTrans.congr_app sq.fac_left (Opposite.op ⦋0⦌)) k
  change sq.lift.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 0) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x k) 0 at hk
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using hk

/-- 全 native Hom の入力点ごとの指定と、全入力で固定した合成端を同時に回収する。 -/
lemma triangleLongHomFamily_exists_with_vertices
    (H K : SSet.{max u v}) [KanComplex H] (c : K ⟶ H)
    (x : K _⦋0⦌ → ((ihom
      ((SSet.uliftFunctor.{v, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj H) _⦋0⦌)
    (hx : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (X := (SSet.uliftFunctor.{v, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})) (Y := H)
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath))).app (Opposite.op ⦋0⦌) (x k) =
        c.app (Opposite.op ⦋0⦌) k) :
    ∃ q : K ⟶ (ihom ((SSet.uliftFunctor.{v, u}).obj
        (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj H,
      q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (X := (SSet.uliftFunctor.{v, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
        (Y := H) (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath)) = c ∧
      ∀ k, q.app (Opposite.op ⦋0⦌) k = x k := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLongHomEvaluation_trivialKanFibration.{u, v} H
  exact trivialKanFibration_exists_lift_with_vertices _ c x hx

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
