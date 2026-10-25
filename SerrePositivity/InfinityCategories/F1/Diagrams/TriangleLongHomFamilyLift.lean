module

public import SerrePositivity.InfinityCategories.F1.Diagrams.KanIntervalEvaluation
public import SerrePositivity.InfinityCategories.Core.VertexDiscrete

/-!
概要：合成端固定の長い Hom 全族を、全入力点の指定値を保って構成する。
方針：全 path の評価の trivial Kan 持ち上げ性を零骨格包含へ適用する。
規約：指定値は全 native Hom の関手頂点であり、直接 path の値だけではない。
使われ方：Ind-S (9) の各二胞体からの全族読出し。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- trivial Kan fibration の持ち上げは全頂点の指定値を保てる。 -/
lemma trivialKanFibration_exists_lift_with_vertices {E B K : SSet.{u}}
    (p : E ⟶ B) [TrivialKanFibration p] (c : K ⟶ B)
    (x : K _⦋0⦌ → E _⦋0⦌)
    (hx : ∀ k, p.app (Opposite.op ⦋0⦌) (x k) = c.app (Opposite.op ⦋0⦌) k) :
    ∃ q : K ⟶ E, q ≫ p = c ∧ ∀ k, q.app (Opposite.op ⦋0⦌) k = x k := by
  have : HasLiftingProperty (vertexDiscreteι K) p := TrivialKanFibration.mem _ inferInstance
  let sq : CommSq (vertexDiscreteMap x) (vertexDiscreteι K) p c :=
    ⟨vertexDiscreteMap_comp p c x hx⟩
  refine ⟨sq.lift, sq.fac_right, ?_⟩
  intro k
  have hk := ConcreteCategory.congr_hom
    (NatTrans.congr_app sq.fac_left (Opposite.op ⦋0⦌)) k
  change sq.lift.app (Opposite.op ⦋0⦌) (PinchedHom.constant k 0) =
    PinchedHom.constant (x k) 0 at hk
  simpa only [pinchedConstant_zero] using hk

/-- 全 native Hom の入力点ごとの指定と、全入力で固定した合成端を同時に回収する。 -/
lemma triangleLongHomFamily_exists_with_vertices
    (H K : SSet.{max u v}) [KanComplex H] (c : K ⟶ H)
    (x : K _⦋0⦌ → ((ihom
      ((SSet.uliftFunctor.{v, u}).obj (nerve TriangleNativePath.{u}))).obj H) _⦋0⦌)
    (hx : ∀ k, (evaluateFunctorAt
      (X := (SSet.uliftFunctor.{v, u}).obj (nerve TriangleNativePath.{u})) (Y := H)
      (ULift.up (ComposableArrows.mk₀ triangleFullPath))).app (Opposite.op ⦋0⦌) (x k) =
        c.app (Opposite.op ⦋0⦌) k) :
    ∃ q : K ⟶ (ihom ((SSet.uliftFunctor.{v, u}).obj
        (nerve TriangleNativePath.{u}))).obj H,
      q ≫ evaluateFunctorAt
        (X := (SSet.uliftFunctor.{v, u}).obj (nerve TriangleNativePath.{u}))
        (Y := H) (ULift.up (ComposableArrows.mk₀ triangleFullPath)) = c ∧
      ∀ k, q.app (Opposite.op ⦋0⦌) k = x k := by
  have := triangleLongHomEvaluation_trivialKanFibration.{u, v} H
  exact trivialKanFibration_exists_lift_with_vertices _ c x hx

end SerrePositivity.InfinityCategories
