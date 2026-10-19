module

public import SerrePositivity.InfinityCategories.F1.PointedCylinderPrismProjections

/-!
概要：円柱の中間空間で普遍 prism を評価し、その二端点を厳密に回収する。
方針：全 lift 空間の普遍評価と二つの引き戻しの端点公式を使う。
規約：prism の区間と係数をまとめてからパラメーターを取る。
使われ方：円柱上の pointed-space 値の実際の関手の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：円柱の中間空間全体での普遍 prism の評価。
方針：元の全 lift 空間への射を普遍 prism の curry に合成して展開する。
規約：区間と係数 K を第一因子に置く。
使われ方：円柱の pushout の第一部分上の族。 -/
def pointedCylinderPrismEvaluation {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    (Δ[1] ⊗ K) ⊗ pointedCylinderPrismSpace f s t ⟶ PointedSpaceInfinity.{u} :=
  uncurry (pointedCylinderPrismLift f s t ≫
    prismLiftSpaceCurry pointedSpaceProjection K (pointedPrismData K s t))

/-- 概要：普遍 prism の始点は指定した始点の同値の評価。
方針：元の普遍 prism の始点公式を引き戻す。
規約：全高次パラメーターでの射の等式。
使われ方：円柱上の族の始点の検査。 -/
lemma pointedCylinderPrismEvaluation_zero {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    (prismEndpoint 0 K ▷ pointedCylinderPrismSpace f s t) ≫
        pointedCylinderPrismEvaluation f s t =
      uncurry (pointedCylinderPrismSource f s t) ≫ vertexFiberι pointedSpaceProjection s := by
  let P := pointedCylinderPrismLift f s t
  let H := prismLiftSpacePrism pointedSpaceProjection K (pointedPrismData K s t)
  have h₀ : prismEndpoint 0 (K ⊗ pointedPrismLiftSpace K s t) ≫ H =
      uncurry (pointedPrismLiftSource K s t) ≫ vertexFiberι pointedSpaceProjection s :=
    pointedPrismEvaluation_zero K s t
  calc
    _ = prismEndpoint 0 _ ≫ (Δ[1] ◁ (K ◁ P)) ≫ H := by
      dsimp only [pointedCylinderPrismEvaluation]
      rw [uncurry_natural_left]
      rfl
    _ = (K ◁ P) ≫ uncurry (pointedPrismLiftSource K s t) ≫
        vertexFiberι pointedSpaceProjection s := by
      rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₀]
    _ = uncurry (P ≫ pointedPrismLiftSource K s t) ≫ vertexFiberι pointedSpaceProjection s := by
      rw [uncurry_natural_left, Category.assoc]
    _ = _ := by rw [pointedCylinderPrismLift_source]

/-- 概要：普遍 prism の終点は終点の同値を貼り付け射で前合成した評価。
方針：元の普遍 prism の終点公式と内部 Hom の前合成の評価を使う。
規約：終点の族との貼り合わせは厳密。
使われ方：円柱上の族を pushout で貼り合わせる可換性。 -/
lemma pointedCylinderPrismEvaluation_one {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    (prismEndpoint 1 K ▷ pointedCylinderPrismSpace f s t) ≫
        pointedCylinderPrismEvaluation f s t =
      (f ▷ pointedCylinderPrismSpace f s t) ≫ uncurry (pointedCylinderPrismTarget f s t) ≫
        vertexFiberι pointedSpaceProjection t := by
  let P := pointedCylinderPrismLift f s t
  let H := prismLiftSpacePrism pointedSpaceProjection K (pointedPrismData K s t)
  have h₁ : prismEndpoint 1 (K ⊗ pointedPrismLiftSpace K s t) ≫ H =
      uncurry (pointedPrismLiftEndpoint K s t) ≫ vertexFiberι pointedSpaceProjection t :=
    pointedPrismEvaluation_one K s t
  calc
    _ = prismEndpoint 1 _ ≫ (Δ[1] ◁ (K ◁ P)) ≫ H := by
      dsimp only [pointedCylinderPrismEvaluation]
      rw [uncurry_natural_left]
      rfl
    _ = (K ◁ P) ≫ uncurry (pointedPrismLiftEndpoint K s t) ≫
        vertexFiberι pointedSpaceProjection t := by
      rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₁]
    _ = uncurry (P ≫ pointedPrismLiftEndpoint K s t) ≫ vertexFiberι pointedSpaceProjection t := by
      rw [uncurry_natural_left, Category.assoc]
    _ = uncurry (pointedCylinderPrismTarget f s t ≫ (pre f).app _) ≫
        vertexFiberι pointedSpaceProjection t := by rw [pointedCylinderPrismLift_endpoint]
    _ = _ := by rw [uncurry_pre_app, Category.assoc]

end SerrePositivity.InfinityCategories
