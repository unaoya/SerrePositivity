module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps

/-! # 正方形の宇宙比較

概要：正方形の ULift と大きい宇宙の正方形の同型は二つの実三角形を保つ。
方針：直積と標準単体の同型を合成し、Yoneda 座標を照合する。
規約：辺・対角を含む実単体集合の比較。使われ方：普遍四角形の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet MonoidalCategory
open scoped _root_.Simplicial

/-- 正方形の持ち上げと大きい宇宙の正方形の実同型。 -/
def uliftSquareIso :
    (SSet.uliftFunctor.{v, u}).obj (Δ[1] ⊗ Δ[1] : SSet.{u}) ≅
      (Δ[1] ⊗ Δ[1] : SSet.{max u v}) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso Δ[1] Δ[1] ≪≫
    MonoidalCategory.tensorIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso 1) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso 1)

/-- 二つの三角形は正方形の宇宙同型で保たれる。 -/
lemma uliftSquareIso_triangle (i : Fin 2) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i) ≫ uliftSquareIso.hom =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 2).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i :
        (Δ[2] : SSet.{max u v}) ⟶ Δ[1] ⊗ Δ[1]) := by
  ext d s <;> fin_cases i <;> rfl

/-- 正方形からの実図式の持ち上げ。 -/
def uliftSquare {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X :=
  uliftSquareIso.inv ≫ (SSet.uliftFunctor.{v, u}).map F

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
