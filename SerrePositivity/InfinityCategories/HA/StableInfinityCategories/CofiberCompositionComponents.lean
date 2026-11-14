module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionRectangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingComparisonMiddle
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.ArrowSquareHomotopy
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingSplitProjection

/-! # 合成 cofiber 比較の三成分

概要：元の列から合成射の列への比較は、始点で恒等、第二・第三成分で長方形の辺となる。
方針：比較ホモトピーの三頂点上の道を計算し、接続射の自然性を適用する。
規約：端点の表示を Arrow の等号に含める。使われ方：八面体の第一の比較と可換式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：比較三角形の射の第一成分は元の始点の恒等射。
方針：固定頂点の成分を評価する。
規約：端点を Arrow で輸送する。使われ方：接続射の可換式の始点条件。 -/
lemma CofiberCompositionRectangle.triangleMorphism_source_arrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionRectangle t τ) :
    Arrow.mk (r.triangleMorphism ht).hom₁ = Arrow.mk (𝟙 t.hoShortComplex.X₁) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTransOfEndpoints_fixedVertex_arrow r.comparisonHomotopy.h
    r.comparisonHomotopy.h₀ r.comparisonHomotopy.h₁
    (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0) r.comparisonHomotopy_source
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  exact h

/-- 概要：比較三角形の射の第二成分は長方形の右面の下辺。
方針：右下の道を指定した下辺の一次単体と比較する。
規約：端点の輸送を許す。使われ方：合成する二つ目の射との照合。 -/
lemma CofiberCompositionRectangle.triangleMorphism_middle_arrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionRectangle t τ) :
    Arrow.mk (r.triangleMorphism ht).hom₂ =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0)) := by
  have hp : ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      r.comparisonHomotopy.h = snd Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0)).edge := by
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy_middle r.diagram).trans
      (congrArg (fun g => snd (Δ[0] : SSet.{u}) Δ[1] ≫ g)
        ((by rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge]; exact (SSet.yonedaEquiv.symm_apply_apply _).symm)))
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints_vertexPath_arrow r.comparisonHomotopy
    (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow _) hp
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 0 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  exact h

/-- 概要：比較三角形の射の第三成分は二つの cofiber を結ぶ右面の上辺。
方針：右上の道を指定した上辺の一次単体と比較する。
規約：接続射を含む実際の三角形の射の成分。使われ方：八面体の最初の cofiber 間の射。 -/
lemma CofiberCompositionRectangle.triangleMorphism_target_arrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionRectangle t τ) :
    Arrow.mk (r.triangleMorphism ht).hom₃ =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0)) := by
  have hp : ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) ▷ (Δ[1] : SSet.{u})) ≫
      r.comparisonHomotopy.h = snd Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0)).edge := by
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy_target r.diagram).trans
      (congrArg (fun g => snd (Δ[0] : SSet.{u}) Δ[1] ≫ g)
        ((by rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge]; exact (SSet.yonedaEquiv.symm_apply_apply _).symm)))
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints_vertexPath_arrow r.comparisonHomotopy
    (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow _) hp
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  exact h

/-- 概要：元の cofiber と合成射の cofiber の比較は懸垂に値を取る接続射と可換。
方針：比較ホモトピーに接続射の自然性を適用する。
規約：三角形の第一・第三成分は上で指定した実際の射。使われ方：八面体の第二の可換式。 -/
lemma CofiberCompositionRectangle.connecting_comm {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) {τ : (Δ[2] : SSet.{u}) ⟶ X}
    (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionRectangle t τ) :
    (r.triangleMorphism ht).hom₃ ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting r.outerZeroTriangle r.outer_isCofiber =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map (r.triangleMorphism ht).hom₁ :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_naturality_of_homotopy t r.outerZeroTriangle ht r.outer_isCofiber
    r.comparisonHomotopy

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
