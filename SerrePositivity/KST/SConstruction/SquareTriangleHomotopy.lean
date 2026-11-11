module
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinders
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTrianglePushout

/-! # 同じ全対角比較を共有する二三角形の全高次比較を貼る
概要：正方形の元の両三角形の全比較を、元の両正方形を結ぶ全比較へ戻す。
方針：正方形の三角形分割の pushout を全比較区間との直積で保つ。
規約：両元の全面と全対角円柱を保ち、零単体だけの比較に弱めない。
使われ方：始辺消去四面体の高次比較から、出力した全円柱の高次比較を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {E : SSet.{u}} {f g : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E}
  (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ g))
  (K : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ g))
  (hc : (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫ K.h)

/-- 二つの全三角形比較を、同じ全対角円柱に沿って貼った実写像。 -/
def squareTriangleHomotopyMap :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.map (tensorRight (Δ[1] : SSet.{u}))).desc H.h K.h hc

/-- 元の上側全三角形比較を厳密に回収する。 -/
lemma squareTriangleHomotopyMap_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫ squareTriangleHomotopyMap H K hc = H.h :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.map (tensorRight (Δ[1] : SSet.{u}))).inl_desc _ _ _

/-- 元の下側全三角形比較も厳密に回収する。 -/
lemma squareTriangleHomotopyMap_lower :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ▷ (Δ[1] : SSet.{u})) ≫ squareTriangleHomotopyMap H K hc = K.h :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.map (tensorRight (Δ[1] : SSet.{u}))).inr_desc _ _ _

/-- 貼った全比較の始端は元の同じ正方形全体。 -/
lemma squareTriangleHomotopyMap_zero :
    SSet.ι₀ ≫ squareTriangleHomotopyMap H K hc = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext
  · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc,
      squareTriangleHomotopyMap_upper, H.h₀]
  · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc,
      squareTriangleHomotopyMap_lower, K.h₀]

/-- 貼った全比較の終端も元の同じ正方形全体。 -/
lemma squareTriangleHomotopyMap_one :
    SSet.ι₁ ≫ squareTriangleHomotopyMap H K hc = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext
  · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc,
      squareTriangleHomotopyMap_upper, H.h₁]
  · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc,
      squareTriangleHomotopyMap_lower, K.h₁]

/-- 元の二正方形を両端に持ち、元の両三角形比較を保持する実高次円柱。 -/
def squareTriangleHomotopy : SSet.Homotopy f g where
  h := squareTriangleHomotopyMap H K hc
  h₀ := squareTriangleHomotopyMap_zero H K hc
  h₁ := squareTriangleHomotopyMap_one H K hc
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro q
    exact False.elim q.1.property

/-- 元の両全面の全基底比較を指定すれば、貼った全比較もその同じ基底像を保つ。 -/
lemma squareTriangleHomotopyMap_projection {B : SSet.{u}} (p : E ⟶ B)
    (q : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ B)
    (hu : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫ q = H.h ≫ p)
    (hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ▷ (Δ[1] : SSet.{u})) ≫ q = K.h ≫ p) :
    squareTriangleHomotopyMap H K hc ≫ p = q := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.map (tensorRight (Δ[1] : SSet.{u}))).hom_ext
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫ _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ▷ (Δ[1] : SSet.{u})) ≫ q
    rw [← Category.assoc, squareTriangleHomotopyMap_upper, hu]
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ▷ (Δ[1] : SSet.{u})) ≫ _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ▷ (Δ[1] : SSet.{u})) ≫ q
    rw [← Category.assoc, squareTriangleHomotopyMap_lower, hl]

end SerrePositivity.KST.SConstruction
