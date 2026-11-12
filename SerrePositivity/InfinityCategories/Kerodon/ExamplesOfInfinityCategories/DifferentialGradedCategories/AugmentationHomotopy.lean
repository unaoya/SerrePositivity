module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy
public import Mathlib.Tactic.Abel

/-!
# A.5 の augmentation 補正とホモトピーの相殺

概要：補正された右辺から定数射への m 次ホモトピーを取り出す。
方針：C⊗ℤΔ¹ の射の加減法を用いる。
規約：KST Construction A.5 の右辺の augmentation 補正。被約複体には移さない。
使われ方：Lemma 4.16 の C(ψ) ≃ C(ψ)+C(φ)−C(e) から C(φ) ≃ C(e) を導く。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

/-- 概要：自由整数加群のテンソル区間からの射影。
方針：積の自由化との同型と幾何的射影を合成する。
規約：KST Definition A.3 の定数ホモトピー。
使われ方：A.5 の augmentation 補正を加減する。 -/
def linearizedCylinderProjection (X : SSet.{u}) : linearizedCylinder X ⟶ linearizedSpace X :=
  (linearizedTensorIso X Δ[1]).hom ≫ linearizedSpaceMap (CartesianMonoidalCategory.fst X Δ[1])

/-- 概要：区間の零端点と射影の合成は恒等写像。
方針：自由化関手に幾何的端点の等式を適用する。
規約：KST Definition A.3。使われ方：定数ホモトピーの始点条件。 -/
@[reassoc (attr := simp)]
lemma linearizedEndpoint₀_projection (X : SSet.{u}) :
    linearizedEndpoint₀ X ≫ linearizedCylinderProjection X = 𝟙 _ := by
  simp only [linearizedEndpoint₀, linearizedCylinderProjection,
    Category.assoc, Iso.inv_hom_id_assoc]
  change ((SimplicialObject.whiskering _ _).obj integerLinearization).map SSet.ι₀ ≫
    ((SimplicialObject.whiskering _ _).obj integerLinearization).map
      (CartesianMonoidalCategory.fst X Δ[1]) = _
  rw [← CategoryTheory.Functor.map_comp, SSet.ι₀_fst]
  exact ((SimplicialObject.whiskering _ _).obj integerLinearization).map_id X

/-- 概要：区間の一端点と射影の合成は恒等写像。
方針：自由化関手に幾何的端点の等式を適用する。
規約：KST Definition A.3。使われ方：定数ホモトピーの終点条件。 -/
@[reassoc (attr := simp)]
lemma linearizedEndpoint₁_projection (X : SSet.{u}) :
    linearizedEndpoint₁ X ≫ linearizedCylinderProjection X = 𝟙 _ := by
  simp only [linearizedEndpoint₁, linearizedCylinderProjection,
    Category.assoc, Iso.inv_hom_id_assoc]
  change ((SimplicialObject.whiskering _ _).obj integerLinearization).map SSet.ι₁ ≫
    ((SimplicialObject.whiskering _ _).obj integerLinearization).map
      (CartesianMonoidalCategory.fst X Δ[1]) = _
  rw [← CategoryTheory.Functor.map_comp, SSet.ι₁_fst]
  exact ((SimplicialObject.whiskering _ _).obj integerLinearization).map_id X

/-- 概要：補正された和の比較から augmentation 定数射への比較を取り出す。
方針：区間写像 H を、定数な ψ+φ の区間写像から引く。
規約：KST Lemma 4.16 に用いる A.5 の右辺の augmentation 補正。同変性は別条件。
使われ方：非被約 C(H) 上で C(φ) と C(e) の m 次ホモトピーを構成する。 -/
def LinearizedMHomotopy.cancel_augmentation
    {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
    {ψ φ e : linearizedSpace X ⟶ D} {m : ℕ}
    (H : LinearizedMHomotopy ψ (ψ + φ - e) m) : LinearizedMHomotopy φ e m where
  h := linearizedCylinderProjection X ≫ (ψ + φ) - H.h
  h₀ n hn := by
    simp only [Preadditive.comp_sub, linearizedEndpoint₀_projection_assoc,
      NatTrans.app_sub, NatTrans.app_add, H.h₀ n hn]
    abel
  h₁ n hn := by
    simp only [Preadditive.comp_sub, linearizedEndpoint₁_projection_assoc,
      NatTrans.app_sub, NatTrans.app_add, H.h₁ n hn]
    abel

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
