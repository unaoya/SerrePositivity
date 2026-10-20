module
public import SerrePositivity.KST.SConstruction.FamilyCylinderEndpointAdjustment

/-! # 全区間境界固定の比較からの実円柱補正
概要：元の全区間境界の固定式を直接使い、両端と基底比較全体を保つ相対補正を行う。
方針：単射な区間境界に沿って実二次元比較を持ち上げ、二端面を厳密に回収する。
規約：合成した全境界固定比較をそのまま使い、二面への選び直しを挟まない。
使われ方：累積補正を含む全段帰納の相対持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 合成済みの全境界固定比較を、その全射影を保持して相対的に持ち上げる。 -/
def cylinderBoundaryAdjustmentData {U E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    {a b : U ⟶ E} (H : SSet.Homotopy a b)
    (G : SSet.Homotopy (a ≫ p) (b ≫ p)) (L : SSet.Homotopy (H.h ≫ p) G.h)
    (hr : ((U ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫ L.h =
      fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫
        (U ◁ (SSet.boundary 1).ι) ≫ H.h ≫ p) : CylinderEndpointAdjustmentData p H G L := by
  let ex := exists_relative_fibration_family_transport p (U ◁ (SSet.boundary 1).ι) H.h L hr
  let k := ex.choose
  have he := familyCylinder_endpoints_of_boundary ex.choose_spec.2.1
  let K : SSet.Homotopy a b := {
    h := k
    h₀ := he.1.trans H.h₀
    h₁ := he.2.trans H.h₁
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  exact ⟨K, ex.choose_spec.1, ex.choose_spec.2.2.choose,
    ex.choose_spec.2.2.choose_spec.1, ex.choose_spec.2.2.choose_spec.2⟩

end SerrePositivity.KST.SConstruction
