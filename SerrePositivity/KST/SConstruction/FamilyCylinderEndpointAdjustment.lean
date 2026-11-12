module
public import SerrePositivity.KST.SConstruction.FamilyCylinderFixedBoundary
public import SerrePositivity.KST.SConstruction.RelativeFamilyRectification

/-! # 元の二次元比較を保つ両端固定の円柱の相対補正
概要：Kan fibration に沿って円柱を補正し、両端と全二次元比較の射影を保持する。
方針：元の区間境界上の固定式を相対持ち上げに使い、二頂点から両端を回収する。
規約：端点・射影を厳密に固定し、与えられた全基底比較円柱を持ち上げる。
使われ方：全段 raw 比較を厳密に可換にする各逐次段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 同じ全区間境界を持つ二円柱は、元の二端面も厳密に一致する。 -/
lemma familyCylinder_endpoints_of_boundary {U E : SSet.{u}}
    {v w : U ⊗ (Δ[1] : SSet.{u}) ⟶ E}
    (h : (U ◁ (SSet.boundary 1).ι) ≫ v = (U ◁ (SSet.boundary 1).ι) ≫ w) :
    SSet.ι₀ ≫ v = SSet.ι₀ ≫ w ∧ SSet.ι₁ ≫ v = SSet.ι₁ ≫ w := by
  have hz : (vertexSection U ≫ U ◁ SSet.boundary.ι (1 : Fin 2)) ≫
      (U ◁ (SSet.boundary 1).ι) = SSet.ι₀ := by
    rw [Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι]
    exact section_zero U
  have ho : (vertexSection U ≫ U ◁ SSet.boundary.ι (0 : Fin 2)) ≫
      (U ◁ (SSet.boundary 1).ι) = SSet.ι₁ := by
    rw [Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι]
    exact section_one U
  constructor
  · simpa only [← Category.assoc, hz] using congrArg
      ((vertexSection U ≫ U ◁ SSet.boundary.ι (1 : Fin 2)) ≫ ·) h
  · simpa only [← Category.assoc, ho] using congrArg
      ((vertexSection U ≫ U ◁ SSet.boundary.ι (0 : Fin 2)) ≫ ·) h

/-- 元の基底比較をそのまま持ち上げ、円柱の両端を厳密に保って射影を補正する。 -/
lemma exists_endpoint_preserving_cylinder_adjustment {U E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] {a b : U ⟶ E} (H : SSet.Homotopy a b)
    (G : SSet.Homotopy (a ≫ p) (b ≫ p)) (L : SSet.Homotopy (H.h ≫ p) G.h)
    (h₀ : (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ L.h = fst U Δ[1] ≫ a ≫ p)
    (h₁ : (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ L.h = fst U Δ[1] ≫ b ≫ p) :
    ∃ K : SSet.Homotopy a b, K.h ≫ p = G.h ∧
      ∃ V : SSet.Homotopy H.h K.h,
        ((U ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫ V.h =
          fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫ (U ◁ (SSet.boundary 1).ι) ≫ H.h ∧
        V.h ≫ p = L.h := by
  have hr := familyCylinder_fixed_boundary (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H p) h₀ h₁
  obtain ⟨k, hk, hj, V, hV, hp⟩ := exists_relative_fibration_family_transport
    p (U ◁ (SSet.boundary 1).ι) H.h L hr
  have he := familyCylinder_endpoints_of_boundary hj
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
  exact ⟨K, hk, V, hV, hp⟩

/-- 元の全基底比較と両端境界を保つ補正円柱と実比較のデータ。 -/
structure CylinderEndpointAdjustmentData {U E B : SSet.{u}} (p : E ⟶ B)
    {a b : U ⟶ E} (H : SSet.Homotopy a b)
    (G : SSet.Homotopy (a ≫ p) (b ≫ p)) (L : SSet.Homotopy (H.h ≫ p) G.h) where
  /-- 元の両端を持つ補正済み円柱。 -/
  val : SSet.Homotopy a b
  /-- 指定した基底円柱の厳密な回収。 -/
  projection : val.h ≫ p = G.h
  /-- 元の円柱から補正済み円柱への実二次元比較。 -/
  comparison : SSet.Homotopy H.h val.h
  /-- 元の全区間境界を全比較時刻で厳密に固定する。 -/
  boundary : ((U ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫ comparison.h =
    fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫ (U ◁ (SSet.boundary 1).ι) ≫ H.h
  /-- 指定した元の基底比較全体を回収する。 -/
  comparison_projection : comparison.h ≫ p = L.h

/-- 元の二次元比較をそのまま持ち上げる、両端固定の実補正データを構成する。 -/
def cylinderEndpointAdjustmentData {U E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    {a b : U ⟶ E} (H : SSet.Homotopy a b)
    (G : SSet.Homotopy (a ≫ p) (b ≫ p)) (L : SSet.Homotopy (H.h ≫ p) G.h)
    (h₀ : (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ L.h = fst U Δ[1] ≫ a ≫ p)
    (h₁ : (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ L.h = fst U Δ[1] ≫ b ≫ p) :
    CylinderEndpointAdjustmentData p H G L := by
  let ex := exists_endpoint_preserving_cylinder_adjustment p H G L h₀ h₁
  exact ⟨ex.choose, ex.choose_spec.1, ex.choose_spec.2.choose,
    ex.choose_spec.2.choose_spec.1, ex.choose_spec.2.choose_spec.2⟩

end SerrePositivity.KST.SConstruction
