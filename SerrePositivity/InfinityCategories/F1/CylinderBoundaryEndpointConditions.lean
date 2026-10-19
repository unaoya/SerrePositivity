module

public import SerrePositivity.InfinityCategories.F1.CylinderFixedBoundaryFamily

/-!
概要：円柱の境界関手の固定条件と両端の fiber 写像の固定条件の同値。
方針：境界の左右の包含へ制限し、逆方向は直和の一意性を使う。
規約：任意の高次パラメーターの族に対して厳密な条件を比較する。
使われ方：境界関手の fiber と両端制限の fiber の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：境界関手を固定することは両端の fiber 写像をそれぞれ固定することと同値。
方針：包含後の端点公式と直和の射の一意性を使う。
規約：F は任意のパラメーター L からの族。
使われ方：実際の四角形の境界 fiber の条件の並べ替え。 -/
lemma cylinderBoundaryCondition_iff_endpoints {K J L : SSet.{u + 1}} (f : K ⟶ J)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t)
    (F : L ⟶ cylinderFixedEndpointSquareSpace f s t) :
    F ≫ (cylinderFixedEndpointSquarePointed f s t ≫
        (pre (transportCylinderEndpointInclusion f)).app _) =
      SSet.const (functorVertex (intervalBoundaryPointedMap g₀ g₁)) ↔
    F ≫ cylinderFixedEndpointSquareSource f s t = SSet.const (functorVertex g₀) ∧
      F ≫ cylinderFixedEndpointSquareTarget f s t = SSet.const (functorVertex g₁) := by
  constructor
  · intro hb
    constructor
    · apply functorVertexFiber_hom_ext pointedSpaceProjection s
      rw [Category.assoc, cylinderFixedEndpointSquareSource_ι, SSet.const_comp]
      have h := congrArg (fun w ↦ w ≫ (pre (joinEndpointInl K J)).app PointedSpaceInfinity) hb
      simp only [Category.assoc] at h
      rw [← NatTrans.comp_app, ← pre_map, SSet.const_comp] at h
      exact h
    · apply functorVertexFiber_hom_ext pointedSpaceProjection t
      rw [Category.assoc, cylinderFixedEndpointSquareTarget_ι, SSet.const_comp]
      have h := congrArg (fun w ↦ w ≫ (pre (joinEndpointInr K J)).app PointedSpaceInfinity) hb
      simp only [Category.assoc] at h
      rw [← NatTrans.comp_app, ← pre_map, SSet.const_comp] at h
      exact h
  · rintro ⟨h₀, h₁⟩
    apply uncurry_injective
    apply joinEndpointTensor_hom_ext
    · rw [← uncurry_pre_app, ← uncurry_pre_app]
      congr 1
      simp only [Category.assoc]
      rw [← NatTrans.comp_app, ← pre_map]
      change F ≫ cylinderFixedEndpointSquarePointed f s t ≫
        (pre (cylinderSquareSourceInclusion f)).app _ = _
      rw [← cylinderFixedEndpointSquareSource_ι, ← Category.assoc, h₀,
        SSet.const_comp, SSet.const_comp]
      rfl
    · rw [← uncurry_pre_app, ← uncurry_pre_app]
      congr 1
      simp only [Category.assoc]
      rw [← NatTrans.comp_app, ← pre_map]
      change F ≫ cylinderFixedEndpointSquarePointed f s t ≫
        (pre (pushout.inr (prismEndpoint 1 K) f)).app _ = _
      rw [← cylinderFixedEndpointSquareTarget_ι, ← Category.assoc, h₁,
        SSet.const_comp, SSet.const_comp]
      rfl

/-- 概要：任意のパラメーターで同値な固定条件は頂点 fiber の厳密な同型を与える。
方針：二方向の fiber への持ち上げを作り、包含で互いに逆であることを確認する。
規約：射や頂点に充填性は要求しない。
使われ方：境界条件を両端条件へ置き換える。 -/
def vertexFiberIsoOfConstraintIff {X B C : SSet.{u}} (p : X ⟶ B) (q : X ⟶ C)
    (b : B _⦋0⦌) (c : C _⦋0⦌)
    (h : ∀ (L : SSet.{u}) (F : L ⟶ X), F ≫ p = SSet.const b ↔ F ≫ q = SSet.const c) :
    vertexFiber p b ≅ vertexFiber q c where
  hom := vertexFiberLift q c (vertexFiberι p b) ((h _ _).mp (vertexFiberι_comp p b))
  inv := vertexFiberLift p b (vertexFiberι q c) ((h _ _).mpr (vertexFiberι_comp q c))
  hom_inv_id := by
    apply vertexFiber_hom_ext p b
    rw [Category.assoc, vertexFiberLift_ι, vertexFiberLift_ι, Category.id_comp]
  inv_hom_id := by
    apply vertexFiber_hom_ext q c
    rw [Category.assoc, vertexFiberLift_ι, vertexFiberLift_ι, Category.id_comp]

/-- 概要：円柱の厳密な境界 fiber は同時端点制限の fiber と厳密に同型。
方針：任意の族の固定条件の同値を fiber 同型に移す。
規約：両端写像に同値性はまだ要求しない。
使われ方：既証明の両端制限の可縮性を境界固定の族へ移す。 -/
def cylinderBoundaryEndpointFiberIso {K J : SSet.{u + 1}} (f : K ⟶ J)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) :
    vertexFiber (cylinderFixedEndpointSquarePointed f s t ≫
      (pre (transportCylinderEndpointInclusion f)).app _)
        (functorVertex (intervalBoundaryPointedMap g₀ g₁)) ≅
      vertexFiber (lift (cylinderFixedEndpointSquareSource f s t)
        (cylinderFixedEndpointSquareTarget f s t)) (functorVertex g₀, functorVertex g₁) :=
  vertexFiberIsoOfConstraintIff _ _ _ _ (by
    intro L F
    rw [cylinderBoundaryCondition_iff_endpoints]
    constructor
    · rintro ⟨h₀, h₁⟩
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, lift_fst, SSet.const_comp]
        exact h₀
      · simp only [Category.assoc, lift_snd, SSet.const_comp]
        exact h₁
    · intro h
      constructor
      · have hx := congrArg (fun w ↦ w ≫ fst _ _) h
        simp only [Category.assoc, lift_fst, SSet.const_comp] at hx
        exact hx
      · have hx := congrArg (fun w ↦ w ≫ snd _ _) h
        simp only [Category.assoc, lift_snd, SSet.const_comp] at hx
        exact hx)

end SerrePositivity.InfinityCategories
