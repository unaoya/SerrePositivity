module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalTransportBoundaryFamily
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CylinderEquivalenceSquareIso

/-!
概要：固定した二つの端点写像と両端固定の区間族から相対 lift の実際のデータを作る。
方針：定値な境界の関手と区間写像空間上の分類図式を相対内部 Hom に束ねる。
規約：区間の内部の分類図式は全高次パラメーターとともに動く。
使われ方：円柱と区間の表現の境界 fiber を比較する実際の族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：両端図式とパラメーターの直積上の射は二つの端点で一意に決まる。
方針：各次数で直和の二つの場合へ分ける。
規約：高次のパラメーターは任意。
使われ方：固定した境界写像の族の可換性。 -/
lemma joinEndpointTensor_hom_ext {K J L X : SSet.{u}}
    {F G : joinEndpointDiagram K J ⊗ L ⟶ X}
    (h₀ : (joinEndpointInl K J ▷ L) ≫ F = (joinEndpointInl K J ▷ L) ≫ G)
    (h₁ : (joinEndpointInr K J ▷ L) ≫ F = (joinEndpointInr K J ▷ L) ≫ G) : F = G := by
  apply SSet.hom_ext
  intro n
  ext x
  rcases x with ⟨x, l⟩
  cases x with
  | inl k =>
    exact ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app h₀ n)
      (show (K ⊗ L).obj n from (k, l))
  | inr j =>
    exact ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app h₁ n)
      (show (J ⊗ L).obj n from (j, l))

/-- 概要：区間への射の端点部分で普遍的な分類区間の族を評価すると端点に定値。
方針：端点部分の区間への射と普遍区間の端点公式を使う。
規約：部分 j の係数は任意。
使われ方：境界固定の二つの可換条件。 -/
lemma intervalFamily_endpoint_restriction {M A : SSet.{u + 1}}
    (q : M ⟶ (Δ[1] : SSet.{u + 1})) (j : A ⟶ M)
    (s t b : SpaceInfinity.{u} _⦋0⦌) (i : Fin 2)
    (hj : j ≫ q = SSet.const (stdSimplex.obj₀Equiv.symm i))
    (hb : prismEndpoint i _ ≫ intervalMappingUncurry (𝟙 (intervalMappingSpace s t)) =
      SSet.const b) :
    (j ▷ intervalMappingSpace s t) ≫ uncurry (cylinderIntervalDiagramι s t ≫ (pre q).app _) =
      SSet.const b := by
  rw [uncurry_pre_app, ← Category.assoc, ← comp_whiskerRight, hj]
  change (snd A _ ≫ prismEndpoint i _) ≫
    intervalMappingUncurry (𝟙 (intervalMappingSpace s t)) = _
  rw [Category.assoc, hb, SSet.comp_const]

/-- 概要：指定した両端写像を pointed-space 値の境界の関手にまとめる。
方針：二つの fiber 写像を包含後に直和から貼る。
規約：両端写像に同値性は要求しない。
使われ方：定値な境界条件の関手。 -/
def intervalBoundaryPointedMap {K J : SSet.{u + 1}} {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) :
    joinEndpointDiagram K J ⟶ PointedSpaceInfinity.{u} :=
  joinEndpointDesc (g₀ ≫ vertexFiberι pointedSpaceProjection s)
    (g₁ ≫ vertexFiberι pointedSpaceProjection t)

/-- 概要：定値な境界の族は動く普遍区間の分類図式と厳密に可換。
方針：両端の直積の一意性で二つの端点公式に帰着する。
規約：境界包含 j は底の零端と一端を保つ。
使われ方：実際の相対内部 Hom のデータの定義。 -/
lemma intervalBoundaryFamily_compatibility {M K J : SSet.{u + 1}}
    (q : M ⟶ (Δ[1] : SSet.{u + 1})) (j : joinEndpointDiagram K J ⟶ M)
    (hj₀ : (joinEndpointInl K J ≫ j) ≫ q = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hj₁ : (joinEndpointInr K J ≫ j) ≫ q = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) :
    (SSet.const (functorVertex (intervalBoundaryPointedMap g₀ g₁)) :
        intervalMappingSpace s t ⟶ _) ≫
          (ihom (joinEndpointDiagram K J)).map pointedSpaceProjection =
      (cylinderIntervalDiagramι s t ≫ (pre q).app _) ≫ (pre j).app _ := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_const_functorVertex, uncurry_pre_app]
  apply joinEndpointTensor_hom_ext
  · calc
      _ = SSet.const s := by
        change ((joinEndpointInl K J ▷ _) ≫ fst _ _ ≫ intervalBoundaryPointedMap g₀ g₁) ≫
          pointedSpaceProjection = _
        rw [← Category.assoc, whiskerRight_fst, Category.assoc]
        change (fst K _ ≫ g₀ ≫ vertexFiberι pointedSpaceProjection s) ≫ pointedSpaceProjection = _
        rw [Category.assoc, Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
      _ = _ := by
        rw [← Category.assoc, ← comp_whiskerRight]
        exact (intervalFamily_endpoint_restriction q (joinEndpointInl K J ≫ j) s t s 0
          hj₀ (intervalMappingUncurry_zero _)).symm
  · calc
      _ = SSet.const t := by
        change ((joinEndpointInr K J ▷ _) ≫ fst _ _ ≫ intervalBoundaryPointedMap g₀ g₁) ≫
          pointedSpaceProjection = _
        rw [← Category.assoc, whiskerRight_fst, Category.assoc]
        change (fst J _ ≫ g₁ ≫ vertexFiberι pointedSpaceProjection t) ≫ pointedSpaceProjection = _
        rw [Category.assoc, Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
      _ = _ := by
        rw [← Category.assoc, ← comp_whiskerRight]
        exact (intervalFamily_endpoint_restriction q (joinEndpointInr K J ≫ j) s t t 1
          hj₁ (intervalMappingUncurry_one _)).symm

/-- 概要：実際の区間写像空間上で底を動かし両端写像を固定する相対データ。
方針：定値な境界と普遍区間による分類図式を相対内部 Hom へ束ねる。
規約：各区間の高次の lift を全て含むためのデータ。
使われ方：区間と円柱の境界固定 lift 空間の定義。 -/
def intervalBoundaryFamilyData {M K J : SSet.{u + 1}}
    (q : M ⟶ (Δ[1] : SSet.{u + 1})) (j : joinEndpointDiagram K J ⟶ M)
    (hj₀ : (joinEndpointInl K J ≫ j) ≫ q = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hj₁ : (joinEndpointInr K J ≫ j) ≫ q = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (r : internalHom.PullbackObjObj j pointedSpaceProjection)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) : intervalMappingSpace s t ⟶ r.pt :=
  relativeBoundaryFamilyData j pointedSpaceProjection r
    (SSet.const (functorVertex (intervalBoundaryPointedMap g₀ g₁)))
    (cylinderIntervalDiagramι s t ≫ (pre q).app _)
    (intervalBoundaryFamily_compatibility q j hj₀ hj₁ g₀ g₁)

end SerrePositivity.InfinityCategories
